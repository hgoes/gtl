{-| This module provides a data structure for type-checked GTL specifications.
 -}
module Language.GTL.Model where

import Language.GTL.Parser.Token (BinOp(GOpAnd))
import Language.GTL.Parser.Syntax
import Language.GTL.Backend.All
import Language.GTL.Expression
import Language.GTL.Types
import Data.Map as Map
import Data.Set as Set
import Prelude hiding (mapM)
import Data.Traversable (mapM)
import Misc.ProgramOptions

-- | A parsed and typechecked GTL model.
data GTLModel a = GTLModel
                  { gtlModelContract :: TypedExpr a -- ^ The contract of the model as a boolean formula.
                  , gtlModelBackend :: AllBackend -- ^ An abstract model in a synchronous specification language.
                  , gtlModelInput :: Map a GTLType -- ^ The input variables with types of the model.
                  , gtlModelOutput :: Map a GTLType -- ^ The output variables with types of the model.
                  , gtlModelLocals :: Map a GTLType -- ^ The local variables with types of the model.
                  , gtlModelDefaults :: Map a (Maybe GTLConstant) -- ^ Default values for inputs. `Nothing' means any value.
                  , gtlModelCycleTime :: Integer -- ^ Cycle time in us
                  }

-- | Represents the start or end of a connection, by specifying the instance
--   name, the variable name and a list of indices that refer to the right
--   component of the variable.
data GTLConnectionPoint a = GTLConnPt String a [Integer]

-- | A GTL specification represents a type checked GTL file.
data GTLSpec a = GTLSpec
               { gtlSpecModels :: Map String (GTLModel a) -- ^ All models in the specification.
               , gtlSpecInstances :: Map String (GTLInstance a)
               , gtlSpecVerify :: TypedExpr (String,a) -- ^ A formula to verify.
               , gtlSpecConnections :: [(GTLConnectionPoint a,GTLConnectionPoint a)] -- ^ Connections between models.
               }

-- | A GTL instance is a concrete manifestation of a model.
data GTLInstance a = GTLInstance
                     { gtlInstanceModel :: String -- ^ The model of which this is an instance
                     , gtlInstanceContract :: Maybe (TypedExpr a) -- ^ Additional contract
                     , gtlInstanceDefaults :: Map a (Maybe GTLConstant) -- ^ Additional default values
                     }

-- | Get the type of a variable which resides in an instance.
getInstanceVariableType :: (Ord a,Show a) => GTLSpec a -> Bool -> String -> a -> GTLType
getInstanceVariableType spec inp inst var = case Map.lookup inst (gtlSpecInstances spec) of
  Nothing -> error $ "Internal error: Instance "++show inst++" not found."
  Just rinst -> case Map.lookup (gtlInstanceModel rinst) (gtlSpecModels spec) of
    Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel rinst)++" not found"
    Just mdl -> case Map.lookup var (if inp then gtlModelInput mdl else gtlModelOutput mdl) of
      Nothing -> error $ "Internal error: Variable "++show var++" not found."
      Just tp -> tp

-- | Parse a GTL model from a unchecked model declaration.
gtlParseModel :: Options -> Map String UnResolvedType -> ModelDecl -> IO (Either String (String,GTLModel String,Set [String]))
gtlParseModel opts aliases mdl = do
  let rtps = do
        rinps <- mapM (resolveType aliases) (modelInputs mdl)
        routps <- mapM (resolveType aliases) (modelOutputs mdl)
        rlocs <- mapM (resolveType aliases) (modelLocals mdl)
        return (rinps,routps,rlocs)
  case rtps of
    Left err -> return $ Left err
    Right (inps,outps,locs) -> do
      mback <- initAllBackend (modelType mdl) opts (modelArgs mdl)
      case mback of
        Nothing -> return $ Left $ "Couldn't initialize backend "++(modelType mdl)
        Just back -> return $ do
          (inp,outp) <- allTypecheck back (inps,outps)
          let allType = Map.unions [inp,outp,locs]
              enums = getEnums allType
          expr <- makeTypedExpr
                  (\q n inf -> case q of
                      Nothing -> Right (n,if Map.member n inp
                                          then Input
                                          else (if Map.member n outp
                                                then Output
                                                else (case inf of
                                                         Nothing -> StateIn
                                                         Just ContextIn -> StateIn
                                                         Just ContextOut -> StateOut
                                                     )
                                               ))
                      _ -> Left "Contract may not contain qualified variables")
                  allType enums (case modelContract mdl of
                                    [] -> GConstBool True
                                    c -> foldl1 (GBin GOpAnd NoTime) c)
          lst <- mapM (\(var,init) -> case init of
                          InitAll -> return (var,Nothing)
                          InitOne c -> do
                            ce <- makeTypedExpr (\q n _ -> Left "Init expression may not contain variables"::Either String (String,VarUsage)) allType enums c
                            case Map.lookup var allType of
                              Nothing -> Left $ "Unknown variable: "++show var++" in model "++modelName mdl
                              Just tp -> if getType (unfix ce) `isSubtypeOf` tp
                                         then (case getConstant ce of
                                                  Just p -> return $ (var,Just p)
                                                  Nothing -> Left $ "Init expression must be a constant"
                                              )
                                         else Left $ show var ++ " has type "++show tp++", but is initialized with "++show (getType $ unfix ce)) (modelInits mdl)
          return (modelName mdl,GTLModel { gtlModelContract = expr
                                         , gtlModelBackend = back
                                         , gtlModelInput = inp
                                         , gtlModelOutput = outp
                                         , gtlModelLocals = locs
                                         , gtlModelDefaults = Map.fromList lst
                                         , gtlModelCycleTime = modelCycleTime mdl
                                         },enums)

-- | Get all possible enum types.
getEnums :: Map a GTLType -> Set [String]
getEnums mp = Set.unions $ fmap getEnums' (Map.elems mp)
  where
    getEnums' :: GTLType -> Set [String]
    getEnums' (Fix (GTLEnum xs)) = Set.singleton xs
    getEnums' (Fix (GTLArray sz tp)) = getEnums' tp
    getEnums' (Fix (GTLTuple xs)) = Set.unions (fmap getEnums' xs)
    getEnums' (Fix (GTLNamed name tp)) = getEnums' tp
    getEnums' _ = Set.empty

-- | Parse a GTL specification from an unchecked list of declarations.
gtlParseSpec :: Options -> [Declaration] -> IO (Either String (GTLSpec String))
gtlParseSpec opts decls = do
  let aliases = foldl (\mp decl -> case decl of
                          TypeAlias name tp -> Map.insert name tp mp
                          _ -> mp) Map.empty decls
  mdls <- fmap sequence $ sequence [ gtlParseModel opts aliases m
                                   | Model m <- decls
                                   ]
  return $ do
    rmdls <- mdls
    let mdl_mp = Map.fromList [ (name,mdl) | (name,mdl,_) <- rmdls ]
        enums = Set.unions [ enum | (_,_,enum) <- rmdls ]
    insts <- sequence 
             [ do 
                  mdl <- case Map.lookup (instanceModel i) mdl_mp of
                    Nothing -> Left $ "Model "++(instanceModel i)++" not found."
                    Just m -> return m
                  contr <- case instanceContract i of
                    [] -> return Nothing
                    _ -> makeTypedExpr (\q n inf -> case q of
                             Nothing -> Right (n,if Map.member n (gtlModelInput mdl)
                                                 then Input
                                                 else (if Map.member n (gtlModelOutput mdl)
                                                       then Output
                                                       else (case inf of
                                                                Nothing -> StateIn
                                                                Just ContextIn -> StateIn
                                                                Just ContextOut -> StateOut
                                                            )))
                             _ -> Left "Contract may not contain qualified variables") (Map.union (gtlModelInput mdl) (gtlModelOutput mdl)) enums
                         (foldl1 (GBin GOpAnd NoTime) (instanceContract i)) >>= return.Just
                  return (instanceName i,GTLInstance { gtlInstanceModel = instanceModel i
                                                     , gtlInstanceContract = contr
                                                     , gtlInstanceDefaults = Map.empty
                                                     })
             | Instance i <- decls ]
    let inst_mp = Map.fromList insts
        alltp = Map.fromList [ ((q,n),tp)
                             | (q,inst) <- insts
                             , let mdl = mdl_mp!(gtlInstanceModel inst)
                             , (n,tp) <- Map.toList $ Map.union (gtlModelInput mdl) (gtlModelOutput mdl)
                             ]
    vexpr <- makeTypedExpr (\q n inf -> case q of
                                 Nothing -> Left "No unqualified variables allowed in verify clause"
                                 Just rq -> Right ((rq,n),Input)
                             ) alltp enums (case concat [ v | Verify (VerifyDecl v) <- decls ] of
                                             [] -> GConstBool True
                                             x -> foldl1 (GBin GOpAnd NoTime) x)
    conns <- sequence [ do
                           finst <- case Map.lookup f inst_mp of
                             Nothing -> Left $ "Instance "++f++" not found."
                             Just x -> return x
                           let fmdl = mdl_mp!(gtlInstanceModel finst)
                           tinst <- case Map.lookup t inst_mp of
                             Nothing -> Left $ "Instance "++t++" not found."
                             Just x -> return x
                           let tmdl = mdl_mp!(gtlInstanceModel tinst)
                           fvar <- case Map.lookup fv (gtlModelOutput fmdl) of
                             Nothing -> Left $ "Variable "++f++"."++fv++" not found or not an output variable."
                             Just x -> return x
                           tvar <- case Map.lookup tv (gtlModelInput tmdl) of
                             Nothing -> Left $ "Variable "++t++"."++tv++" not found or not an input variable."
                             Just x -> return x
                           ftp <- resolveIndices fvar fi
                           ttp <- resolveIndices tvar ti
                           if ftp `isSubtypeOf` ttp then return (GTLConnPt f fv fi,GTLConnPt t tv ti)
                             else Left $ "Type mismatch between "++f++"."++fv++show fi++"("++show ftp++") and "++t++"."++tv++show ti++"("++show ttp++")."
              |  Connect (ConnectDecl f fv fi t tv ti) <- decls ]
    return $ GTLSpec { gtlSpecModels = mdl_mp
                     , gtlSpecInstances = inst_mp
                     , gtlSpecVerify = vexpr
                     , gtlSpecConnections = conns
                     }

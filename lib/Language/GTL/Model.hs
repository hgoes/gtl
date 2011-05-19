{-| This module provides a data structure for type-checked GTL specifications.
 -}
module Language.GTL.Model where

import Language.GTL.Parser.Token (BinOp(GOpAnd))
import Language.GTL.Parser.Syntax
import Language.GTL.Backend.All
import Language.GTL.Expression
import Language.GTL.Types
import Data.Typeable
import Data.Dynamic
import Data.Map as Map
import Data.Set as Set
import Data.List (genericIndex,genericLength)
import Data.Binary
import Prelude hiding (mapM)
import Data.Traversable (mapM)

-- | A parsed and typechecked GTL model.
data GTLModel a = GTLModel
                  { gtlModelContract :: TypedExpr a -- ^ The contract of the model as a boolean formula.
                  , gtlModelBackend :: AllBackend -- ^ An abstract model in a synchronous specification language.
                  , gtlModelInput :: Map a GTLType -- ^ The input variables with types of the model.
                  , gtlModelOutput :: Map a GTLType -- ^ The output variables with types of the model.
                  , gtlModelDefaults :: Map a (Maybe GTLConstant) -- ^ Default values for inputs. `Nothing' means any value.
                  }

data GTLConnectionPoint a = GTLConnPt String a [Integer]

-- | A GTL specification represents a type checked GTL file.
data GTLSpec a = GTLSpec
               { gtlSpecModels :: Map String (GTLModel a) -- ^ All models in the specification.
               , gtlSpecInstances :: Map String (GTLInstance a)
               , gtlSpecVerify :: TypedExpr (String,a) -- ^ A formula to verify.
               , gtlSpecConnections :: [(GTLConnectionPoint a,GTLConnectionPoint a)] -- ^ Connections between models.
               }

data GTLInstance a = GTLInstance
                     { gtlInstanceModel :: String
                     , gtlInstanceContract :: Maybe (TypedExpr a)
                     , gtlInstanceDefaults :: Map a (Maybe GTLConstant)
                     }

-- | Parse a GTL model from a unchecked model declaration.
gtlParseModel :: ModelDecl -> IO (Either String (String,GTLModel String,Set [String]))
gtlParseModel mdl = do
  mback <- initAllBackend (modelType mdl) (modelArgs mdl)
  case mback of
    Nothing -> return $ Left $ "Couldn't initialize backend "++(modelType mdl)
    Just back -> return $ do
      {-oinp <- mapM (\str -> case parseGTLType str of
                       Nothing -> Left $ "Unknown type "++show str
                       Just rtp -> return rtp) (modelInputs mdl)
      oout <- mapM (\str -> case parseGTLType str of
                       Nothing -> Left $ "Unknown type "++show str
                       Just rtp -> return rtp) (modelOutputs mdl)-}
      (inp,outp) <- allTypecheck back (modelInputs mdl,modelOutputs mdl)
      let allType = Map.union inp outp
          enums = getEnums allType
      expr <- makeTypedExpr
              (\q n -> case q of
                  Nothing -> Right n
                  _ -> Left "Contract may not contain qualified variables") 
              allType enums (case modelContract mdl of
                                [] -> GConstBool True
                                c -> foldl1 (GBin GOpAnd) c)
      lst <- mapM (\(var,init) -> case init of
                      InitAll -> return (var,Nothing)
                      InitOne c -> do
                        ce <- makeTypedExpr (\q n -> Left "Init expression may not contain variables"::Either String String) allType enums c
                        case Map.lookup var allType of
                          Nothing -> Left $ "Unknown variable: "++show var
                          Just tp -> if tp == getType ce
                                     then (case getConstant ce of
                                              Just p -> return $ (var,Just p)
                                              Nothing -> Left $ "Init expression must be a constant"
                                          )
                                     else Left $ show var ++ " has type "++show tp++", but is initialized with "++show (getType ce)) (modelInits mdl)
      return (modelName mdl,GTLModel { gtlModelContract = expr
                                     , gtlModelBackend = back
                                     , gtlModelInput = inp
                                     , gtlModelOutput = outp
                                     , gtlModelDefaults = Map.fromList lst
                                     },enums)

getEnums :: Map a GTLType -> Set [String]
getEnums mp = Set.unions $ fmap getEnums' (Map.elems mp)
  where
    getEnums' :: GTLType -> Set [String]
    getEnums' (GTLEnum xs) = Set.singleton xs
    getEnums' (GTLArray sz tp) = getEnums' tp
    getEnums' (GTLTuple xs) = Set.unions (fmap getEnums' xs)
    getEnums' _ = Set.empty

resolveIndices :: GTLType -> [Integer] -> Either String GTLType
resolveIndices tp [] = return tp
resolveIndices (GTLArray sz tp) (x:xs) = if x < sz
                                         then resolveIndices tp xs
                                         else Left $ "Index "++show x++" is out of array bounds ("++show sz++")"
resolveIndices (GTLTuple tps) (x:xs) = if x < (genericLength tps)
                                       then resolveIndices (tps `genericIndex` x) xs
                                       else Left $ "Index "++show x++" is out of array bounds ("++show (genericLength tps)++")"
resolveIndices tp _ = Left $ "Type "++show tp++" isn't indexable"

-- | Parse a GTL specification from an unchecked list of declarations.
gtlParseSpec :: [Declaration] -> IO (Either String (GTLSpec String))
gtlParseSpec decls = do
  mdls <- fmap sequence $ sequence [ gtlParseModel m
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
                    _ -> makeTypedExpr (\q n -> case q of
                             Nothing -> Right n
                             _ -> Left "Contract may not contain qualified variables") (Map.union (gtlModelInput mdl) (gtlModelOutput mdl)) enums
                         (foldl1 (GBin GOpAnd) (instanceContract i)) >>= return.Just
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
    vexpr <- makeTypedExpr (\q n -> case q of
                                 Nothing -> Left "No unqualified variables allowed in verify clause"
                                 Just rq -> Right (rq,n)
                             ) alltp enums (case concat [ v | Verify (VerifyDecl v) <- decls ] of
                                             [] -> GConstBool True
                                             x -> foldl1 (GBin GOpAnd) x)
    sequence_ [ do
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
                   if ftp==ttp then return ()
                     else Left $ "Type mismatch between "++f++"."++fv++show fi++" and "++t++"."++tv++show ti++"."
              |  Connect (ConnectDecl f fv fi t tv ti) <- decls ]
    return $ GTLSpec { gtlSpecModels = mdl_mp
                     , gtlSpecInstances = inst_mp
                     , gtlSpecVerify = vexpr
                     , gtlSpecConnections = [ (GTLConnPt f fv fi,GTLConnPt t tv ti)
                                            | Connect (ConnectDecl f fv fi t tv ti) <- decls ]
                     }

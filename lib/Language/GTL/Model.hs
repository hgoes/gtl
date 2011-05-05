{-| This module provides a data structure for type-checked GTL specifications.
 -}
module Language.GTL.Model where

import Language.GTL.Parser.Token (BinOp(GOpAnd))
import Language.GTL.Parser.Syntax
import Language.GTL.Backend.All
import Language.GTL.Expression
import Data.Typeable
import Data.Dynamic
import Data.Map as Map
import Data.Binary
import Prelude hiding (mapM)
import Data.Traversable (mapM)

-- | A parsed and typechecked GTL model.
data GTLModel a = GTLModel
                  { gtlModelContract :: Expr a Bool -- ^ The contract of the model as a boolean formula.
                  , gtlModelBackend :: AllBackend -- ^ An abstract model in a synchronous specification language.
                  , gtlModelInput :: Map a TypeRep -- ^ The input variables with types of the model.
                  , gtlModelOutput :: Map a TypeRep -- ^ The output variables with types of the model.
                  , gtlModelDefaults :: Map a (Maybe Dynamic) -- ^ Default values for inputs. `Nothing' means any value.
                  }

-- | A GTL specification represents a type checked GTL file.
data GTLSpec a = GTLSpec
               { gtlSpecModels :: Map String (GTLModel a) -- ^ All models in the specification.
               , gtlSpecInstances :: Map String (GTLInstance a)
               , gtlSpecVerify :: Expr (String,a) Bool -- ^ A formula to verify.
               , gtlSpecConnections :: [(String,a,String,a)] -- ^ Connections between models.
               }

data GTLInstance a = GTLInstance
                     { gtlInstanceModel :: String
                     , gtlInstanceContract :: Maybe (Expr a Bool)
                     , gtlInstanceDefaults :: Map a (Maybe Dynamic)
                     }

-- | Parse a GTL model from a unchecked model declaration.
gtlParseModel :: ModelDecl -> IO (Either String (String,GTLModel String))
gtlParseModel mdl = do
  mback <- initAllBackend (modelType mdl) (modelArgs mdl)
  case mback of
    Nothing -> return $ Left $ "Couldn't initialize backend "++(modelType mdl)
    Just back -> return $ do
      oinp <- mapM (\str -> case parseGTLType str of
                       Nothing -> Left $ "Unknown type "++show str
                       Just rtp -> return rtp) (modelInputs mdl)
      oout <- mapM (\str -> case parseGTLType str of
                       Nothing -> Left $ "Unknown type "++show str
                       Just rtp -> return rtp) (modelOutputs mdl)
      (inp,outp) <- allTypecheck back (oinp,oout)
      let allType = Map.union inp outp
      expr <- typeCheck allType
              (\q n -> case q of
                  Nothing -> Right n
                  _ -> Left "Contract may not contain qualified variables") Map.empty (case modelContract mdl of
                                                                                          [] -> GConstBool True
                                                                                          c -> foldl1 (GBin GOpAnd) c)
      lst <- mapM (\(var,init) -> case init of
                      InitAll -> return (var,Nothing)
                      InitOne c -> case Map.lookup var allType of
                        Nothing -> Left $ "Unknown variable: "++show var
                        Just tp -> if tp == typeOf (undefined::Int)
                                   then return (var,Just $ toDyn (fromIntegral c::Int))
                                   else Left $ show var ++ " has type "++show tp++", but is initialized with Int") (modelInits mdl)
      return (modelName mdl,GTLModel { gtlModelContract = expr
                                     , gtlModelBackend = back
                                     , gtlModelInput = inp
                                     , gtlModelOutput = outp
                                     , gtlModelDefaults = Map.fromList lst
                                     })

-- | Parse a GTL specification from an unchecked list of declarations.
gtlParseSpec :: [Declaration] -> IO (Either String (GTLSpec String))
gtlParseSpec decls = do
  mdls <- fmap sequence $ sequence [ gtlParseModel m
                                   | Model m <- decls
                                   ]
  return $ do
    rmdls <- mdls
    let alltp = Map.fromList [ ((q,n),tp)
                             | (q,mdl) <- rmdls
                             , (n,tp) <- Map.toList $ Map.union (gtlModelInput mdl) (gtlModelOutput mdl)
                             ]

    vexpr <- typeCheck alltp (\q n -> case q of
                                 Nothing -> Left "No unqualified variables allowed in verify clause"
                                 Just rq -> Right (rq,n)
                             ) Map.empty (case concat [ v | Verify (VerifyDecl v) <- decls ] of
                                             [] -> GConstBool True
                                             x -> foldl1 (GBin GOpAnd) x)
    let mdl_mp = Map.fromList rmdls
    insts <- sequence 
             [ do 
                  mdl <- case Map.lookup (instanceModel i) mdl_mp of
                    Nothing -> Left $ "Model "++(instanceModel i)++" not found."
                    Just m -> return m
                  contr <- case instanceContract i of
                    [] -> return Nothing
                    _ -> typeCheck (Map.union (gtlModelInput mdl) (gtlModelOutput mdl))
                         (\q n -> case q of
                             Nothing -> Right n
                             _ -> Left "Contract may not contain qualified variables") Map.empty
                         (foldl1 (GBin GOpAnd) (instanceContract i)) >>= return.Just
                  return (instanceName i,GTLInstance { gtlInstanceModel = instanceModel i
                                                     , gtlInstanceContract = contr
                                                     , gtlInstanceDefaults = Map.empty
                                                     })
             | Instance i <- decls ]
    let inst_mp = Map.fromList insts
    sequence_ [ do
                   fmdl <- case Map.lookup f mdl_mp of
                     Nothing -> Left $ "Model "++f++" not found."
                     Just x -> return x
                   tmdl <- case Map.lookup t mdl_mp of
                     Nothing -> Left $ "Model "++t++" not found."
                     Just x -> return x
                   fvar <- case Map.lookup fv (gtlModelOutput fmdl) of
                     Nothing -> Left $ "Variable "++f++"."++fv++" not found or not an output variable."
                     Just x -> return x
                   tvar <- case Map.lookup tv (gtlModelInput tmdl) of
                     Nothing -> Left $ "Variable "++t++"."++tv++" not found or not an input variable."
                     Just x -> return x
                   if fvar==tvar then return ()
                     else Left $ "Type mismatch between "++f++"."++fv++" and "++t++"."++tv++"."
              |  Connect (ConnectDecl f fv t tv) <- decls ]
    return $ GTLSpec { gtlSpecModels = mdl_mp
                     , gtlSpecInstances = inst_mp
                     , gtlSpecVerify = vexpr
                     , gtlSpecConnections = [ (f,fv,t,tv)
                                            | Connect (ConnectDecl f fv t tv) <- decls ]
                     }
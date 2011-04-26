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
data GTLModel = GTLModel
                { gtlModelContract :: Expr String Bool -- ^ The contract of the model as a boolean formula.
                , gtlModelBackend :: AllBackend -- ^ An abstract model in a synchronous specification language.
                , gtlModelInput :: Map String TypeRep -- ^ The input variables with types of the model.
                , gtlModelOutput :: Map String TypeRep -- ^ The output variables with types of the model.
                , gtlModelDefaults :: Map String (Maybe Dynamic) -- ^ Default values for inputs. `Nothing' means any value.
                }

-- | A GTL specification represents a type checked GTL file.
data GTLSpec = GTLSpec
               { gtlSpecModels :: Map String GTLModel -- ^ All models in the specification.
               , gtlSpecVerify :: Expr (String,String) Bool -- ^ A formula to verify.
               , gtlSpecConnections :: [(String,String,String,String)] -- ^ Connections between models.
               }

-- | Parse a GTL model from a unchecked model declaration.
gtlParseModel :: ModelDecl -> IO (Either String (String,GTLModel))
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
gtlParseSpec :: [Declaration] -> IO (Either String GTLSpec)
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
    return $ GTLSpec { gtlSpecModels = Map.fromList rmdls
                     , gtlSpecVerify = vexpr
                     , gtlSpecConnections = [ (f,fv,t,tv)
                                            | Connect (ConnectDecl f fv t tv) <- decls ]
                     }
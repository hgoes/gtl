module Language.GTL.Model where

import Language.GTL.Token (BinOp(GOpAnd))
import Language.GTL.Syntax
import Language.GTL.Backend.All
import Data.Typeable
import Control.Monad
import Data.Map as Map

data GTLModel = GTLModel
                { gtlModelContract :: Expr String Bool
                , gtlModelBackend :: AllBackend
                , gtlModelInput :: Map String TypeRep
                , gtlModelOutput :: Map String TypeRep
                }

data GTLSpec = GTLSpec
               { gtlSpecModels :: Map String GTLModel
               , gtlSpecVerify :: Expr (String,String) Bool
               , gtlSpecConnections :: [(String,String,String,String)]
               }

gtlParseModel :: ModelDecl -> IO (Either String (String,GTLModel))
gtlParseModel mdl = do
  mback <- initAllBackend (modelType mdl) (modelArgs mdl)
  case mback of
    Nothing -> return $ Left $ "Couldn't initialize backend "++(modelType mdl)
    Just back -> return $ do
      (inp,outp) <- allTypecheck back (modelInputs mdl) (modelOutputs mdl)
      expr <- typeCheck (Map.union inp outp)
              (\q n -> case q of
                  Nothing -> Right n
                  _ -> Left "Contract may not contain qualified variables") (case modelContract mdl of
                                                                                [] -> GConstBool True
                                                                                c -> foldl1 (GBin GOpAnd) c)
      return (modelName mdl,GTLModel { gtlModelContract = expr
                                     , gtlModelBackend = back
                                     , gtlModelInput = inp
                                     , gtlModelOutput = outp
                                     })

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
                                 Just rq -> Right (rq,n)) (case concat [ v | Verify (VerifyDecl v) <- decls ] of
                                                              [] -> GConstBool True
                                                              x -> foldl1 (GBin GOpAnd) x)
    return $ GTLSpec { gtlSpecModels = Map.fromList rmdls
                     , gtlSpecVerify = vexpr
                     , gtlSpecConnections = [ (f,fv,t,tv)
                                            | Connect (ConnectDecl f fv t tv) <- decls ]
                     }
  
  
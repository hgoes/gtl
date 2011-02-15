module Language.GTL.PromelaCIntegration where

import Language.GTL.Parser (gtl)
import Language.GTL.Lexer (alexScanTokens)
import Language.GTL.Syntax
import Language.GTL.ScadeAnalyzer
import Language.GTL.ErrorRefiner

import qualified Language.Promela.Syntax as Pr
import qualified Language.Scade.Syntax as Sc
import Language.Promela.Pretty

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.BDD

translateGTL :: Maybe FilePath -> [Declaration] -> [Sc.Declaration] -> IO String
translateGTL traces gtlcode scadecode
  = do
    let tps = typeMap gtlcode scadecode
        conns = connectionMap gtlcode tps
    nevers <- case traces of
      Nothing -> return []
      Just tr -> runBDDM (do
                             rtr <- readBDDTraces tr
                             return [generateNeverClaim $ head rtr]
                         )
    return $ show $ prettyPromela $ (generatePromelaCode tps conns)++nevers

generateNeverClaim :: BDDTrace s -> Pr.Module
generateNeverClaim trace = Pr.Never (traceToPromela (\mdl var -> "now."++mdl++"_state."++var) trace)

generatePromelaCode :: TypeMap -> [((String,String),(String,String))] -> [Pr.Module]
generatePromelaCode tp conns
  = let procs = fmap (\(name,(int_name,inp,outp)) ->
                       let assignments = [Pr.StepStmt (Pr.StmtDo [[Pr.StepStmt (Pr.StmtCCode $ unlines $
                                                                                [name++"_input."++tvar++" = now."++
                                                                                 fmod++"_state."++fvar++";" 
                                                                                | ((fmod,fvar),(tmod,tvar)) <- conns, tmod==name ]++
                                                                                [int_name++"("++
                                                                                 (if Map.null inp
                                                                                  then ""
                                                                                  else "&"++name++"_input,")++
                                                                                 "&now."++name++"_state);"
                                                                                ]
                                                                               ) Nothing]
                                                                 ]) Nothing]
                       in Pr.ProcType { Pr.proctypeActive = Nothing
                                      , Pr.proctypeName = name
                                      , Pr.proctypeArguments = []
                                      , Pr.proctypePriority = Nothing
                                      , Pr.proctypeProvided = Nothing
                                      , Pr.proctypeSteps = assignments
                                      }) $ Map.toList tp
        states = fmap (\(name,(int_name,inp,outp)) -> Pr.CState ("outC_"++int_name++" "++name++"_state") "Global" Nothing) $ Map.toList tp
        inp_decls = [Pr.CDecl (unlines $
                               (fmap (\(int_name,_,_) -> "\\#include <"++int_name++".h>") (Map.elems tp)) ++
                               (fmap (\(name,(int_name,inp,outp)) -> if Map.null inp
                                                                     then "//No input structure for "++name
                                                                     else "inC_"++int_name++" "++name++"_input;"
                                     ) (Map.toList tp))
                              )]
        init = [Pr.Init Nothing ([Pr.StepStmt (Pr.StmtCCode $ unlines $
                                               fmap (\(name,(int_name,inp,outp)) -> 
                                                      int_name++"_reset(&now."++name++"_state);") (Map.toList tp)
                                              ) Nothing,
                                  Pr.StepStmt (Pr.StmtAtomic 
                                               [Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.RunExpr name [] Nothing) Nothing
                                               | name <- Map.keys tp
                                               ]) Nothing
                                 ])
               ]
    in inp_decls ++ states ++ procs ++ init

connectionMap :: [Declaration] -> TypeMap -> [((String,String),(String,String))]
connectionMap def tp = mapMaybe (\decl -> case decl of
                                    Model _ -> Nothing
                                    Verify _ -> Nothing
                                    Connect conn -> let fromTp = getConnectionPoint conn False
                                                        toTp = getConnectionPoint conn True
                                                    in if fromTp == toTp
                                                       then Just ((connectFromModel conn,connectFromVariable conn),
                                                                  (connectToModel conn,connectToVariable conn))
                                                       else error $ "Type mismatch for connection "++show conn) def
                                                            
  where
    getConnectionPoint conn kind = let smodel = if kind
                                                then connectToModel conn
                                                else connectFromModel conn
                                       svar = if kind
                                              then connectToVariable conn
                                              else connectFromVariable conn
                                   in case Map.lookup smodel tp of
                                     Nothing -> error $ "Model "++show smodel++" not declared"
                                     Just (_,inp,outp) -> if kind
                                                          then case Map.lookup svar inp of
                                                            Nothing -> error $ show svar ++ " is not a input variable of model "++show smodel
                                                            Just rtp -> rtp
                                                          else case Map.lookup svar outp of
                                                            Nothing -> error $ show svar ++ " is not a output variable of model "++show smodel
                                                            Just rtp -> rtp
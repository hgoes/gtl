{-# LANGUAGE GADTs #-}
module Language.GTL.PromelaCIntegration where

import Language.GTL.Parser (gtl)
import Language.GTL.Lexer (alexScanTokens)
import Language.GTL.Syntax as GTL
import Language.GTL.ScadeAnalyzer
import Language.GTL.ErrorRefiner
import Language.GTL.Translation
import Language.GTL.LTL

import qualified Language.Promela.Syntax as Pr
import qualified Language.Scade.Syntax as Sc
import Language.Promela.Pretty

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import Data.BDD
import Data.Bits

translateGTL :: Maybe FilePath -> [Declaration] -> [Sc.Declaration] -> IO String
translateGTL traces gtlcode scadecode
  = runBDDM $ do
    rtr <- case traces of
      Nothing -> return []
      Just tr -> do
        rtr <- readBDDTraces tr
        return rtr
    let tps = typeMap gtlcode scadecode
        conns = connectionMap gtlcode tps
        claims = case concat [ verifyFormulas decl | Verify decl <- gtlcode ] of
          [] -> []
          cl -> [neverClaim (case rtr of
                                [] -> []
                                x:_ -> x) $ ExprNot $ foldl1 (ExprBinBool GTL.And) cl]
    {-nevers <- case traces of
      Nothing -> return []
      Just tr -> runBDDM (do
                             rtr <- readBDDTraces tr
                             return [generateNeverClaim $ head rtr]
                         )-}
    return $ show $ prettyPromela $ (generatePromelaCode tps conns)++claims

neverClaim :: BDDTrace s -> Formula -> Pr.Module
neverClaim trace f
  = let traceAut = traceToBuchi trace
        states = Map.toList $ translateGBA $ buchiProduct (ltlToBuchi $ gtlToLTL f) traceAut
        showSt ((i,j),k) = show i++ "_"++show j++"_"++show k
        init = Pr.prIf [ [Pr.StmtGoto $ "st"++showSt i]  | (i,st) <- states, isStart st ]
        steps = [ Pr.StmtLabel ("st"++showSt i)
                  (let cexprr = case snd (vars st) of
                         Nothing -> []
                         Just (mdl,vs) -> [ generateBDDCheck ("now."++mdl++"_state."++v) (bitSize (undefined::Int)) tree
                                          | ((v,lvl),tree) <- Map.toList vs]
                       inner = case cexprl ++ cexprr of
                         [] -> jump
                         cexprs -> Pr.prSequence
                                   [Pr.StmtCExpr Nothing (foldl1 (\x y -> x++"&&"++y) cexprs)
                                   ,jump]
                       jump = Pr.prIf
                              [ [Pr.StmtGoto $ "st"++showSt j]
                              | j <- Set.toList (successors st)]
                              
                       cexprl = [ "("++(case ratom of
                                           GTLRel rel lhs rhs -> clit lhs ++ (case rel of
                                                                                 BinLT -> "<"
                                                                                 BinLTEq -> "<="
                                                                                 BinGT -> ">"
                                                                                 BinGTEq -> ">="
                                                                                 BinEq -> "=="
                                                                                 BinNEq -> "!=") ++ clit rhs
                                           _ -> error "Not yet implemented AUINV")++")"
                                | (atom,en) <- Map.toList $ fst $ vars st,
                                  let ratom = if en then atom else gtlAtomNot atom ]
                       clit :: Show a => Expr a -> String
                       clit (ExprConst x) = show x
                       clit (ExprVar (Just mdl) var lvl) = "now."++mdl++"_state."++var
                       clit (ExprBinInt op lhs rhs) = "("++clit lhs++(case op of
                                                                         OpPlus -> "+"
                                                                         OpMinus -> "-"
                                                                         OpMult -> "*"
                                                                         OpDiv -> "/")++clit rhs++")"
                       clit e = error $ "All variables in never claim must be qualified ["++show e++"]"
                   in if finalSets st
                      then Pr.StmtLabel ("accept"++showSt i) inner
                      else inner)
                | (i,st) <- states ]
    in Pr.prNever $ [init]++steps

generateNeverClaim :: BDDTrace s -> Pr.Module
generateNeverClaim trace = Pr.Never (traceToPromela (\mdl (var,lvl) -> "now."++mdl++"_state."++var) trace)

generatePromelaCode :: TypeMap -> [((String,String),(String,String))] -> [Pr.Module]
generatePromelaCode tp conns
  = let procs = fmap (\(name,(int_name,inp,outp)) ->
                       let assignments = [Pr.StepStmt (Pr.prDo [[Pr.StmtCCode $ unlines $
                                                                 [name++"_input."++tvar++" = now."++
                                                                  fmod++"_state."++fvar++";" 
                                                                 | ((fmod,fvar),(tmod,tvar)) <- conns, tmod==name ]++
                                                                 [int_name++"("++
                                                                  (if Map.null inp
                                                                   then ""
                                                                   else "&"++name++"_input,")++
                                                                  "&now."++name++"_state);"
                                                                 ]
                                                                ]
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
        init = [Pr.prInit ([Pr.StmtCCode $ unlines $
                            fmap (\(name,(int_name,inp,outp)) -> 
                                   int_name++"_reset(&now."++name++"_state);") (Map.toList tp),
                            Pr.prAtomic 
                            [Pr.StmtExpr $ Pr.ExprAny $ Pr.RunExpr name [] Nothing
                            | name <- Map.keys tp
                            ]
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
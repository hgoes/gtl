module Language.GTL.Target.Printer where

import Language.GTL.Model
import Language.GTL.Buchi
import Language.GTL.LTL
import Language.GTL.Expression
import Language.GTL.Translation

import Data.Map as Map
import Data.Set as Set

simplePrettyPrint :: GTLSpec String -> String
simplePrettyPrint spec
  = unlines $ concat [
     [name ++ "{"]++
     ["  input "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelInput mdl) ]++
     ["  output "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelOutput mdl) ]++
     (fmap ("  "++) (simplePrettyPrintBuchi (ltlToBuchi distributeNot (gtlToLTL (gtlModelContract mdl)))))++
     ["}"]
  | (name,mdl) <- Map.toList $ gtlSpecModels spec ]

simplePrettyPrintBuchi :: GBuchi Integer (Set (TypedExpr String,Bool)) (Set Integer) -> [String]
simplePrettyPrintBuchi buchi = concat
                               [ [(if isStart co then "initial " else "")++"state "++show st++" {"]++
                                 [ "  "++(if p then "" else "not ") ++ show at | (at,p) <- Set.toList (vars co) ]++
                                 [ "  -> "++show succ | succ <- Set.toList (successors co) ]++
                                 [ "  final "++show f | f <- Set.toList (finalSets co) ] ++
                                 ["}"]
                               | (st,co) <- Map.toList buchi ]

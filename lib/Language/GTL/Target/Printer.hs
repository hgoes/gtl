module Language.GTL.Target.Printer where

import Language.GTL.Model
import Language.GTL.Buchi
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
     (fmap ("  "++) (simplePrettyPrintBuchi (gtl2ba (gtlModelContract mdl))))++
     ["}"]
  | (name,mdl) <- Map.toList $ gtlSpecModels spec ]

simplePrettyPrintBuchi :: BA [TypedExpr String] Integer -> [String]
simplePrettyPrintBuchi buchi = concat [ [ (if Set.member st (baInits buchi) then "initial " else "")++
                                          (if Set.member st (baFinals buchi) then "final " else "")++
                                          "state "++show st++" {" ] ++
                                        [ "  "++show cond ++ " -> "++show trg
                                        | (cond,trg) <- Set.toList trans ]++
                                        ["}"]
                                      | (st,trans) <- Map.toList (baTransitions buchi)
                                      ]

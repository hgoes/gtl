{-| A simple pretty printer that produces ASCII text. -}
module Language.GTL.Target.Printer
       (simplePrettyPrint) where

import Language.GTL.Model
import Language.GTL.Buchi
import Language.GTL.Expression
import Language.GTL.Translation

import Data.Map as Map
import Data.Set as Set

-- | Render a GTL specification as text
simplePrettyPrint :: GTLSpec String -> String
simplePrettyPrint spec
  = unlines $ concat [
     [name ++ "{"]++
     ["  input "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelInput mdl) ]++
     ["  output "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelOutput mdl) ]++
     ["  local "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelLocals mdl) ]++
     ["  cycle-time "++renderTime (gtlModelCycleTime mdl)]++
     (fmap ("  "++) (simplePrettyPrintBuchi (gtl2ba (Just $ gtlModelCycleTime mdl) (gtlModelContract mdl))))++
     ["}"]
  | (name,mdl) <- Map.toList $ gtlSpecModels spec ] ++
    ["verify {"] ++
    (fmap ("  "++) (simplePrettyPrintBuchi (gtl2ba Nothing $ gnot $ gtlSpecVerify spec))) ++
    ["}"]

renderTime :: Integer -> String
renderTime us
  | us `mod` 1000000 == 0 = show (us `div` 1000000) ++ "s"
  | us `mod` 1000 == 0    = show (us `div` 1000) ++ "ms"
  | otherwise             = show us ++ "us"

simplePrettyPrintBuchi :: Show v => BA [TypedExpr v] Integer -> [String]
simplePrettyPrintBuchi buchi = concat [ [ (if Set.member st (baInits buchi) then "initial " else "")++
                                          (if Set.member st (baFinals buchi) then "final " else "")++
                                          "state "++show st++" {" ] ++
                                        [ "  "++show cond ++ " -> "++show trg
                                        | (cond,trg) <- Set.toList trans ]++
                                        ["}"]
                                      | (st,trans) <- Map.toList (baTransitions buchi)
                                      ]

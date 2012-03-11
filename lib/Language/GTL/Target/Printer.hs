{-| A simple pretty printer that produces ASCII text. -}
module Language.GTL.Target.Printer
       (simplePrettyPrint) where

import Language.GTL.Model
import Language.GTL.Buchi
import Language.GTL.Expression
import Language.GTL.Translation

import Data.Map as Map
import Data.Set as Set
import Data.List (intersperse)

-- | Render a GTL specification as text
simplePrettyPrint :: GTLSpec String -> String
simplePrettyPrint spec
  = unlines $ concat [
     ["component " ++ name
     ,"  inputs"]++
     ["    "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelInput mdl) ]++
     ["  outputs"]++
     ["    "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelOutput mdl) ]++
     ["  locals"]++
     ["    "++show tp++" "++vname | (vname,tp) <- Map.toList (gtlModelLocals mdl) ]++
     ["  cycle-time "++renderTime (gtlModelCycleTime mdl)]++
     (fmap ("  "++) (simplePrettyPrintBuchi localTerm (gtl2ba (Just $ gtlModelCycleTime mdl) (gtlModelContract mdl))))
  | (name,mdl) <- Map.toList $ gtlSpecModels spec ] ++
    ["instance"] ++
	[
	"   "++(gtlInstanceModel inst)++" "++name++
	" "++(instanceContract (gtlInstanceContract inst))
	| (name,inst) <- Map.toList $ gtlSpecInstances spec ] ++
    ["verify"] ++
    (fmap ("  "++) (simplePrettyPrintBuchi globalTerm (gtl2ba Nothing $ gnot $ gtlSpecVerify spec)))

instanceContract :: (Maybe a) -> String
instanceContract inst = case inst of
				Nothing -> "" 
				n -> "todo"

renderTerm :: (v -> Integer -> ShowS) -> Integer -> TypedExpr v -> ShowS
renderTerm f p (Fix expr) = showTermWith f (renderTerm f) p (getValue expr)

localTerm :: String -> Integer -> ShowS
localTerm name 0 = showString name
localTerm name lvl = showString name . showChar '_' . showsPrec 0 lvl

globalTerm :: (String,String) -> Integer -> ShowS
globalTerm (x,y) = localTerm (x++"."++y)

renderTime :: Integer -> String
renderTime us
  | us `mod` 1000000 == 0 = show (us `div` 1000000) ++ "s"
  | us `mod` 1000 == 0    = show (us `div` 1000) ++ "ms"
  | otherwise             = show us ++ "us"

simplePrettyPrintBuchi :: (v -> Integer -> ShowS) -> BA [TypedExpr v] Integer -> [String]
simplePrettyPrintBuchi f buchi = concat [ [ (if Set.member st (baInits buchi) then "initial " else "")++
                                            (if Set.member st (baFinals buchi) then "final " else "")++
                                            "state "++show st] ++
                                          [ "  "++(concat $ intersperse "," (fmap (\t -> renderTerm f 0 t "") cond)) ++ " -> "++show trg
                                          | (cond,trg) <- trans ]
                                        | (st,trans) <- Map.toList (baTransitions buchi)
                                        ]

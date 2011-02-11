module Language.GTL.ErrorRefiner where

import System.Process
import Data.Maybe (mapMaybe)
import Data.BDD
import Data.Map as Map hiding (mapMaybe)
import Data.Bits

import Language.Promela.Syntax as Pr
import Language.GTL.LTL

parseTrace :: FilePath -> FilePath -> IO [(String,Integer)]
parseTrace promela trail = do
  outp <- readProcess "spin" ["-T","-k",trail,promela] ""
  return $ mapMaybe (\ln -> case words ln of
                        ["ENTER",proc,st] -> Just (proc,read st)
                        _ -> Nothing
                    ) (lines outp)

generateBDDCheck :: String -> Int -> Tree s Int -> String
generateBDDCheck name w
  = foldBDD
    (\sym l r -> "((("++name++"&(1<<"++show (w-sym)++"))=="++name++")?"++l++":"++r++")")
    (\v -> if v then "1" else "0")

translateTrace :: (String -> String -> String) -> Map String (Buchi (Map String (Tree s Int))) -> [(String,Integer)] -> [Pr.Step]
translateTrace f mp trace
  = fmap (\(proc,entr) -> let st = (mp!proc)!entr
                              expr = foldl1 (\x y -> x++"&&"++y) [ generateBDDCheck (f proc var) (bitSize (undefined::Int)) tree
                                                                 | (var,tree) <- Map.toList (vars st)]
                          in Pr.StepStmt (Pr.StmtCExpr Nothing expr) Nothing
         ) trace
    ++ [Pr.StepStmt (Pr.StmtDo [[Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.ConstExpr $ Pr.ConstBool True) Nothing]]) Nothing]
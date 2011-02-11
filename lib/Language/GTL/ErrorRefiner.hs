module Language.GTL.ErrorRefiner where

import System.Process
import Data.Maybe (mapMaybe)
import Data.BDD

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
    (\sym l r -> "(("++name++"&(1<<"++show (w-sym)++"))=="++name++")?("++l++"):("++r++")")
    (\v -> if v then "1" else "0")
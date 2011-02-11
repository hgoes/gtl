module Language.GTL.ErrorRefiner where

import System.Process
import Data.Maybe (mapMaybe)

parseTrace :: FilePath -> FilePath -> IO [(String,Integer)]
parseTrace promela trail = do
  outp <- readProcess "spin" ["-T","-k",trail,promela] ""
  return $ mapMaybe (\ln -> case words ln of
                        ["ENTER",proc,st] -> Just (proc,read st)
                        _ -> Nothing
                    ) (lines outp)
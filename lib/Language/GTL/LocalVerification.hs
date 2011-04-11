module Language.GTL.LocalVerification where

import Language.GTL.Model
import Language.GTL.Backend.All
import Data.Map as Map

verifyLocal :: GTLSpec -> IO ()
verifyLocal spec = mapM_ (\(name,mdl) -> do
                             putStrLn $ "Verifying "++name++":"
                             res <- allVerifyLocal (gtlModelBackend mdl) (gtlModelContract mdl)
                             case res of
                               Nothing -> putStrLn "Undecidable"
                               Just True -> putStrLn "Success"
                               Just False -> putStrLn "Failure"
                         ) (Map.toList $ gtlSpecModels spec)
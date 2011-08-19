{-| Provides the formalism-specific verification backend.
 -}
module Language.GTL.Target.Local where

import Language.GTL.Model
import Language.GTL.Backend.All
import Data.Map as Map

import Misc.ProgramOptions as Opts

-- | Performs the formalism-specific verification algorithms for each model
--   in the specification to find out if the contract for the model holds.
verifyLocal :: Opts.Options -- ^ Options
             -> String -- ^ Name of the GTL file without extension
             -> GTLSpec String
             -> IO ()
verifyLocal opts gtlName spec = mapM_ (\(name,mdl) -> do
                             putStrLn $ "Verifying "++name++":"
                             res <- allVerifyLocal (gtlModelBackend mdl) (gtlModelCycleTime mdl) (gtlModelContract mdl) opts gtlName
                             case res of
                               Nothing -> putStrLn "Undecidable"
                               Just True -> putStrLn "Success"
                               Just False -> putStrLn "Failure"
                         ) (Map.toList $ gtlSpecModels spec)

{-| Provides the formalism-specific verification backend.
 -}
module Language.GTL.Target.Local where

import Language.GTL.Model
import Language.GTL.Backend.All
import Data.Map as Map
import Data.Time
import System.IO (hFlush,stdout)

import Misc.ProgramOptions as Opts

-- | Performs the formalism-specific verification algorithms for each model
--   in the specification to find out if the contract for the model holds.
verifyLocal :: Opts.Options -- ^ Options
             -> String -- ^ Name of the GTL file without extension
             -> GTLSpec String
             -> IO ()
verifyLocal opts gtlName spec = mapM_ (\(name,mdl) -> do
                             putStrLn $ "Verifying "++name++":"
                             hFlush stdout
                             start_time <- getCurrentTime
                             res <- (allVerifyLocal (gtlModelBackend mdl))
                                      (gtlModelCycleTime mdl) (gtlModelContract mdl)
                                      (gtlModelLocals mdl) (gtlModelDefaults mdl) (gtlModelConstantInputs mdl) opts gtlName
                             end_time <- getCurrentTime
                             case res of
                               Nothing -> putStr "Undecidable"
                               Just True -> putStr "Success"
                               Just False -> putStr "Failure"
                             putStrLn $ " ("++show (end_time `diffUTCTime` start_time)++")"
                             hFlush stdout
                         ) (Map.toList $ gtlSpecModels spec)

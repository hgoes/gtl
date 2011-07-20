-----------------------------------------------------------------------------
--
-- Module      :  Misc.VerificationEnvironment
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Misc.VerificationEnvironment (
  runVerification
  , parseTraces

) where

import Language.Promela.Syntax as Pr
import Language.Promela.Pretty
import Language.GTL.ErrorRefiner

import System.FilePath
import System.Cmd
import System.Directory
import System.Process
import System.Exit

import Misc.ProgramOptions as Opts

-- | Generate the pan files using Spin
generatePan
  :: String -- ^ Name of the GTL file without extension
  -> FilePath -- ^ Output directory
    -> IO()
generatePan fileName outputDir = do
  currentDir <- getCurrentDirectory
  setCurrentDirectory outputDir
  rawSystem "spin" ["-a", fileName]
  setCurrentDirectory currentDir

-- | Compile the pan.c in the outputDirectory into an executable
compile
  :: Options -- ^ Program options (uses outputPath)
  -> FilePath -- ^ Output directory
  -> String -- ^ Name of the resulting verifier executable
    -> IO()
compile opts outputDir verifier = do
  let input = outputDir </> "pan.c"
      output = outputDir </> verifier
      flags = (ccFlags opts) ++ (ldFlags opts) ++ ["-lcudd", "-lmtr", "-lepd", "-lst", "-lutil", "-lcudd_arith", "-lm"]
  exitCode <- rawSystem (ccBinary opts) ([input, "-o" ++ output] ++ flags)
  case exitCode of
    ExitSuccess -> return ()
    ExitFailure c -> ioError $ userError "Error while running compiler"

runVerifier
  :: String -- ^ Name of theverifier executable
  -> FilePath -- ^ Output directory
    -> IO(String) -- ^ Returns the output of Spin
runVerifier verifier outputDir = do
  currentDir <- getCurrentDirectory
  setCurrentDirectory outputDir
  outp <- readProcess ("." </> verifier) ["-a","-e"] ""
  setCurrentDirectory currentDir
  return outp

runVerification
  :: Options -- ^ Program options (uses outputPath)
  -> String -- ^ Name of the GTL file without extension
  -> [Pr.Module] -- ^ The Promela modules which should be verified
    -> IO([String]) -- ^ Returns a list of trace files in case of errors
runVerification opts name pr = do
  let outputDir = (outputPath opts)
      verifier = (name ++ "-verifier")
  writeFile (outputDir </> name <.> "pr") (show $ prettyPromela pr)
  generatePan (name <.> "pr") outputDir
  compile opts outputDir verifier
  outp <- runVerifier verifier outputDir
  putStrLn "--- Output ---"
  putStrLn outp
  return $ filterTraces outp

-- | Parses the given traces using Spin, then tracks down which
-- transitions have been used in the error and writes the atoms
-- that have to hold in that transition sequence into a fileType
-- /name/.gtltrace. That can be read back to do a conditional run.
parseTraces
  :: Options -- ^ Program options (uses outputPath)
  -> String -- ^ Name of the GTL file without extension
  -> [String] -- ^ Generated trace files
  -> ([(String, Integer, Integer)] -> Trace) -- ^ Function that converts a list of transitions to trace i.e. a list of atoms that have to hold in each transition. /s/ is the transition index.
    -> IO()
parseTraces opts name traceFiles f = do
  currentDir <- getCurrentDirectory
  setCurrentDirectory (outputPath opts)
  traces <- mapM (\trace -> do
                     res <- fmap f $ parseTrace (name <.> "pr") trace
                     return res
                 ) traceFiles
  case traces of
    [] -> putStrLn "No errors found."
    _  -> do
      putStrLn $ show (length traces) ++ " errors found"
      writeTraces (name <.> "gtltrace") traces
      putStrLn $ "Written to "++(name <.> "gtltrace")
  setCurrentDirectory currentDir

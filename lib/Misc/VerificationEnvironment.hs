{-| Provides functions to invoke SPIN and parse the results. -}
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
  outp <- readProcess ("." </> verifier) ["-a"] ""
  setCurrentDirectory currentDir
  return outp

-- | Write a promela file, generate C-code from it using SPIN, compile the
--   generated verifier, invoke it and collect the generated traces.
runVerification
  :: Options -- ^ Program options (uses outputPath)
  -> String -- ^ Name of the GTL file without extension
  -> [Pr.Module] -- ^ The Promela modules which should be verified
    -> IO([String]) -- ^ Returns a list of trace files in case of errors
runVerification opts name pr =
  let outputDir = (outputPath opts)
      verifier = (name ++ "-verifier")
  in
    writeFile (outputDir </> name <.> "pr") (show $ prettyPromela pr) >>
      if not (dryRun opts) then do
        generatePan (name <.> "pr") outputDir
        compile opts outputDir verifier
        outp <- runVerifier verifier outputDir
        putStrLn "--- Output ---"
        putStrLn outp
        return $ filterTraces outp
      else return []

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
      if verbosity opts > 1
        then putStrLn $ renderTraces traces
        else return ()
      writeTraces (name <.> "gtltrace") traces
      putStrLn $ "Written to "++(name <.> "gtltrace")
  setCurrentDirectory currentDir

renderTraces :: [Trace] -> String
renderTraces tr = unlines (renderTraces' 1 tr)
  where
    renderTraces' n [] = []
    renderTraces' n (t:ts) = ("Trace "++show n):renderTrace' n t ts
    renderTrace' n [] ts = renderTraces' n ts
    renderTrace' n (s:ss) ts = renderAtoms' n s ss ts
    renderAtoms' n [] ss ts = "  ~":renderTrace' n ss ts
    renderAtoms' n (a:as) ss ts = ("  "++show a):renderAtoms' n as ss ts
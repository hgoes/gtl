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

) where

import Language.Promela.Pretty
import Language.GTL.ErrorRefiner

import System.FilePath
import System.Cmd
import System.Directory
import System.Process

import Misc.ProgramOptions as Opts

generatePan fileName outputDir = do
  currentDir <- getCurrentDirectory
  setCurrentDirectory outputDir
  rawSystem "spin" ["-a", fileName]
  setCurrentDirectory currentDir

compile opts outputDir verifier = do
  rawSystem (ccBinary opts) ([outputDir </> "pan.c", "-o" ++ (outputDir </> verifier)] ++ (ccFlags opts))

runVerifier verifier outputDir = do
  currentDir <- getCurrentDirectory
  setCurrentDirectory outputDir
  outp <- readProcess ("." </> verifier) ["-a","-e"] ""
  setCurrentDirectory currentDir
  return outp

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


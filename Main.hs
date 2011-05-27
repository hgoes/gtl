{-# LANGUAGE CPP #-}
module Main where

import System.FilePath
import System.Process
import Control.Monad (when)
import System.Exit
import System.Directory
import System.IO.Error

import Language.GTL.Parser.Lexer as GTL
import Language.GTL.Parser as GTL
import Language.Scade.Lexer as Sc
import Language.Scade.Parser as Sc
import Language.Promela.Pretty
import Language.Scade.Pretty

import Language.GTL.PromelaCIntegration
import Language.GTL.LocalVerification
import Language.GTL.Translation
import Language.GTL.Model
import Language.GTL.PromelaDynamicBDD as PrBd
import Language.GTL.PrettyPrinter as PrPr
import Language.GTL.PromelaNative as PrNat

import Misc.ProgramOptions

x2s :: FilePath -> IO String
x2s fp = readProcess "C:\\Program Files\\Esterel Technologies\\SCADE 6.1.2\\SCADE Suite\\bin\\x2s.exe" [fp] ""

loadScade :: FilePath -> IO String
loadScade fp = case takeExtension fp of
  ".scade" -> readFile fp
  ".xscade" -> x2s fp

loadScades :: [FilePath] -> IO String
loadScades = fmap concat . mapM loadScade

versionString :: String
versionString = "This is the GALS Translation Language of version "++version++".\nBuilt on "++date++"."
                ++(case tag of
                      Nothing -> ""
                      Just rtag -> "\nBuilt from git tag: "++rtag++".")
                ++(case branch of
                      Nothing -> ""
                      Just rbranch -> "\nBuilt from git branch: "++rbranch++".")
  where
#ifdef BUILD_VERSION
    version = BUILD_VERSION
#else
    version = "unknown"
#endif
#ifdef BUILD_DATE
    date = BUILD_DATE
#else
    date = "unknown date"
#endif
#ifdef BUILD_TAG
    tag = Just BUILD_TAG
#else
    tag = Nothing
#endif
#ifdef BUILD_BRANCH
    branch = Just BUILD_BRANCH
#else
    branch = Nothing
#endif

main = do
  (opts,gtl_file) <- getOptions
  when (showHelp opts) $ do
    putStr usage
    exitSuccess
  when (showVersion opts) $ do
    putStrLn versionString
    exitSuccess
  (createDirectoryIfMissing True $ outputPath opts)
    `catch` (\e -> putStrLn $ "Could not create build dir: " ++ (ioeGetErrorString e))
  gtl_str <- readFile gtl_file
  mgtl <- gtlParseSpec $ GTL.gtl $ GTL.lexGTL gtl_str
  rgtl <- case mgtl of
    Left err -> error err
    Right x -> return x
  case mode opts of
    NativeC -> translateGTL (traceFile opts) rgtl >>= putStrLn
    Local -> verifyLocal rgtl
    PromelaBuddy -> PrBd.verifyModel opts (dropExtension gtl_file) rgtl
    Tikz -> do
      str <- PrPr.gtlToTikz rgtl
      putStrLn str
    Pretty -> putStrLn (simplePrettyPrint rgtl)
    Native -> PrNat.verifyModel opts (dropExtension gtl_file) rgtl
  return ()

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
import Language.UPPAAL.PrettyPrinter

import Language.GTL.Target.PromelaKCG
import Language.GTL.Target.Local
import Language.GTL.Translation
import Language.GTL.Model
--import Language.GTL.Target.PromelaCUDD as PrBd
--import Language.GTL.Target.PrettyPrinter as PrPr
import Language.GTL.Target.Promela as PrNat
import Language.GTL.Target.UPPAAL as UPP
import Language.GTL.Target.Printer

import Misc.ProgramOptions

x2s :: Options -> FilePath -> IO String
x2s opts fp = case (scadeRoot opts) of
  Nothing -> return ""
  Just p -> readProcess (p </> "SCADE Suite" </> "bin" </> "x2s.exe") [fp] ""

modes :: [(String,TranslationMode)]
modes = [("native-c",NativeC),("local",Local),{-("promela-buddy",PromelaBuddy),-}{-("tikz",Tikz),-}("pretty",Pretty),("native",Native),("uppaal",UPPAAL)]

modeString :: (Show a,Eq b) => b -> [(a,b)] -> String
modeString def [] = ""
modeString def [(name,md)] = show name ++ (if md==def
                                           then "(default)"
                                           else "")
modeString def names = buildOr names
  where
    buildOr ((name,md):names) = show name ++ (if md==def
                                              then "(default)"
                                              else "")++
                                case names of
                                  [(name2,md2)] -> " or " ++ show name2 ++ (if md2==def
                                                                            then "(default)"
                                                                            else "")
                                  _ -> ", "++buildOr names

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
  opts <- getOptions
  when (showHelp opts) $ do
    putStr usage
    exitSuccess
  when (showVersion opts) $ do
    putStrLn versionString
    exitSuccess
  let gtl_file = gtlFile opts
  print $ ccFlags opts
  print $ ldFlags opts
  when (gtl_file == "") $ do
    ioError $ userError "No GTL file given"
  exists <- doesFileExist gtl_file
  when (not exists) $ do
    ioError . userError $ (gtl_file ++ " does not exist.")
  (createDirectoryIfMissing True $ outputPath opts)
    `catch` (\e -> putStrLn $ "Could not create build dir: " ++ (ioeGetErrorString e))
  gtl_str <- readFile gtl_file
  mgtl <- gtlParseSpec $ GTL.gtl $ GTL.lexGTL gtl_str
  rgtl <- case mgtl of
    Left err -> error err
    Right x -> return x
  case mode opts of
    NativeC -> translateGTL (traceFile opts) rgtl >>= putStrLn
    Local -> verifyLocal opts (dropExtension gtl_file) rgtl
    --PromelaBuddy -> PrBd.verifyModel opts (dropExtension gtl_file) rgtl
    {-Tikz -> do
      str <- PrPr.gtlToTikz rgtl
      putStrLn str-}
    Pretty -> putStrLn (simplePrettyPrint rgtl)
    Native -> PrNat.verifyModel opts (dropExtension gtl_file) rgtl
    UPPAAL -> putStr (prettySpecification $ UPP.translateSpec rgtl)
  return ()

{-# LANGUAGE CPP #-}
module Main where

import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Process
import Control.Monad (when)
import System.Exit
import Control.Exception
import Prelude hiding (catch)

import Language.GTL.Parser.Lexer as GTL
import Language.GTL.Parser as GTL
import Language.Scade.Lexer as Sc
import Language.Scade.Parser as Sc
import Language.Promela.Pretty
import Language.Scade.Pretty

import Language.GTL.Target.PromelaKCG
import Language.GTL.Target.Local
import Language.GTL.Translation
import Language.GTL.Model
import Language.GTL.Target.PromelaCUDD as PrBd
--import Language.GTL.Target.PrettyPrinter as PrPr
import Language.GTL.Target.Promela as PrNat

data TranslationMode
     = NativeC
     | Local
     | PromelaBuddy
--     | Tikz
--     | Pretty
     | Native
     deriving (Show,Eq)

data Options = Options
               { mode :: TranslationMode
               , traceFile :: Maybe FilePath
               , keepTmpFiles :: Bool
               , showHelp :: Bool
               , showVersion :: Bool
               , ccBinary :: String
               , ccFlags :: [String]
               }
               deriving Show

defaultOptions = Options
  { mode = Native
  , traceFile = Nothing
  , keepTmpFiles = False
  , showHelp = False
  , showVersion = False
  , ccBinary = "gcc"
  , ccFlags = []
  }

modes :: [(String,TranslationMode)]
modes = [("native-c",NativeC),("local",Local),("promela-buddy",PromelaBuddy),{-("tikz",Tikz),("pretty",Pretty),-}("native",Native)]

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


options :: [OptDescr (Options -> Options)]
options = [Option ['m'] ["mode"] (ReqArg (\str opt -> case lookup str modes of
                                             Just rmode -> opt { mode = rmode }
                                             Nothing -> error $ "Unknown mode "++show str
                                         ) "mode"
                                 ) ("The tranlation mode ("++modeString (mode defaultOptions) modes++")")
          ,Option ['t'] ["trace-file"] (ReqArg (\str opt -> opt { traceFile = Just str }) "file") "Use a trace file to restrict a simulation"
          ,Option ['k'] ["keep"] (NoArg (\opt -> opt { keepTmpFiles = True })) "Keep temporary files"
          ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help information"
          ,Option ['v'] ["version"] (NoArg (\opt -> opt { showVersion = True })) "Show version information"
          ]

x2s :: FilePath -> IO String
x2s fp = readProcess "C:\\Program Files\\Esterel Technologies\\SCADE 6.1.2\\SCADE Suite\\bin\\x2s.exe" [fp] ""

loadScade :: FilePath -> IO String
loadScade fp = case takeExtension fp of
  ".scade" -> readFile fp
  ".xscade" -> x2s fp

loadScades :: [FilePath] -> IO String
loadScades = fmap concat . mapM loadScade

header :: String
header = "Usage: gtl [OPTION...] gtl-file"

getOptions :: IO (Options,String)
getOptions = do
  args <- getArgs
  gcc <- catch (getEnv "CC") (\e -> const (return "gcc") (e::SomeException))
  cflags <- catch (fmap words $ getEnv "CFLAGS") (\e -> const (return []) (e::SomeException))
  let start_opts = defaultOptions { ccBinary = gcc
                                  , ccFlags = cflags
                                  }
  case getOpt Permute options args of
    (o,[n1],[]) -> return (foldl (flip id) start_opts o,n1)
    (o,_,[]) -> return (foldl (flip id) start_opts o,error "Exactly one argument required")
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

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
    putStr (usageInfo header options)
    exitSuccess
  when (showVersion opts) $ do
    putStrLn versionString
    exitSuccess
  gtl_str <- readFile gtl_file
  mgtl <- gtlParseSpec $ GTL.gtl $ GTL.lexGTL gtl_str
  rgtl <- case mgtl of
    Left err -> error err
    Right x -> return x
  case mode opts of
    NativeC -> translateGTL (traceFile opts) rgtl >>= putStrLn
    Local -> verifyLocal rgtl
    PromelaBuddy -> PrBd.verifyModel (keepTmpFiles opts) (ccBinary opts) (ccFlags opts) (dropExtension gtl_file) rgtl
    {-Tikz -> do
      str <- PrPr.gtlToTikz rgtl
      putStrLn str
    Pretty -> putStrLn (simplePrettyPrint rgtl)-}
    Native -> print (prettyPromela $ PrNat.translateSpec rgtl)
  return ()

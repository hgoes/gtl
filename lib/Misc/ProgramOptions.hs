-----------------------------------------------------------------------------
--
-- Module      :  ProgramOptions
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

module Misc.ProgramOptions (
  TranslationMode(..),
  Options(..),
  getOptions,
  usage
) where

import System.Console.GetOpt
import System.Environment
import Control.Exception
import Prelude hiding (catch)

data TranslationMode
     = NativeC
     | Local
     | PromelaBuddy
     | Tikz
     | Pretty
     | Native
     deriving (Show,Eq)

data Options = Options
               { mode :: TranslationMode
               , traceFile :: Maybe FilePath
               , outputPath :: String
               , showHelp :: Bool
               , showVersion :: Bool
               , ccBinary :: String
               , ccFlags :: [String]
               }
               deriving Show

defaultOptions = Options
  { mode = PromelaBuddy
  , traceFile = Nothing
  , outputPath = "."
  , showHelp = False
  , showVersion = False
  , ccBinary = "gcc"
  , ccFlags = []
  }

modes :: [(String,TranslationMode)]
modes = [("native-c",NativeC),("local",Local),("promela-buddy",PromelaBuddy),("tikz",Tikz),("pretty",Pretty),("native",Native)]

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
          ,Option ['o'] ["output-directory"] (ReqArg (\path opts -> opts { outputPath = path }) "path") "Path into which the output should be generated"
          ,Option ['h'] ["help"] (NoArg (\opt -> opt { showHelp = True })) "Show this help information"
          ,Option ['v'] ["version"] (NoArg (\opt -> opt { showVersion = True })) "Show version information"
          ]

header :: String
header = "Usage: gtl [OPTION...] gtl-file"

usage = usageInfo header options

getOptions :: IO (Options,String)
getOptions = do
  args <- getArgs
  gcc <- catch (getEnv "CC") (\e -> const (return "gcc") (e::SomeException))
  cflags <- catch (fmap words $ getEnv "CFLAGS") (\e -> const (return []) (e::SomeException))
  print $ show cflags
  let start_opts = defaultOptions { ccBinary = gcc
                                  , ccFlags = cflags
                                  }
  case getOpt Permute options args of
    (o,[n1],[]) -> return (foldl (flip id) start_opts o,n1)
    (o,_,[]) -> return (foldl (flip id) start_opts o,error "Exactly one argument required")
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

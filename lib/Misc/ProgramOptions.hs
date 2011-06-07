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
import Data.List (unfoldr)
import System.Directory (doesFileExist)
import Data.Graph.Inductive.Query.Monad (mapSnd)

data TranslationMode
     = NativeC
     | Local
     | PromelaBuddy
     | Tikz
     | Pretty
     | Native
     deriving (Show,Eq)

data Options = Options
               { gtlFile :: FilePath
               , mode :: TranslationMode
               , traceFile :: Maybe FilePath
               , outputPath :: String
               , showHelp :: Bool
               , showVersion :: Bool
               , ccBinary :: String
               , ccFlags :: [String]
               , ldFlags :: [String]
               }
               deriving Show

defaultOptions = Options
  { gtlFile = ""
  , mode = PromelaBuddy
  , traceFile = Nothing
  , outputPath = "."
  , showHelp = False
  , showVersion = False
  , ccBinary = "gcc"
  , ccFlags = []
  , ldFlags = []
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

getOptions :: IO Options
getOptions = do
  args <- getArgs
  gcc <- catch (getEnv "CC") (\e -> const (return "gcc") (e::SomeException))
  cflags <- catch (fmap splitOptions $ getEnv "CFLAGS") (\e -> const (return []) (e::SomeException))
  ldflags <- catch (fmap splitOptions $ getEnv "LDFLAGS") (\e -> const (return []) (e::SomeException))
  let start_opts = defaultOptions { ccBinary = gcc
                                  , ccFlags = cflags
                                  , ldFlags = ldflags
                                  }
  case getOpt (ReturnInOrder parseFreeOptions) options args of
    (o, [], []) -> do
      opts <- return $ foldl (flip id) start_opts o
      exists <- doesFileExist (gtlFile opts)
      if gtlFile opts == "" then
        ioError $ userError "No GTL file given"
        else
          if not exists then ioError . userError $ "Not a valid file"
          else
            return opts
    (_, opts, []) -> ioError . userError $ "Unparsed options: " ++ show opts
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

-- | Parses the options which do not start with "-" or "--" but
-- are just assignments (as in CFLAGS="...") or the name of the
-- GTL file.
parseFreeOptions :: String -> (Options -> Options)
parseFreeOptions o =
  let (optName, value) = mapSnd (drop 1) $ span (/= '=') o
  in case optName of
    "CC" -> \opts -> opts { ccBinary = value }
    "CFLAGS" -> \opts -> opts { ccFlags = ccFlags opts ++ (splitOptions $ value) }
    "LDFLAGS" -> \opts -> opts { ldFlags = ldFlags opts ++ (splitOptions $ value) }
    otherwise -> if null value
      then (\opts -> if null $ gtlFile opts then opts { gtlFile = optName } else error "Only one file allowed")
      else error $ "Unknown option " ++ optName

-- | Splits program options by " -" into a list usable for
-- running processes with these options.
splitOptions :: String -> [String]
splitOptions = map (prependIfNecessary '-') . (split (" -"))
  where
    prependIfNecessary :: Eq a => a -> [a] -> [a]
    prependIfNecessary s l@(x:xs) = if s == x then l else s:l

-- | Split list into tokens at break point
split :: Eq a => [a] -> [a] -> [[a]]
split p = unfoldr (split' p)
  where
    split' :: Eq a => [a] -> [a] -> Maybe ([a], [a])
    split' _ [] = Nothing
    split' p l = Just (pre, drop (length p) post)
      where
        (pre, post) = span p l

        span :: Eq a => [a] -> [a] -> ([a], [a])
        span _ [] = ([], [])
        span s l@(x:xs)
          = if match s l then
            ([], l)
          else
            (x:m, r)
          where
            (m, r) = span s xs

        match [] _ = True
        match _ [] = False
        match (t:ts) (s:ss) = if t == s then match ts ss else False

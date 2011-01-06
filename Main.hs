module Main where

import System.Console.GetOpt
import System.Environment

import Language.GTL.Lexer as GTL
import Language.GTL.Parser as GTL
import Language.Scade.Lexer as Sc
import Language.Scade.Parser as Sc
import Language.Promela.Pretty

import Language.GTL.PromelaContract
import Language.GTL.PromelaCIntegration

data TranslationMode
     = NativeC
     | PromelaContract
     deriving Show

data Options = Options
               { mode :: TranslationMode
               }
               deriving Show

defaultOptions = Options
  { mode = PromelaContract
  }

options :: [OptDescr (Options -> Options)]
options = [Option ['m'] ["mode"] (ReqArg (\str opt -> case str of
                                             "native-c" -> opt { mode = NativeC }
                                             "promela-contract" -> opt { mode = PromelaContract }
                                             _ -> error $ "Unknown mode "++str) "mode") "The tranlation mode (either \"native-c\" or \"promela-contract\""
          ]

header :: String
header = "Usage: gtl [OPTION...] gtl-file scadefile"

getOptions :: IO (Options,String,String)
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    (o,[n1,n2],[]) -> return (foldl (flip id) defaultOptions o,n1,n2)
    (_,_,[]) -> ioError (userError "Exactly two arguments required")
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

main = do
  (opts,gtl_file,sc_file) <- getOptions
  case mode opts of
    PromelaContract -> do
      gtl_str <- readFile gtl_file
      sc_str <- readFile sc_file
      let gtl_decls = GTL.gtl $ GTL.alexScanTokens gtl_str
          sc_decls = Sc.scade $ Sc.alexScanTokens sc_str
      print $ prettyPromela $ translateContracts sc_decls gtl_decls
    NativeC -> translateGTL gtl_file sc_file >>= putStr
  return ()
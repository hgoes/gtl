module Main where

import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Process

import Language.GTL.Lexer as GTL
import Language.GTL.Parser as GTL
import Language.Scade.Lexer as Sc
import Language.Scade.Parser as Sc
import Language.Promela.Pretty
import Language.Scade.Pretty

import Language.GTL.PromelaContract as PrTr
import Language.GTL.PromelaCIntegration
import Language.GTL.ScadeContract as ScTr
import Language.GTL.Translation

data TranslationMode
     = NativeC
     | PromelaContract
     | ScadeContract
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
                                             "scade-contract" -> opt { mode = ScadeContract }
                                             _ -> error $ "Unknown mode "++str) "mode"
                                 ) "The tranlation mode (either \"native-c\" or \"promela-contract\""
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
header = "Usage: gtl [OPTION...] gtl-file scadefiles"

getOptions :: IO (Options,String,[String])
getOptions = do
  args <- getArgs
  case getOpt Permute options args of
    (o,n1:ns,[]) -> return (foldl (flip id) defaultOptions o,n1,ns)
    (_,_,[]) -> ioError (userError "At least one argument required")
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

main = do
  (opts,gtl_file,sc_files) <- getOptions
  gtl_str <- readFile gtl_file
  sc_str <- loadScades sc_files
  let gtl_decls = GTL.gtl $ GTL.alexScanTokens gtl_str
      sc_decls = Sc.scade $ Sc.alexScanTokens sc_str
  case mode opts of
    PromelaContract -> print $ prettyPromela $ PrTr.translateContracts sc_decls gtl_decls
    NativeC -> translateGTL gtl_decls sc_decls >>= putStr
    ScadeContract -> do
      putStrLn sc_str
      print $ prettyScade $ ScTr.translateContracts sc_decls gtl_decls
  return ()
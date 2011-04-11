module Main where

import System.Console.GetOpt
import System.Environment
import System.FilePath
import System.Process
import Control.Monad (when)
import System.Exit

import Language.GTL.Lexer as GTL
import Language.GTL.Parser as GTL
import Language.Scade.Lexer as Sc
import Language.Scade.Parser as Sc
import Language.Promela.Pretty
import Language.Scade.Pretty

import Language.GTL.PromelaCIntegration
--import Language.GTL.ScadeContract as ScTr
import Language.GTL.Translation
import Language.GTL.Model
import Language.GTL.ScadeToPromela as ScPr
import Language.GTL.PromelaDynamicBDD as PrBd

data TranslationMode
     = NativeC
     | ScadeContract
     | ScadeToPromela
     | PromelaBuddy
     deriving (Show,Eq)

data Options = Options
               { mode :: TranslationMode
               , traceFile :: Maybe FilePath
               , keepTmpFiles :: Bool
               , showHelp :: Bool
               }
               deriving Show

defaultOptions = Options
  { mode = PromelaBuddy
  , traceFile = Nothing
  , keepTmpFiles = False
  , showHelp = False
  }

modes :: [(String,TranslationMode)]
modes = [("native-c",NativeC),("scade-contract",ScadeContract),("scade-promela",ScadeToPromela),("promela-buddy",PromelaBuddy)]

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
    (o,_,[]) -> if showHelp $ foldl (flip id) defaultOptions o
                then putStr (usageInfo header options) >> exitSuccess
                else ioError (userError "At least one argument required")
    (_,_,errs) -> ioError (userError $ concat errs ++ usageInfo header options)

main = do
  (opts,gtl_file,sc_files) <- getOptions
  gtl_str <- readFile gtl_file
  sc_str <- loadScades sc_files
  let sc_decls = Sc.scade $ Sc.alexScanTokens sc_str
  mgtl <- gtlParseSpec $ GTL.gtl $ GTL.lexGTL gtl_str
  rgtl <- case mgtl of
    Left err -> error err
    Right x -> return x
  case mode opts of
    NativeC -> translateGTL (traceFile opts) rgtl sc_decls >>= putStrLn
    {-ScadeContract -> do
      putStrLn sc_str
      print $ prettyScade $ ScTr.translateContracts sc_decls gtl_decls-}
    ScadeToPromela -> print $ prettyPromela $ ScPr.scadeToPromela sc_decls
    PromelaBuddy -> PrBd.verifyModel (keepTmpFiles opts) (dropExtension gtl_file) sc_decls rgtl
      --print $ prettyPromela $ PrBd.translateContracts sc_decls gtl_decls
  return ()
module Language.GTL.ErrorRefiner where

import System.Process
import Data.Maybe (mapMaybe)
import Data.BDD
import Data.BDD.Serialization
import Data.Map as Map hiding (mapMaybe)
import Data.Bits
import Data.Binary
import Data.Binary.Put
import Data.Binary.Get
import System.FilePath
import Language.Promela.Pretty
import Control.Monad
import Control.Monad.Trans
import qualified Data.ByteString.Lazy as LBS
import Codec.Compression.BZip

import Language.Promela.Syntax as Pr
import Language.GTL.LTL

type BDDTrace s = [(String,Map String (Tree s Int))]

generateBDDCheck :: String -> Int -> Tree s Int -> String
generateBDDCheck name w
  = foldBDD
    (\sym l r -> "((("++name++"&(1<<"++show (w-sym)++"))=="++name++")?"++l++":"++r++")")
    (\v -> if v then "1" else "0")

parseTrace :: FilePath -> FilePath -> IO [(String,Integer)]
parseTrace promela trail = do
  outp <- readProcess "spin" ["-T","-k",trail,promela] ""
  return $ mapMaybe (\ln -> case words ln of
                        ["ENTER",proc,st] -> Just (proc,read st)
                        _ -> Nothing
                    ) (lines outp)

filterTraces :: String -> [String]
filterTraces outp = mapMaybe (\ln -> case words ln of
                                 ["pan:","wrote",fn] -> Just fn
                                 _ -> Nothing) (lines outp)

writeTraces :: FilePath -> [BDDTrace s] -> IO ()
writeTraces fp traces = LBS.writeFile fp $ compress $ runPut (do
                                                                 put $ length traces
                                                                 mapM_ putBDDTrace traces)

runBDDMGet :: Monad m => BDDM s Int Get a -> LBS.ByteString -> BDDM s Int m a
runBDDMGet act str = do
  getm <- debase act
  return $ runGet getm str
  

readBDDTraces :: FilePath -> BDDM s Int IO [BDDTrace s]
readBDDTraces fp = do
  str <- lift $ LBS.readFile fp
  runBDDMGet (do
                 len <- lift get
                 replicateM len getBDDTrace) str
  

putBDDTrace :: BDDTrace s -> Put
putBDDTrace tr = do
  put $ length tr
  mapM_ (\(mdl,mp) -> do
            put mdl
            put (Map.size mp)
            mapM (\(var,tree) -> do
                     put var
                     serializeTree tree
                 ) (Map.toAscList mp)) tr

getBDDTrace :: BDDM s Int Get (BDDTrace s)
getBDDTrace = do
  len <- lift get
  replicateM len $ do
    mdl <- lift get
    sz <- lift get
    lmp <- replicateM sz $ do
      var <- lift get
      tree <- deserializeTree 
      return (var,tree)
    return (mdl,Map.fromAscList lmp)

traceToPromela :: (String -> String -> String) -> BDDTrace s -> [Pr.Step]
traceToPromela f trace
  = fmap (\(mdl,vars) -> let expr = foldl1 (\x y -> x++"&&"++y) [ generateBDDCheck (f mdl var) (bitSize (undefined::Int)) tree
                                                                | (var,tree) <- Map.toList vars]
                         in Pr.StepStmt (Pr.StmtCExpr Nothing expr) Nothing
         ) trace
    ++ [Pr.StepStmt (Pr.StmtDo [[Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.ConstExpr $ Pr.ConstBool True) Nothing]]) Nothing]
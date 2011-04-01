{-# LANGUAGE GADTs #-}
module Language.GTL.ErrorRefiner where

import System.Process
import Data.Maybe (mapMaybe)
import Data.BDD
import Data.BDD.Serialization
import Data.Map as Map hiding (mapMaybe)
import Data.Set as Set
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
import Data.List (genericLength)

import Language.Promela.Syntax as Pr
import Language.GTL.LTL
import qualified Language.GTL.Syntax as GTL
import Language.GTL.Translation

--type BDDTrace s = [(String,Map (String,Integer) (Tree s Int))]

type BDDTrace = [[GTLAtom (String,String)]]

generateBDDCheck :: String -> Int -> Tree s Int -> String
generateBDDCheck name w
  = foldBDD
    (\sym l r -> "((("++name++"|(1<<"++show (w-sym-1)++"))=="++name++")?"++l++":"++r++")")
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

writeTraces :: FilePath -> [BDDTrace] -> IO ()
writeTraces fp traces = LBS.writeFile fp $ compress $ runPut $ put traces

readBDDTraces :: FilePath -> IO [BDDTrace]
readBDDTraces fp = do
  str <- LBS.readFile fp
  return $ runGet get (decompress str)

atomToC :: (String -> String -> Integer -> String) -> GTLAtom (String,String) -> String
atomToC f (GTLRel rel lhs rhs) = (exprToC f lhs) ++ (relToC rel) ++ (exprToC f rhs)
atomToC f (GTLElem (q,n) vals b) = (if b then "(" else "!(") ++ 
                                   (foldl1 (\x y -> x++"||"++y) (fmap (\v -> "("++(f q n 0) ++ "=="++show v ++ ")") vals)) ++
                                   ")"
atomToC f (GTLVar (q,n) h b) = (if b then "" else "!") ++ (f q n h)

relToC :: GTL.Relation -> String
relToC GTL.BinLT = "<"
relToC GTL.BinLTEq = "<="
relToC GTL.BinGT = ">"
relToC GTL.BinGTEq = ">="
relToC GTL.BinEq = "=="
relToC GTL.BinNEq = "!="

exprToC :: (String -> String -> Integer -> String) -> GTL.Expr (String,String) Int -> String
exprToC f (GTL.ExprVar (q,n) h) = f q n h
exprToC f (GTL.ExprConst c) = show c
exprToC f (GTL.ExprBinInt op lhs rhs) = "("++(exprToC f lhs)++(intOpToC op)++(exprToC f rhs)++")"

intOpToC :: GTL.IntOp -> String
intOpToC GTL.OpPlus = "+"
intOpToC GTL.OpMinus = "-"
intOpToC GTL.OpMult = "*"
intOpTOC GTL.OpDiv = "/"
           
traceToPromela :: (String -> String -> Integer -> String) -> BDDTrace -> [Pr.Step]
traceToPromela f trace
  = fmap (\ats -> toStep $ case ats of
             [] -> Pr.StmtSkip
             _ -> Pr.StmtCExpr Nothing (foldl1 (\x y -> x++"&&"++y) (fmap (atomToC f) ats))
         ) trace
    ++ [Pr.StepStmt (Pr.StmtDo [[Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.ConstExpr $ Pr.ConstBool True) Nothing]]) Nothing]

traceElemToC :: (String -> String -> Integer -> String) -> [GTLAtom (String,String)] -> String
traceElemToC f [] = "1"
traceElemToC f ats = foldl1 (\x y -> x++"&&"++y) (fmap (atomToC f) ats)

traceToBuchi :: (String -> String -> Integer -> String) -> BDDTrace -> Buchi (Maybe String)
traceToBuchi f trace = let states = zipWith (\n st -> (n,BuchiState { isStart = n==0
                                                                    , vars = Just $ traceElemToC f st
                                                                    , finalSets = Set.empty
                                                                    , successors = Set.singleton (n+1)
                                                                    })) [0..] trace
                           len = genericLength trace
                           end = (len,BuchiState { isStart = len==0
                                                 , vars = Nothing
                                                 , finalSets = Set.singleton (-1)
                                                 , successors = Set.singleton len
                                                 })
                       in Map.fromList (end:states)
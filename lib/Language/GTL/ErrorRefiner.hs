{-# LANGUAGE GADTs #-}
{-| This module helps with the generation, storing, analyzing and processing of
    trace files.
 -}
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
import qualified Language.GTL.Expression as GTL
import Language.GTL.Translation

-- | A trace is a list of requirements.
--   Each requirement corresponds to a step in the model.
--   Each requirement is a list of atoms that have to be true in the corresponding step.
type Trace = [[GTLAtom (String,String)]]

-- | Converts GTL variables to C-names.
--   Takes the component name, the variable name and the history level of the variable.
type CNameGen = String -> String -> Integer -> String

-- | Parse a SPIN trace file by calling it with the spin interpreter and parsing the output.
--   Produces a list of tuples where the first component is the name of the component that
--   just performed a step and the second one is the state number that it transitioned into.
parseTrace :: FilePath -- ^ The promela file of the model
              -> FilePath -- ^ The path to the promela trail file
              -> IO [(String,Integer)]
parseTrace promela trail = do
  outp <- readProcess "spin" ["-T","-k",trail,promela] ""
  return $ mapMaybe (\ln -> case words ln of
                        ["ENTER",proc,st] -> Just (proc,read st)
                        _ -> Nothing
                    ) (lines outp)

-- | Given the output of a spin verifier, extract the filenames of traces.
filterTraces :: String -> [String]
filterTraces outp = mapMaybe (\ln -> case words ln of
                                 ["pan:","wrote",fn] -> Just fn
                                 _ -> Nothing) (lines outp)

-- | Write a list of traces into a file.
writeTraces :: FilePath -> [Trace] -> IO ()
writeTraces fp traces = LBS.writeFile fp $ compress $ runPut $ put traces

-- | Read a list of traces from a file.
readBDDTraces :: FilePath -> IO [Trace]
readBDDTraces fp = do
  str <- LBS.readFile fp
  return $ runGet get (decompress str)

-- | Given a function to generate names, this function converts a GTL atom into a C-expression.
atomToC :: CNameGen -- ^ Function to generate C-names
           -> GTLAtom (String,String) -- ^ GTL atom to convert
           -> String
atomToC f (GTLRel rel (GTL.EqualExpr lhs rhs)) = (exprToC f lhs) ++ (relToC rel) ++ (exprToC f rhs)
atomToC f (GTLElem (q,n) vals b) = (if b then "(" else "!(") ++ 
                                   (foldl1 (\x y -> x++"||"++y) (fmap (\v -> "("++(f q n 0) ++ "=="++show v ++ ")") vals)) ++
                                   ")"
atomToC f (GTLVar (q,n) h b) = (if b then "" else "!") ++ (f q n h)

-- | Convert a GTL relation to a C operator
relToC :: GTL.Relation -> String
relToC GTL.BinLT = "<"
relToC GTL.BinLTEq = "<="
relToC GTL.BinGT = ">"
relToC GTL.BinGTEq = ">="
relToC GTL.BinEq = "=="
relToC GTL.BinNEq = "!="

-- | Convert a GTL expression to a C-expression
exprToC :: Show t => CNameGen -> GTL.Expr (String,String) t -> String
exprToC f (GTL.ExprVar (q,n) h) = f q n h
exprToC f (GTL.ExprConst c) = show c
exprToC f (GTL.ExprBinInt op lhs rhs) = "("++(exprToC f lhs)++(intOpToC op)++(exprToC f rhs)++")"

-- | Convert a GTL integer operator to a C-operator
intOpToC :: GTL.IntOp -> String
intOpToC GTL.OpPlus = "+"
intOpToC GTL.OpMinus = "-"
intOpToC GTL.OpMult = "*"
intOpTOC GTL.OpDiv = "/"

-- | Convert a trace into a promela module that checks if everything conforms to the trace.
traceToPromela :: CNameGen -> Trace -> [Pr.Step]
traceToPromela f trace
  = fmap (\ats -> toStep $ case ats of
             [] -> Pr.StmtSkip
             _ -> Pr.StmtCExpr Nothing (foldl1 (\x y -> x++"&&"++y) (fmap (atomToC f) ats))
         ) trace
    ++ [Pr.StepStmt (Pr.StmtDo [[Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.ConstExpr $ Pr.ConstBool True) Nothing]]) Nothing]

-- | Convert a element from a trace into a C-expression.
traceElemToC :: CNameGen -> [GTLAtom (String,String)] -> String
traceElemToC f [] = "1"
traceElemToC f ats = foldl1 (\x y -> x++"&&"++y) (fmap (atomToC f) ats)

-- | Convert a trace into a buchi automaton that checks for conformance to that trace.
traceToBuchi :: CNameGen -> Trace -> Buchi (Maybe String)
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
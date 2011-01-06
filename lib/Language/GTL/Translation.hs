{-# LANGUAGE TypeSynonymInstances #-}
module Language.GTL.Translation where

import Data.Map as Map
import Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,foldl1,concat)
import Data.List (intersperse)
--import Data.List (foldl1)

import Language.GTL.Syntax

type CanonFormula = CanonFormulaT (Set Condition)

type CanonFormulaT a = Set (ClauseT a)

type Clause = ClauseT (Set Condition)

data ClauseT a = ClauseT
                 { clauseVars :: Map String a
                 , clauseNext :: CanonFormulaT a
                 , clauseAlways :: CanonFormulaT a
                 } deriving (Eq,Ord)

data Condition = CondLT Integer
               | CondLTEq Integer
               | CondGT Integer
               | CondGTEq Integer
               | CondElem [Integer]
               | CondNElem [Integer]
               deriving (Eq,Ord)

instance Show Clause where
  show cl = concat $ intersperse " and " ([ var ++ show cond | (var,conds) <- Map.toList (clauseVars cl), cond <- Set.toList conds ]
                                          ++(if Set.null (clauseNext cl)
                                             then []
                                             else ["next ("++showFormula (clauseNext cl)++")"])
                                          ++(if Set.null (clauseAlways cl)
                                             then []
                                             else ["always ("++showFormula (clauseAlways cl)++")"]))

showFormula :: CanonFormula -> String
showFormula cls = case Set.size cls of
  0 -> "true"
  1 -> let cl = Set.toList cls in show cl
  _ -> concat $ intersperse " or " [ "(" ++ show cl ++ ")" | cl <- Set.toList cls ]
  

instance Show Condition where
  show (CondLT x) = "<"++show x
  show (CondLTEq x) = "<="++show x
  show (CondGT x) = ">"++show x
  show (CondGTEq x) = ">="++show x
  show (CondElem rng) = " in "++show rng
  show (CondNElem rng) = " nin "++show rng

translateContract :: [Formula] -> CanonFormula
translateContract [] = Set.empty
translateContract (x:xs) = foldl (\st nxt -> canonAnd st (translateFormula nxt))
                           (translateFormula x) xs

canonAndM :: (Monad m,Ord a) => (a -> a -> m a) -> CanonFormulaT a -> CanonFormulaT a -> m (CanonFormulaT a)
canonAndM f lhs rhs
  | Set.null lhs = return rhs
  | Set.null rhs = return lhs
  | otherwise    = mapM (\lc -> mapM (\rc -> clauseAndM f lc rc) (Set.toList rhs) >>= return.(Set.fromList)) (Set.toList lhs) >>= return.(Set.unions)

clauseAndM :: (Monad m,Ord a) => (a -> a -> m a) -> ClauseT a -> ClauseT a -> m (ClauseT a)
clauseAndM f cll clr = do
  nvars <- unionM f (Map.toAscList (clauseVars cll)) (Map.toAscList (clauseVars clr))
  nnext <- canonAndM f (clauseNext cll) (clauseNext clr)
  nalways <- canonAndM f (clauseAlways cll) (clauseAlways clr)
  return (ClauseT
          { clauseVars = Map.fromAscList nvars
          , clauseNext = nnext
          , clauseAlways = nalways
          })

unionM :: (Monad m,Ord k) => (a -> a -> m a) -> [(k,a)] -> [(k,a)] -> m [(k,a)]
unionM f [] r = return r
unionM f l [] = return l
unionM f l@((lk,lv):ls) r@((rk,rv):rs) = case compare lk rk of
  LT -> do
    rest <- unionM f ls r
    return ((lk,lv):rest)
  GT -> do
    rest <- unionM f l rs
    return ((rk,rv):rest)
  EQ -> do
    nv <- f lv rv
    rest <- unionM f ls rs
    return ((lk,nv):rest)
  
canonAnd :: CanonFormula -> CanonFormula -> CanonFormula
canonAnd lhs rhs
  | Set.null lhs = rhs
  | Set.null rhs = lhs
  | otherwise = Set.fromList [ clauseAnd lc rc | lc <- Set.toList lhs, rc <- Set.toList rhs ]

clauseAnd :: Clause -> Clause -> Clause
clauseAnd cll clr = ClauseT
  { clauseVars = Map.unionWith (Set.union) (clauseVars cll) (clauseVars clr)
  , clauseNext = canonAnd (clauseNext cll) (clauseNext clr)
  , clauseAlways = canonAnd (clauseAlways cll) (clauseAlways clr)
  }

condition :: String -> Condition -> CanonFormula
condition n x = Set.singleton (ClauseT { clauseVars = Map.singleton n (Set.singleton x)
                                       , clauseNext = Set.empty
                                       , clauseAlways = Set.empty
                                       })

conditionNot :: Condition -> Condition
conditionNot (CondLT x) = CondGTEq x
conditionNot (CondLTEq x) = CondGT x
conditionNot (CondGT x) = CondLTEq x
conditionNot (CondGTEq x) = CondLT x
conditionNot (CondElem x) = CondNElem x
conditionNot (CondNElem x) = CondElem x

clauseNot :: Clause -> CanonFormula
clauseNot cl = (Set.fromList [ ClauseT { clauseVars = Map.singleton var (Set.singleton $ conditionNot c)
                                       , clauseNext = Set.empty
                                       , clauseAlways = Set.empty
                                       }
                             | (var,conds) <- Map.toList (clauseVars cl),
                               c <- Set.toList conds ]) `Set.union`
               (if Set.null (clauseNext cl)
                then Set.empty
                else Set.singleton $ ClauseT { clauseVars = Map.empty
                                             , clauseNext = formulaNot (clauseNext cl)
                                             , clauseAlways = Set.empty
                                             }) `Set.union`
               (if Set.null (clauseAlways cl)
                then Set.empty
                else Set.singleton $ ClauseT { clauseVars = Map.empty
                                             , clauseNext = Set.empty
                                             , clauseAlways = formulaNot (clauseAlways cl)
                                             })

formulaNot :: CanonFormula -> CanonFormula
formulaNot st 
  | Set.null st = Set.singleton $ ClauseT { clauseVars = Map.empty
                                          , clauseNext = Set.empty
                                          , clauseAlways = Set.empty
                                          }
  | otherwise = Set.unions $ fmap clauseNot (Set.toList st)

translateFormula :: Formula -> CanonFormula
translateFormula (BinLT (Variable n) (Constant x)) = condition n (CondLT x)
translateFormula (BinLT (Constant x) (Variable n)) = condition n (CondGT x)
translateFormula (BinGT (Variable n) (Constant x)) = condition n (CondGT x)
translateFormula (BinGT (Constant x) (Variable n)) = condition n (CondLT x)
translateFormula (BinEQ (Variable n) (Constant x)) = condition n (CondElem [x])
translateFormula (BinEQ (Constant x) (Variable n)) = condition n (CondElem [x])
translateFormula (Not formula) = formulaNot $ translateFormula formula
translateFormula (And lhs rhs) = let l = translateFormula lhs
                                     r = translateFormula rhs
                                 in canonAnd l r
translateFormula (Or lhs rhs) = translateFormula lhs `Set.union` translateFormula rhs
translateFormula (Always formula) = Set.singleton $ ClauseT { clauseVars = Map.empty
                                                            , clauseNext = Set.empty
                                                            , clauseAlways = translateFormula formula
                                                            }
translateFormula (Next formula) = Set.singleton $ ClauseT { clauseVars = Map.empty
                                                          , clauseNext = translateFormula formula
                                                          , clauseAlways = Set.empty
                                                          }
translateFormula (Follows lhs rhs) = let l = translateFormula (Not lhs)
                                         r = translateFormula rhs
                                     in r `Set.union` l

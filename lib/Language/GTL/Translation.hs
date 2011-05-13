{-# LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, ScopedTypeVariables #-}
{-| Translates GTL expressions into LTL formula.
 -}
module Language.GTL.Translation(
  GTLAtom(..),
  mapGTLVars,
  gtlAtomNot,
  gtlToBuchi,
  gtlsToBuchi,
  getAtomVars,
  gtlToLTL
  ) where

import Language.GTL.Expression as GTL
import Language.GTL.LTL as LTL
import Language.GTL.Buchi
import Data.Binary
import Data.Word
import Data.Typeable
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,foldl1,concat,mapM)
import Data.List (genericLength)

import Data.Set as Set
import Data.Map as Map

-- | A representation of GTL expressions that can't be further translated into LTL
--   and thus have to be used as atoms.
data GTLAtom v = GTLBoolExpr (GTL.BoolExpr v) Bool
               deriving (Eq, Ord)

instance VarType v => Show (GTLAtom v) where
  show (GTLBoolExpr e _) = show e

instance (VarType v, Binary v) => Binary (GTLAtom v) where
  put (GTLBoolExpr e n) = put e >> put n
  get = do
    e <- get
    n <- get
    return $ GTLBoolExpr e n

-- | Applies a function to every variable in the atom.
mapGTLVars :: (VarType v, VarType w) => (v -> w) -> GTLAtom v -> GTLAtom w
mapGTLVars f (GTLBoolExpr e p) = GTLBoolExpr (mapVarsBoolExpr f e) p

-- | Negate a GTL atom.
gtlAtomNot :: GTLAtom v -> GTLAtom v
gtlAtomNot (GTLBoolExpr e p) = GTLBoolExpr e (not p) -- TODO: be more intelligent as before
--gtlAtomNot (GTLElem name lits p) = GTLElem name lits (not p)
--gtlAtomNot (GTLVar n lvl v) = GTLVar n lvl (not v)

-- | Like `gtlToBuchi' but takes more than one formula.
gtlsToBuchi :: (Monad m, VarType v) => ([GTLAtom v] -> m a) -> [GTL.LogicExpr v] -> m (Buchi a)
gtlsToBuchi f = (gtlToBuchi f) . foldl1 (BinLogicExpr GTL.And)

-- | Translates a GTL expression into a buchi automaton.
--   Needs a user supplied function that converts a list of atoms that have to be
--   true into the variable type of the buchi automaton.
gtlToBuchi :: (Monad m, VarType v) => ([GTLAtom v] -> m a) -> GTL.LogicExpr v -> m (Buchi a)
gtlToBuchi f expr = mapM (\co -> do
                             nvars <- f (fmap (\(at,p) -> if p
                                                          then at
                                                          else gtlAtomNot at
                                              ) $ Set.toList (vars co))
                             return $ co { vars = nvars }
                         ) $
                    ltlToBuchi (gtlToLTL expr)

-- | Extract all variables with their history level from an atom.
getAtomVars :: VarType v => GTLAtom v -> [(v,Integer)]
getAtomVars (GTLBoolExpr e _) = getVarsBoolExpr e

-- | Translate a GTL expression into a LTL formula.
gtlToLTL :: VarType v => LogicExpr v -> LTL (GTLAtom v)
gtlToLTL (GTL.LogicTerm t) = LTL.Atom $ GTLBoolExpr t True
gtlToLTL (GTL.BinLogicExpr op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Implies -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
  GTL.Until -> LTL.Bin LTL.Until (gtlToLTL l) (gtlToLTL r)
gtlToLTL (GTL.Not x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.Always x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.Next x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.ExprAutomaton buchi) = LTL.LTLSimpleAutomaton (simpleAutomaton buchi)
--gtlToLTL (GTL.ExprAutomaton buchi) = LTL.LTLAutomaton (fmap (\co -> co { vars = gtlToLTL (vars co) }) (buchiSwitch buchi))

expandExpr :: VarType v => LogicExpr v -> [Set (GTLAtom v)]
expandExpr (GTL.LogicTerm t) = [Set.singleton (GTLBoolExpr t True)]
expandExpr (GTL.BinLogicExpr op l r) = case op of
  GTL.And -> [ Set.union lm rm | lm <- expandExpr l, rm <- expandExpr r ]
  GTL.Or -> expandExpr l ++ expandExpr r
  GTL.Implies -> expandExpr (GTL.BinLogicExpr GTL.Or (GTL.Not l) r)
  GTL.Until -> error "Can't use until in state formulas yet"
expandExpr (GTL.Not x) = expandNot (expandExpr x)
  where
    expandNot [] = [Set.empty]
    expandNot (x:xs) = let res = expandNot xs
                       in Set.fold (\at cur -> fmap (Set.insert (gtlAtomNot at)) res ++ cur) res x
expandExpr (GTL.Always x) = error "Can't use always in state formulas yet"
expandExpr (GTL.Next x) = error "Can't use next in state formulas yet"
expandExpr (GTL.ExprAutomaton buchi) = error "Can't use automata in state formulas yet"

simpleAutomaton :: VarType v => GBuchi Integer (LogicExpr v) f -> GBuchi Integer (Set (GTLAtom v)) f
simpleAutomaton buchi
  = let expandState st = [ BuchiState { isStart = isStart st
                                      , vars = nvar
                                      , finalSets = finalSets st
                                      , successors = Set.fromList $ concat [ mapping!succ | succ <- Set.toList (successors st) ]
                                      }
                         | nvar <- expandExpr (vars st) ]
        (mapping,_,res) = Map.foldrWithKey (\name co (mp,n,stmp) -> let sts = zip [n..] (expandState co)
                                                                        len = genericLength sts
                                                                    in (Map.insert name (fmap fst sts) mp,
                                                                        n+len,
                                                                        foldl (\stmp' (cn,cco) -> Map.insert cn cco stmp') stmp sts)
                                           ) (Map.empty,0,Map.empty) buchi
    in res



buchiSwitch :: Ord a => GBuchi a b f -> GBuchi a b f
buchiSwitch buchi = Map.foldrWithKey (\name co mp->
                                       foldl (\mp2 succ ->
                                               Map.adjust (\co2 -> co2 { successors = Set.insert name (successors co2) }) succ mp2
                                             ) mp (successors co))
                    (fmap (\co -> co { successors = Set.empty }) buchi) buchi

{-# LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, ScopedTypeVariables,
    TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
{-| Translates GTL expressions into LTL formula.
 -}
module Language.GTL.Translation(
  gtl2ba,
  gtlToLTL,
  expandAutomaton
  ) where

import Language.GTL.Expression as GTL
import Language.GTL.Types as GTL
import Language.GTL.LTL as LTL
import Language.GTL.Buchi
import Data.Foldable
import Prelude hiding (foldl,foldl1,concat,mapM)
import Data.Set as Set hiding (foldl)

-- | Translates a GTL expression into a buchi automaton.
--   Needs a user supplied function that converts a list of atoms that have to be
--   true into the variable type of the buchi automaton.
gtl2ba :: (Ord v,Show v) => Maybe Integer -> TypedExpr v -> BA [TypedExpr v] Integer
gtl2ba cy e = ltl2ba $ gtlToLTL cy e

getSteps :: Integer -> TimeSpec -> Integer
getSteps _ NoTime = 0
getSteps _ (TimeSteps s) = s
getSteps cy (TimeUSecs s) = s `div` cy

getUSecs :: TimeSpec -> Integer
getUSecs (TimeUSecs s) = s
getUSecs (TimeSteps n) = n
getUSecs NoTime = 0

gtlToLTL :: (Ord v,Show v) => Maybe Integer -> TypedExpr v -> LTL (TypedExpr v)
gtlToLTL cycle_time expr = fst $ gtlToLTL' 0 cycle_time expr

-- | Translate a GTL expression into a LTL formula.
gtlToLTL' :: (Ord v,Show v) => Integer -> Maybe Integer -> TypedExpr v -> (LTL (TypedExpr v),Integer)
gtlToLTL' clk cycle_time (Fix expr)
  | getType expr == gtlBool = case getValue expr of
    Var _ _ _ -> (Atom $ Fix expr,clk)
    Value (GTLBoolVal x) -> (Ground x,clk)
    BinBoolExpr op l r -> let (lhs,clk1) = gtlToLTL' clk cycle_time l
                              (rhs,clk2) = gtlToLTL' clk1 cycle_time r
                          in case op of
                            GTL.And -> (LTL.Bin LTL.And lhs rhs,clk2)
                            GTL.Or -> (LTL.Bin LTL.Or lhs rhs,clk2)
                            GTL.Implies -> (LTL.Bin LTL.Or (LTL.Un LTL.Not lhs) rhs,clk2)
                            GTL.Until NoTime -> (LTL.Bin LTL.Until lhs rhs,clk2)
                            GTL.Until ti -> case cycle_time of
                              Just rcycle_time -> (foldl (\expr _ -> LTL.Bin LTL.Or rhs (LTL.Bin LTL.And lhs (LTL.Un LTL.Next expr))) rhs [1..(getSteps rcycle_time ti)],clk2)
                              Nothing -> (LTL.Bin LTL.Or rhs (LTL.Bin LTL.And
                                                              (LTL.Bin LTL.And
                                                               (Atom (Fix $ Typed gtlBool $ ClockReset clk2 (getUSecs ti)))
                                                               lhs)
                                                              (LTL.Un LTL.Next
                                                               (LTL.Bin LTL.Until (LTL.Bin LTL.And
                                                                                   lhs
                                                                                   (Atom (Fix $ Typed gtlBool $ ClockRef clk2)))
                                                                (LTL.Bin LTL.And
                                                                 rhs
                                                                 (Atom (Fix $ Typed gtlBool $ ClockReset clk2 0))
                                                                )
                                                               )
                                                              )
                                                             ),clk2+1)
    BinRelExpr rel lhs rhs -> case fmap Atom $ flattenRel rel lhs rhs of
      [e] -> (e,clk)
      es -> (foldl1 (LTL.Bin LTL.And) es,clk)
    UnBoolExpr op p -> let (arg,clk1) = gtlToLTL' clk cycle_time p
                       in case op of
                         GTL.Not -> (LTL.Un LTL.Not arg,clk1)
                         GTL.Always -> (LTL.Bin LTL.UntilOp (LTL.Ground False) arg,clk1)
                         GTL.Next NoTime -> (LTL.Un LTL.Next arg,clk1)
                         GTL.Next ti -> case cycle_time of
                           Just rcycle_time -> (foldl (\expr _ -> LTL.Bin LTL.And arg (LTL.Un LTL.Next expr)) arg [2..(getSteps rcycle_time ti)],clk1)
                         GTL.Finally NoTime -> (LTL.Bin LTL.Until (LTL.Ground True) arg,clk1)
                         GTL.Finally ti -> case cycle_time of
                           Just rcycle_time -> (foldl (\expr _ -> LTL.Bin LTL.Or arg (LTL.Un LTL.Next expr)) arg [2..(getSteps rcycle_time ti)],clk1)
                           Nothing -> gtlToLTL' clk cycle_time (Fix $ Typed gtlBool $ BinBoolExpr (GTL.Until ti) (Fix $ Typed gtlBool (Value (GTLBoolVal True))) p)
                         GTL.After ti -> case cycle_time of
                           Just rcycle_time -> (foldl (\expr _ -> LTL.Un LTL.Next expr) arg [1..(getSteps rcycle_time ti)],clk1)
                           Nothing
                             | getUSecs ti == 0 -> (arg,clk1)
                             | otherwise -> (LTL.Bin LTL.And
                                             (Atom $ Fix $ Typed gtlBool $ ClockReset clk1 (getUSecs ti))
                                             (LTL.Un LTL.Next
                                              ((LTL.Bin LTL.Until
                                                (LTL.Ground True)
                                                (LTL.Bin LTL.And
                                                 (LTL.Un LTL.Not (Atom $ Fix $ Typed gtlBool $ ClockRef clk1))
                                                 arg)))),clk1+1)
    IndexExpr _ _ -> (Atom (Fix expr),clk)
    Automaton buchi -> (LTLAutomaton (renameStates $ optimizeTransitionsBA $ minimizeBA $ expandAutomaton $ renameStates buchi),clk)
    BuiltIn "equal" args@(x:xs) -> case unfix $ getType (unfix x) of
      GTLBool -> let (clk1,tt) = foldl (\(cclk,cres) arg -> let (nres,nclk) = gtlToLTL' cclk cycle_time arg in (nclk,nres:cres)) (clk,[]) args
                     (clk2,ff) = foldl (\(cclk,cres) arg -> let (nres,nclk) = gtlToLTL' cclk cycle_time (distributeNot arg) in (nclk,nres:cres)) (clk1,[]) args
                 in (LTL.Bin LTL.Or (foldl1 (LTL.Bin LTL.And) tt) (foldl1 (LTL.Bin LTL.And) ff),clk2)
  | otherwise = error "Internal error: Non-bool expression passed to gtlToLTL"
    where
      flattenRel :: Relation -> TypedExpr v -> TypedExpr v -> [TypedExpr v]
      flattenRel rel (Fix lhs) (Fix rhs) = case (getValue lhs,getValue rhs) of
        (Value (GTLArrayVal xs),Value (GTLArrayVal ys)) -> zipWith (\x y -> Fix $ Typed gtlBool (BinRelExpr rel x y)) xs ys
        (Value (GTLArrayVal xs),_) -> zipWith (\x i -> Fix $ Typed gtlBool (BinRelExpr rel x (Fix $ Typed (getType $ unfix x) (IndexExpr (Fix rhs) i)))) xs [0..]
        (_,Value (GTLArrayVal ys)) -> zipWith (\i y -> Fix $ Typed gtlBool (BinRelExpr rel (Fix $ Typed (getType $ unfix y) (IndexExpr (Fix lhs) i)) y)) [0..] ys
        (Value (GTLTupleVal xs),Value (GTLTupleVal ys)) -> zipWith (\x y -> Fix $ Typed gtlBool (BinRelExpr rel x y)) xs ys
        (Value (GTLTupleVal xs),_) -> zipWith (\x i -> Fix $ Typed gtlBool (BinRelExpr rel x (Fix $ Typed (getType $ unfix x) (IndexExpr (Fix rhs) i)))) xs [0..]
        (_,Value (GTLTupleVal ys)) -> zipWith (\i y -> Fix $ Typed gtlBool (BinRelExpr rel (Fix $ Typed (getType $ unfix y) (IndexExpr (Fix lhs) i)) y)) [0..] ys
        _ -> [Fix $ Typed gtlBool (BinRelExpr rel (Fix lhs) (Fix rhs))]

expandAutomaton :: (Ord t,Ord v,Show v) => BA [TypedExpr v] t -> BA [TypedExpr v] t
expandAutomaton ba = ba { baTransitions = fmap (\ts -> [ (Set.toList cond,trg)
                                                       | (cs,trg) <- ts,
                                                         let cs_expr = case cs of
                                                               [] -> Fix $ Typed gtlBool (Value (GTLBoolVal True))
                                                               [c] -> c
                                                               _ -> foldl1 (\x y -> Fix $ Typed gtlBool (BinBoolExpr GTL.And x y)) cs,
                                                         cond <- expandExpr cs_expr
                                                       ]) (baTransitions ba) }

expandExpr :: (Ord v,Show v) => TypedExpr v -> [Set (TypedExpr v)]
expandExpr expr
  | baseType (getType $ unfix expr) == gtlBool = case getValue (unfix expr) of
    Var _ _ _ -> [Set.singleton expr]
    Value (GTLBoolVal False) -> []
    Value (GTLBoolVal True) -> [Set.empty]
    Value _ -> error "No non-boolean expression allowed in state formulas (should not get here"
    BinBoolExpr op l r -> case op of
      GTL.And -> [ Set.union lm rm | lm <- expandExpr l, rm <- expandExpr r ]
      GTL.Or -> expandExpr l ++ expandExpr r
      GTL.Implies -> expandExpr (Fix $ Typed gtlBool (BinBoolExpr GTL.Or (Fix $ Typed gtlBool (UnBoolExpr GTL.Not l)) r))
      GTL.Until _ -> error "Can't use until in state formulas yet"
      GTL.UntilOp _ -> error "Can't use untilop in state formulas yet"
    BinRelExpr _ _ _ -> [Set.singleton expr]
    BinIntExpr _ _ _ -> error "Can't use binary int expr in state formulas yet"
    UnBoolExpr op p -> case op of
      GTL.Not -> let expandNot [] = [Set.empty]
                     expandNot (x:xs) = let res = expandNot xs
                                        in [ Set.insert (distributeNot at) el | el <- res, at <- Set.toList x ]
                 in expandNot (expandExpr p)
      GTL.Next _ -> error "Can't use next in state formulas yet"
      GTL.Always -> error "Can't use always in state formulas yet"
      GTL.Finally _ -> error "Can't use finally in state formulas yet"
      GTL.After _ -> error "Can't use after in state formulas yet"
    IndexExpr _ _ -> [Set.singleton expr]
    Automaton _ -> error "Can't use automata in state formulas yet"
    ClockReset _ _ -> error "Can't use clock reset in state formulas yet"
    ClockRef _ -> error "Can't use clock ref in state formulas yet"
    BuiltIn _ _ -> error "Can't use builtin in state formulas yet"
  | otherwise = error $ "Passed non-boolean ("++show (getType $ unfix expr)++") expression "++show expr++" as state formula"

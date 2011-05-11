{-# LANGUAGE GADTs #-}
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
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,foldl1,concat,mapM)
import Data.List (genericLength)

import Data.Set as Set
import Data.Map as Map

-- | A representation of GTL expressions that can't be further translated into LTL
--   and thus have to be used as atoms.
data GTLAtom v = GTLRel GTL.Relation (GTL.Expr v Int) (GTL.Expr v Int)
               | GTLElem v [Integer] Bool
               | GTLVar v Integer Bool
               deriving (Eq,Ord)

instance Show v => Show (GTLAtom v) where
  show (GTLRel rel lhs rhs) = show lhs ++ " " ++ show rel ++ " " ++ show rhs
  show (GTLElem var vals t) = show var ++ (if t then "" else " not")++" in "++show vals
  show (GTLVar var hist t) = show var ++ (if hist==0 then "" else "["++show hist++"]")

instance Binary v => Binary (GTLAtom v) where
  put (GTLRel rel lhs rhs) = put (0::Word8) >> put rel >> put lhs >> put rhs
  put (GTLElem v vals b) = put (1::Word8) >> put v >> put vals >> put b
  put (GTLVar v h b) = put (2::Word8) >> put v >> put h >> put b
  get = do
    i <- get :: Get Word8
    case i of
      0 -> do
        rel <- get
        lhs <- get
        rhs <- get
        return $ GTLRel rel lhs rhs
      1 -> do
        v <- get
        vals <- get
        b <- get
        return $ GTLElem v vals b
      2 -> do
        v <- get
        h <- get
        b <- get
        return $ GTLVar v h b

-- | Applies a function to every variable in the atom.
mapGTLVars :: (v -> w) -> GTLAtom v -> GTLAtom w
mapGTLVars f (GTLRel rel lhs rhs) = GTLRel rel (mapVars f lhs) (mapVars f rhs)
mapGTLVars f (GTLElem v vals b) = GTLElem (f v) vals b
mapGTLVars f (GTLVar v i b) = GTLVar (f v) i b

-- | Negate a GTL atom.
gtlAtomNot :: GTLAtom v -> GTLAtom v
gtlAtomNot (GTLRel rel l r) = GTLRel (relNot rel) l r
gtlAtomNot (GTLElem name lits p) = GTLElem name lits (not p)
gtlAtomNot (GTLVar n lvl v) = GTLVar n lvl (not v)

-- | Like `gtlToBuchi' but takes more than one formula.
gtlsToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> [GTL.Expr v Bool] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (ExprBinBool GTL.And)

-- | Translates a GTL expression into a buchi automaton.
--   Needs a user supplied function that converts a list of atoms that have to be
--   true into the variable type of the buchi automaton.
gtlToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> GTL.Expr v Bool -> m (Buchi a)
gtlToBuchi f expr = mapM (\co -> do
                             nvars <- f (fmap (\(at,p) -> if p 
                                                          then at
                                                          else gtlAtomNot at
                                              ) $ Set.toList (vars co))
                             return $ co { vars = nvars }
                         ) $
                    ltlToBuchi (gtlToLTL expr)

-- | Extract all variables with their history level from an atom.
getAtomVars :: GTLAtom v -> [(v,Integer)]
getAtomVars (GTLElem n _ _) = [(n,0)]
getAtomVars (GTLRel _ lhs rhs) = getVars lhs ++ getVars rhs
getAtomVars (GTLVar n h _) = [(n,h)]

-- | Translate a GTL expression into a LTL formula.
gtlToLTL :: Ord v => Expr v Bool -> LTL (GTLAtom v)
gtlToLTL (GTL.ExprRel rel l r) = LTL.Atom $ GTLRel rel l r
gtlToLTL (GTL.ExprBinBool op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Implies -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
  GTL.Until -> LTL.Bin LTL.Until (gtlToLTL l) (gtlToLTL r)
gtlToLTL (GTL.ExprNot x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.ExprAlways x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.ExprNext x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.ExprElem v lits p) = LTL.Atom $ GTLElem v lits p
gtlToLTL (GTL.ExprVar n lvl) = LTL.Atom $ GTLVar n lvl True
gtlToLTL (GTL.ExprAutomaton buchi) = LTL.LTLSimpleAutomaton (simpleAutomaton buchi)
gtlToLTL (GTL.ExprConst c) = LTL.Ground c
--gtlToLTL (GTL.ExprAutomaton buchi) = LTL.LTLAutomaton (fmap (\co -> co { vars = gtlToLTL (vars co) }) (buchiSwitch buchi))

expandExpr :: Ord v => Expr v Bool -> [Set (GTLAtom v)]
expandExpr (GTL.ExprRel rel l r) = [Set.singleton (GTLRel rel l r)]
expandExpr (GTL.ExprBinBool op l r) = case op of
  GTL.And -> [ Set.union lm rm | lm <- expandExpr l, rm <- expandExpr r ]
  GTL.Or -> expandExpr l ++ expandExpr r
  GTL.Implies -> expandExpr (GTL.ExprBinBool GTL.Or (GTL.ExprNot l) r)
  GTL.Until -> error "Can't use until in state formulas yet"
expandExpr (GTL.ExprNot x) = expandNot (expandExpr x)
  where
    expandNot [] = [Set.empty]
    expandNot (x:xs) = let res = expandNot xs
                       in Set.fold (\at cur -> fmap (Set.insert (gtlAtomNot at)) res ++ cur) res x
expandExpr (GTL.ExprAlways x) = error "Can't use always in state formulas yet"
expandExpr (GTL.ExprNext x) = error "Can't use next in state formulas yet"
expandExpr (GTL.ExprElem v lits p) = [Set.singleton (GTLElem v lits p)]
expandExpr (GTL.ExprVar n lvl) = [Set.singleton (GTLVar n lvl True)]
expandExpr (GTL.ExprAutomaton buchi) = error "Can't use automata in state formulas yet"

simpleAutomaton :: Ord v => GBuchi Integer (Expr v Bool) f -> GBuchi Integer (Set (GTLAtom v)) f
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
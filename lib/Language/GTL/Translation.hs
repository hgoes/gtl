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
import Data.Binary
import Data.Word
import Data.Typeable

import Data.Set as Set

-- | A representation of GTL expressions that can't be further translated into LTL
--   and thus have to be used as atoms.
data GTLAtom v = forall t. (Eq v, Show t, Eq t, Ord t, Typeable t, Binary t) => GTLRel GTL.Relation (GTL.EqualExpr v t)
               | GTLElem v [Integer] Bool
               | GTLVar v Integer Bool

instance Show v => Show (GTLAtom v) where
  show (GTLRel rel (GTL.EqualExpr lhs rhs)) = show lhs ++ " " ++ show rel ++ " " ++ show rhs
  show (GTLElem var vals t) = show var ++ (if t then "" else " not")++" in "++show vals
  show (GTLVar var hist t) = show var ++ (if hist==0 then "" else "["++show hist++"]")

instance Eq v => Eq (GTLAtom v) where
  (==) (GTLRel a1 a2) (GTLRel b1 b2) = (((a1 == b1)) && (castEqual a2 b2))
  (==) (GTLElem a1 a2 a3) (GTLElem b1 b2 b3)
           = ((((a1 == b1)) && ((a2 == b2))) && ((a3 == b3)))
  (==) (GTLVar a1 a2 a3) (GTLVar b1 b2 b3)
           = ((((a1 == b1)) && ((a2 == b2))) && ((a3 == b3)))
  (==) _ _ = False

instance Ord v => Ord (GTLAtom v) where
  compare (GTLRel a1 a2) (GTLRel b1 b2) =
    case compare a1 b1 of
      EQ -> castCompare a2 b2
      r -> r
  compare (GTLElem a1 a2 a3) (GTLElem b1 b2 b3) =
    case compare a1 b1 of
      EQ -> case compare a2 b2 of
        EQ -> compare a3 b3
        r -> r
      r -> r
  compare (GTLVar a1 a2 a3) (GTLVar b1 b2 b3) =
    case compare a1 b1 of
      EQ -> case compare a2 b2 of
        EQ -> compare a3 b3
        r -> r
      r -> r
  compare _ _ = LT

instance (VarType v, Binary v) => Binary (GTLAtom v) where
  put (GTLRel rel (GTL.EqualExpr lhs rhs)) = put (0::Word8) >> put rel >> put lhs >> put rhs
  put (GTLElem v vals b) = put (1::Word8) >> put v >> put vals >> put b
  put (GTLVar v h b) = put (2::Word8) >> put v >> put h >> put b
  get = do
    i <- get :: Get Word8
    case i of
      0 -> do
        rel <- get
        lhs :: (GTL.Expr v Int) <- error "Not implemented" -- get TODO
        rhs :: (GTL.Expr v Int) <- get
        return $ GTLRel rel (GTL.EqualExpr lhs rhs)
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
mapGTLVars :: (VarType w, Binary w) => (v -> w) -> GTLAtom v -> GTLAtom w
mapGTLVars f (GTLRel rel (GTL.EqualExpr lhs rhs)) = GTLRel rel (GTL.EqualExpr (mapVars f lhs) (mapVars f rhs))
mapGTLVars f (GTLElem v vals b) = GTLElem (f v) vals b
mapGTLVars f (GTLVar v i b) = GTLVar (f v) i b

-- | Negate a GTL atom.
gtlAtomNot :: GTLAtom v -> GTLAtom v
gtlAtomNot (GTLRel rel (GTL.EqualExpr l r)) = GTLRel (relNot rel) (GTL.EqualExpr l r)
gtlAtomNot (GTLElem name lits p) = GTLElem name lits (not p)
gtlAtomNot (GTLVar n lvl v) = GTLVar n lvl (not v)

-- | Like `gtlToBuchi' but takes more than one formula.
gtlsToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> [GTL.Expr v Bool] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (ExprBinBool GTL.And)

-- | Translates a GTL expression into a buchi automaton.
--   Needs a user supplied function that converts a list of atoms that have to be
--   true into the variable type of the buchi automaton.
gtlToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> GTL.Expr v Bool -> m (Buchi a)
gtlToBuchi f = ltlToBuchiM (f . fmap (\(at,p) -> if p
                                                 then at
                                                 else gtlAtomNot at)
                           ) .
             gtlToLTL

-- | Extract all variables with their history level from an atom.
getAtomVars :: GTLAtom v -> [(v,Integer)]
getAtomVars (GTLElem n _ _) = [(n,0)]
getAtomVars (GTLRel _ (GTL.EqualExpr lhs rhs)) = getVars lhs ++ getVars rhs
getAtomVars (GTLVar n h _) = [(n,h)]

-- | Translate a GTL expression into a LTL formula.
gtlToLTL :: Expr v Bool -> LTL (GTLAtom v)
gtlToLTL (GTL.ExprRel rel (GTL.EqualExpr l r)) = LTL.Atom (GTLRel rel (GTL.EqualExpr l r))
gtlToLTL (GTL.ExprBinBool op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Implies -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
gtlToLTL (GTL.ExprNot x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.ExprAlways x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.ExprNext x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.ExprElem v lits p) = LTL.Atom (GTLElem v lits p)
gtlToLTL (GTL.ExprVar n lvl) = LTL.Atom (GTLVar n lvl True)

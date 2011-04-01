{-# LANGUAGE GADTs #-}
module Language.GTL.Translation where

import Language.GTL.Syntax as GTL
import Language.GTL.LTL as LTL
import Data.Binary
import Data.Word

import Data.Set as Set

data GTLAtom v = GTLRel GTL.Relation (GTL.Expr v Int) (GTL.Expr v Int)
               | GTLElem v [Integer] Bool
               | GTLVar v Integer Bool
               deriving (Show,Eq,Ord)

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

mapGTLVars :: (v -> w) -> GTLAtom v -> GTLAtom w
mapGTLVars f (GTLRel rel lhs rhs) = GTLRel rel (mapVars f lhs) (mapVars f rhs)
mapGTLVars f (GTLElem v vals b) = GTLElem (f v) vals b
mapGTLVars f (GTLVar v i b) = GTLVar (f v) i b

gtlAtomNot :: GTLAtom v -> GTLAtom v
gtlAtomNot (GTLRel rel l r) = GTLRel (relNot rel) l r
gtlAtomNot (GTLElem name lits p) = GTLElem name lits (not p)
gtlAtomNot (GTLVar n lvl v) = GTLVar n lvl (not v)

gtlsToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> [GTL.Expr v Bool] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (ExprBinBool GTL.And)

gtlToBuchi :: (Monad m,Ord v,Show v) => ([GTLAtom v] -> m a) -> GTL.Expr v Bool -> m (Buchi a)
gtlToBuchi f = ltlToBuchiM (f . fmap (\(at,p) -> if p
                                                 then at
                                                 else gtlAtomNot at)
                           ) .
             gtlToLTL

getAtomVars :: GTLAtom v -> [(v,Integer)]
getAtomVars (GTLElem n _ _) = [(n,0)]
getAtomVars (GTLRel _ lhs rhs) = getVars lhs ++ getVars rhs
getAtomVars (GTLVar n h _) = [(n,h)]

gtlToLTL :: Expr v Bool -> LTL (GTLAtom v)
gtlToLTL (GTL.ExprRel rel l r) = LTL.Atom (GTLRel rel l r)
gtlToLTL (GTL.ExprBinBool op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Implies -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
gtlToLTL (GTL.ExprNot x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.ExprAlways x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.ExprNext x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.ExprElem v lits p) = LTL.Atom (GTLElem v lits p)
gtlToLTL (GTL.ExprVar n lvl) = LTL.Atom (GTLVar n lvl True)
{-# LANGUAGE GADTs #-}
module Language.GTL.Translation where

import Language.GTL.Syntax as GTL
import Language.GTL.LTL as LTL

import Data.Set as Set

data GTLAtom = GTLRel GTL.Relation (GTL.Expr Int) (GTL.Expr Int)
             | GTLElem (Maybe String) String [Integer] Bool
             | GTLVar (Maybe String) String Integer Bool
             deriving (Show,Eq,Ord)

gtlAtomNot :: GTLAtom -> GTLAtom
gtlAtomNot (GTLRel rel l r) = GTLRel (relNot rel) l r
gtlAtomNot (GTLElem q name lits p) = GTLElem q name lits (not p)
gtlAtomNot (GTLVar q n lvl v) = GTLVar q n lvl (not v)

gtlsToBuchi :: Monad m => ([GTLAtom] -> m a) -> [Formula] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (ExprBinBool GTL.And)

gtlToBuchi :: Monad m => ([GTLAtom] -> m a) -> Formula -> m (Buchi a)
gtlToBuchi f = ltlToBuchiM (f . fmap (\(at,p) -> if p
                                                 then at
                                                 else gtlAtomNot at)
                           ) .
             gtlToLTL

getAtomVars :: GTLAtom -> [(Maybe String,String,Integer)]
getAtomVars (GTLElem q n _ _) = [(q,n,0)]
getAtomVars (GTLRel _ lhs rhs) = getVars lhs ++ getVars rhs

gtlToLTL :: Formula -> LTL GTLAtom
gtlToLTL (GTL.ExprRel rel l r) = LTL.Atom (GTLRel rel l r)
gtlToLTL (GTL.ExprBinBool op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Follows -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
gtlToLTL (GTL.ExprNot x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.ExprAlways x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.ExprNext x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.ExprElem q v lits p) = LTL.Atom (GTLElem q v lits p)
gtlToLTL (GTL.ExprVar q n lvl) = LTL.Atom (GTLVar q n lvl True)
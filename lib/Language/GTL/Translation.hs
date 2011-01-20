module Language.GTL.Translation where

import Language.GTL.Syntax as GTL
import Language.GTL.LTL as LTL

import Data.Set as Set

data GTLAtom = GTLRel GTL.Relation GTL.Lit GTL.Lit
             | GTLElem String [GTL.Lit] Bool
             deriving (Show,Eq,Ord)

gtlAtomNot :: GTLAtom -> GTLAtom
gtlAtomNot (GTLRel rel l r) = GTLRel (relNot rel) l r
gtlAtomNot (GTLElem name lits p) = GTLElem name lits (not p)

gtlsToBuchi :: Monad m => ([GTLAtom] -> m a) -> [Formula] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (BinOp GTL.And)

gtlToBuchi :: Monad m => ([GTLAtom] -> m a) -> Formula -> m (Buchi a)
gtlToBuchi f = ltlToBuchiM (f . fmap (\(at,p) -> if p
                                                 then at
                                                 else gtlAtomNot at)
                           ) .
             gtlToLTL

gtlToLTL :: Formula -> LTL GTLAtom
gtlToLTL (GTL.BinRel rel l r) = LTL.Atom (GTLRel rel l r)
gtlToLTL (GTL.BinOp op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Follows -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
gtlToLTL (GTL.Not x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.Always x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.Next x) = LTL.Un LTL.Next (gtlToLTL x)
gtlToLTL (GTL.Elem v lits p) = LTL.Atom (GTLElem v lits p)
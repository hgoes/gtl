module Language.GTL.Translation where

import Language.GTL.Syntax as GTL
import Language.GTL.LTL as LTL

import Data.Set as Set

gtlsToBuchi :: Monad m => ([(GTL.Relation,GTL.Lit,GTL.Lit)] -> m a) -> [Formula] -> m (Buchi a)
gtlsToBuchi f = gtlToBuchi f . foldl1 (BinOp GTL.And)

gtlToBuchi :: Monad m => ([(GTL.Relation,GTL.Lit,GTL.Lit)] -> m a) -> Formula -> m (Buchi a)
gtlToBuchi f = ltlToBuchiM (f . fmap (\((rel,l,r),p) -> (if p
                                                         then rel
                                                         else relNot rel,l,r))
                           ) .
             gtlToLTL

gtlToLTL :: Formula -> LTL (GTL.Relation,GTL.Lit,GTL.Lit)
gtlToLTL (GTL.BinRel rel l r) = LTL.Atom (rel,l,r)
gtlToLTL (GTL.BinOp op l r) = case op of
  GTL.And -> LTL.Bin LTL.And (gtlToLTL l) (gtlToLTL r)
  GTL.Or -> LTL.Bin LTL.Or (gtlToLTL l) (gtlToLTL r)
  GTL.Follows -> LTL.Bin LTL.Or (LTL.Un LTL.Not (gtlToLTL l)) (gtlToLTL r)
gtlToLTL (GTL.Not x) = LTL.Un LTL.Not (gtlToLTL x)
gtlToLTL (GTL.Always x) = LTL.Bin LTL.UntilOp (LTL.Ground False) (gtlToLTL x)
gtlToLTL (GTL.Next x) = LTL.Un LTL.Next (gtlToLTL x)
{-# LANGUAGE MultiParamTypeClasses,FunctionalDependencies,FlexibleInstances #-}
module Data.AtomContainer
       (AtomContainer(..)
       ,ExprOrdering(..))
       where

import Data.Map as Map

-- | Represents data structures which can store atomic expressions
class Ord b => AtomContainer a b | a -> b where
  atomsTrue :: a -- ^ The container representing all possible values
  atomSingleton :: Bool -> b -> a -- ^ A container containing just a single restriction on the values.
  compareAtoms :: a -> a -> ExprOrdering -- ^ Compare the value spaces defined by the containers
  mergeAtoms :: a -> a -> Maybe a -- ^ Merge the containers together, resulting in a container which represents the intersection between the two.

-- | Represents the relations in which two expressions can stand
data ExprOrdering = EEQ -- ^ Both expressions define the same value space
                  | ENEQ -- ^ The expressions define non-overlapping value spaces
                  | EGT -- ^ The value space of the second expression is contained by the first
                  | ELT -- ^ The value space of the first expression is contained by the second
                  | EUNK -- ^ The expressions have overlapping value spaces or the relation isn't known
                  deriving (Show,Eq,Ord)

instance Ord a => AtomContainer (Map a Bool) a where
  atomsTrue = Map.empty
  atomSingleton t p = Map.singleton p t
  compareAtoms x y
    | x == y = EEQ
    | Map.isSubmapOf x y = EGT
    | Map.isSubmapOf y x = ELT
    | otherwise = ENEQ
  mergeAtoms = mergeAlphabet

mergeAlphabet :: Ord a => Map a Bool -> Map a Bool -> Maybe (Map a Bool)
mergeAlphabet a1 a2
  = if confl
    then Nothing
    else Just nmp
      where (confl,nmp) = Map.mapAccum (\hasC (x,y) -> (hasC || x/=y,x)) False $ Map.unionWith (\(x1,_) (y1,_) -> (x1,y1))
                          (fmap (\x -> (x,x)) a1)
                          (fmap (\x -> (x,x)) a2)

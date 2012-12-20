{-# LANGUAGE FlexibleContexts,FlexibleInstances,KindSignatures #-}
{- | Implements the fixpoint construction for data types.
     Allows non-recursive data types to be made into recursive ones. -}
module Data.Fix where

import Data.Binary

-- | A fixpoint data structure.
--   Allows the construction of infinite data types from finite constructors.
data Fix f = Fix { unfix :: f (Fix f) }

-- | A helper class to allow the fixpoint of a data-type to be an instance of the 'Binary' class.
class Binary2 (a :: * -> *) where
  get2 :: Binary b => Get (a b)
  put2 :: Binary b => a b -> Put

instance Binary2 a => Binary (Fix a) where
  get = fmap Fix get2
  put = put2 . unfix

-- | A helper class to allow the fixpoint of a data-type to be an instance of the 'Eq' class.
class Eq2 (a :: * -> *) where
  eq2 :: Eq b => a b -> a b -> Bool

instance Eq2 a => Eq (Fix a) where
  x == y = eq2 (unfix x) (unfix y)

-- | A helper class to allow the fixpoint of a data-type to be an instance of the 'Show' class.
class Show2 (a :: * -> *) where
  showsPrec2 :: Show b => Int -> a b -> ShowS
  showsPrec2 _ x str = show2 x ++ str
  show2 :: Show b => a b -> String
  show2 x = showsPrec2 0 x ""

instance Show2 a => Show (Fix a) where
  show x = show2 (unfix x)

-- | A helper class to allow the fixpoint of a data-type to be an instance of the 'Ord' class.
class Eq2 a => Ord2 (a :: * -> *) where
  compare2 :: Ord b => a b -> a b -> Ordering

instance Ord2 a => Ord (Fix a) where
  compare x y = compare2 (unfix x) (unfix y)

--instance (Binary (a b)) => Binary (Fix a) where
--  get = undefined
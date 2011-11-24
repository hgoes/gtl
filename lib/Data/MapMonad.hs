module Data.MapMonad where

import Data.Map as Map

unionWithKeyM :: (Monad m, Ord k) => (k -> a -> a -> m a) -> Map k a -> Map k a -> m (Map k a)
unionWithKeyM f m1 = Map.foldlWithKey merge (return m1)
  where merge mM k x = do
          m <- mM
          case Map.lookup k m of
            Nothing -> return (Map.insert k x m)
            Just x' -> f k x' x >>= \x'' -> return (Map.insert k x' m)

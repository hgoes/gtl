{-# LANGUAGE ExistentialQuantification, FlexibleInstances #-}

module Language.GTL.BuchiHistory where

import Data.Set as Set
import Data.Map as Map

class HistoryState a where
  showState :: a -> String

instance HistoryState Integer where
  showState = show

instance HistoryState Int where
  showState = show

instance HistoryState [Char] where
  showState s = "%" ++ s ++ "%"

instance (HistoryState a, HistoryState b) => HistoryState (a,b,Bool) where
  showState (a,b,c) = "(" ++ showState a ++ "," ++ showState b ++ "," ++ show c ++ ")"

instance (HistoryState a, HistoryState b) => HistoryState (a,b) where
  showState (a,b) = "(" ++ showState a ++ "," ++ showState b ++ ")"

instance HistoryState a => HistoryState (Set a) where
  showState s
    | Set.null s = "{}"
    | otherwise =
      let l = Set.toAscList s
          str = foldl (\str s' -> str ++ "," ++ showState s') (showState $ head l) (tail l)
      in "{" ++ str ++ "}"

data BAHistory =
  NoHistory
  | Product BAHistory BAHistory
  | forall a. (HistoryState a) => Rename (Map a Integer) BAHistory

showStateMap m
  | Map.null m = "{}"
  | otherwise =
    let m' = Map.toAscList m
        showMapping (s,s') = showState s ++ " -> " ++ showState s'
        str = foldl (\str f -> str ++ ", " ++ showMapping f) (showMapping $ head m') (tail m')
    in "{" ++ str ++ "}"

showBaHistory NoHistory = "none"
showBaHistory (Product l r) = "product(" ++ (showBaHistory l) ++ ", " ++ (showBaHistory r) ++ ")"
showBaHistory (Rename m h) = "rename(" ++ (showBaHistory h) ++ ", " ++ (showStateMap m) ++ ")"

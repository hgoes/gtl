{-| This module contains b&#xFC;chi automata as well as related automata data
    structures. They all closely resemble the data structures described in the
    paper "Fast LTL to B&#xFC;chi Automata Translation" by Gastin and Oddoux. -}
module Language.GTL.Buchi where

import Data.Map as Map
import Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,concat)
import Data.Binary
import qualified Data.List as List

{-| A very weak alternating automaton.
    It is used as the first step in translating LTL to B&#xFC;chi automata. -}
data VWAA a st = VWAA { vwaaTransitions :: Map st (Set (a,Set st)) -- ^ A map of states to transitions
                      , vwaaInits :: Set (Set st) -- ^ A set of initialization states
                      , vwaaCoFinals :: Set st -- ^ A set of cofinal states
                      } deriving (Eq,Ord)

{-| A generalized B&#xFC;chi automaton.
    VWAAs get translated into this. -}
data GBA a st = GBA { gbaTransitions :: Map (Set st) (Set (a,Set st,Set st))
                    , gbaInits :: Set (Set st)
                    } deriving (Eq,Ord)

{-| A classical B&#xFC;chi automaton.
    This is the target data structure for the LTL translation algorithm. -}
data BA a st = BA { baTransitions :: Map st (Set (a,st))
                  , baInits :: Set st
                  , baFinals :: Set st
                  } deriving (Eq,Ord)

instance (Binary a,Binary st,Ord a,Ord st) => Binary (BA a st) where
  put ba = do
    put (baTransitions ba)
    put (baInits ba)
    put (baFinals ba)
  get = do
    trans <- get
    inits <- get
    fins <- get
    return $ BA trans inits fins

instance (Show a,Show st,Ord st) => Show (BA a st) where
  show ba = unlines $ concat [ [(if Set.member st (baInits ba)
                                 then "initial "
                                 else "") ++ (if Set.member st (baFinals ba)
                                              then "final "
                                              else "")++
                                "state "++show st]++
                               [ "  "++show cond++" -> "++show trg | (cond,trg) <- Set.toList trans ]
                             | (st,trans) <- Map.toList $ baTransitions ba ]

instance (Show a,Show st,Ord st) => Show (VWAA a st) where
  show vwaa = unlines $ (concat [ [(if Set.member st (vwaaCoFinals vwaa)
                                    then "cofinal "
                                    else "") ++ "state "++show st]
                                  ++ [ "  "++show cond++" -> "++(show $ Set.toList trg) | (cond,trg) <- Set.toList trans ]
                                | (st,trans) <- Map.toList $ vwaaTransitions vwaa ])++
              ["inits: "++concat (List.intersperse ", " [ show (Set.toList f) | f <- Set.toList $ vwaaInits vwaa ])]

instance (Show a,Show st,Ord st) => Show (GBA a st) where
  show gba = unlines $ (concat [ [ (if Set.member st (gbaInits gba)
                                    then "initial "
                                    else "")++"state "++show st ] ++
                                 [ "  "++show cond++" ->"++show (Set.toList fins)++" "++show (Set.toList trg) | (cond,trg,fins) <- Set.toList trans ]
                               | (st,trans) <- Map.toList (gbaTransitions gba) ])

class BAState st where
  -- | Generates a new state which isn't in use, yet.
  unusedBAState :: BA a st -> st

instance BAState Integer where
  unusedBAState ba = (fst $ Map.findMax $ baTransitions ba) + 1

-- | Maps over the transition conditions of a B&#xFC;chi automaton.
baMapAlphabet :: (Ord a,Ord b,Ord st) => (a -> b) -> BA a st -> BA b st
baMapAlphabet f ba = ba { baTransitions = fmap (Set.map (\(c,trg) -> (f c,trg))) (baTransitions ba) }

-- | Enumerates all states starting from 0 thus reducing the space needed to store the automaton.
renameStates :: Ord st => BA a st -> BA a Integer
renameStates ba = let (_,stmp) = Map.mapAccum (\i _ -> (i+1,i)) 0 (baTransitions ba)
                      trans' = fmap (\trg -> Set.mapMonotonic (\(c,t) -> (c,stmp!t)) trg) $ Map.mapKeysMonotonic (\k -> stmp!k) (baTransitions ba)
                      inits' = Set.mapMonotonic (stmp!) (baInits ba)
                      fins' = Set.mapMonotonic (stmp!) (baFinals ba)
                  in BA { baTransitions = trans'
                        , baInits = inits'
                        , baFinals = fins'
                        }

removeDeadlocks :: (Ord a,Ord st) => BA a st -> BA a st
removeDeadlocks ba
  = let (rem,keep) = Map.partition Set.null (baTransitions ba)
        loop rem mp
          | Map.null rem = mp
          | otherwise = let (rem',mp') = Map.mapEither (\trans -> let ntrans = Set.filter (\(_,st) -> not $ Map.member st rem) trans
                                                                  in if Set.null ntrans
                                                                     then Left ntrans
                                                                     else Right ntrans
                                                       ) mp
                        in loop rem' mp'
        ntrans = loop rem keep
    in BA { baTransitions = ntrans
          , baInits = Set.intersection (baInits ba) (Map.keysSet ntrans)
          , baFinals = Set.intersection (baFinals ba) (Map.keysSet ntrans)
          }

{- Farewell, all joys! Oh death, come close mine eyes!
   More geese than swans now live, more fools than wise.

                                        -- Orlando Gibbons -}

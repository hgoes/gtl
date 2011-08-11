module Language.GTL.DEA (
    DEA(..), determinizeBA
  )
  where

import Prelude hiding (foldl)
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Data.Foldable (foldl)
import Language.GTL.Buchi

{-| Not a real DEA. Has no final states as they are not needed (the acceptance condition
    of the Buchi automaton can not be represented). Also the transition function is only
    partial. The semantics are that there is a virtual failure state into which an
    executing algorithm will go if no transition can be taken. -}
data DEA a st = DEA { deaTransitions :: Map st (Map a st)
                  , deaInit :: st
                  -- , deaFinals :: Set st -- Not needed at the moment
                  } deriving (Eq,Ord)

instance (Show a,Show st,Ord st) => Show (DEA a st) where
  show dea = unlines $ concat [ [(if st == (deaInit dea)
                                 then "initial "
                                 else "") ++
                                "state "++show st]++
                               [ "  "++show cond++" -> "++show trg | (cond,trg) <- Map.toList trans ]
                             | (st,trans) <- Map.toList $ deaTransitions dea ]

type PowSetSt st = Set st

-- | Creates a new state /q/ which will be the only initial state of /ba/ and duplicates all
--  transitions from the old initial states but originating at q. Leaves the rest of the
--  automaton as it is. This follows the standard construction.
mergeInits :: (Eq a, Ord a, Eq st, Ord st, BAState st) => BA a st -> BA a st
mergeInits ba =
  let initTrans = foldl (\ts s -> Set.union ts $ fromJust $ (Map.lookup s $ baTransitions ba)) Set.empty $ baInits ba
      initState = unusedBAState ba
  in ba {
    baTransitions = Map.insert initState initTrans $ baTransitions ba,
    baInits = Set.singleton initState
  }

-- | Tries to determinize a given B&#xFC;chi automaton. Only possible if all states are final.
determinizeBA :: (Eq a, Ord a, Eq st, Ord st, BAState st) => BA a st -> DEA a (PowSetSt st)
determinizeBA ba
  | (Set.size $ baFinals ba) /= (Map.size $ baTransitions ba) = error "Not able to transform BA into DEA."
  | otherwise =
      let ba' = mergeInits ba
          initS = Set.singleton $ Set.findMin $ baInits ba
          (trans, states) = determinize' ba (Set.singleton initS) (Map.empty, Set.empty)
      in DEA {
          deaTransitions = trans,
          deaInit = initS
        }
      where
        determinize' :: (Eq a, Ord a, Eq st, Ord st) => BA a st -> Set (Set st) -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st)) -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st))
        determinize' ba remaining r
          | Set.null remaining = r
          | otherwise =
            let next = Set.findMax remaining
                (remaining', trans', qs') = buildTransition ba next r
            in determinize' ba (Set.union remaining' (Set.delete next remaining)) (trans', qs')

        buildTransition :: (Eq a, Ord a, Eq st, Ord st) => BA a st -> Set st -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st)) -> (Set (PowSetSt st), Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st))
        buildTransition ba q (trans, qs) =
          let trans' = getTransitions ba q
              trans'' = mergeTransitions trans'
              newStates = (targetStates trans'') `Set.difference` qs
          in (newStates, Map.insert q trans'' trans, Set.insert q qs)

        -- Get the transitions in the BA which origin at the given set of states.
        getTransitions :: (Eq a, Ord a, Eq st, Ord st) => BA a st -> PowSetSt st -> Set (Map a (Set st))
        getTransitions ba = foldl (\trans s -> Set.insert (transform $ fromJust $ Map.lookup s (baTransitions ba)) trans) Set.empty
          where
            transform :: (Eq a, Ord a, Eq st, Ord st) => Set (a, st) -> Map a (Set st)
            transform = foldl putTransition Map.empty
            putTransition trans' (g, ts) = Map.alter (maybe (Just $ Set.singleton ts) (\ts' -> Just $ Set.insert ts ts')) g trans'

        -- Given a set of transitions merge these into transitions leading into the power set of states.
        mergeTransitions :: (Eq a, Ord a, Eq st, Ord st) => Set (Map a (Set st)) -> Map a (PowSetSt st)
        mergeTransitions = foldl (flip mergeTransitions') Map.empty
          where
            mergeTransitions' trans = Map.foldrWithKey unionState trans
            unionState g ts trans' = Map.alter (maybe (Just ts) (Just . (Set.union ts))) g trans'

        targetStates :: (Eq st, Ord st) => Map a (PowSetSt st) -> Set (PowSetSt st)
        targetStates = foldl (flip Set.insert) Set.empty

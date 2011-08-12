{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}

module Language.GTL.DEA (
    DEA(..), determinizeBA, minimizeDEA
  )
  where

import Prelude hiding (foldl)
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Data.Foldable (foldl, find)
import Language.GTL.Buchi

-- Models total functions via mapping structures. The instances may not really be total,
-- this has to be ensured by the user. But it should make the intention clear.
class TotalFunction a b c | a -> b, a -> c where
  (!$) :: a -> b -> c

-- Force total maps through type system.
data MakeTotal a = MakeTotal a
unTotal (MakeTotal m) = m

instance Ord a => TotalFunction (MakeTotal (Map a b)) a b where
  (MakeTotal m) !$ k = fromJust $ Map.lookup k m

type DEATransitionFunc a st = MakeTotal (Map st (Map a st))

{-| Not a real DEA. Has no final states as they are not needed (the acceptance condition
    of the Buchi automaton can not be represented). Also the transition function is only
    partial. The semantics are that there is a virtual failure state into which an
    executing algorithm will go if no transition can be taken. -}
data DEA a st = DEA { deaTransitions :: DEATransitionFunc a st
                  , deaInit :: st
                  -- , deaFinals :: Set st -- Not needed at the moment
                  }

instance (Show a,Show st,Ord st) => Show (DEA a st) where
  show dea = unlines $ concat [ [(if st == (deaInit dea)
                                 then "initial "
                                 else "") ++
                                "state "++show st]++
                               [ "  "++show cond++" -> "++show trg | (cond,trg) <- Map.toList trans ]
                             | (st,trans) <- Map.toList $ unTotal $ deaTransitions dea ]

-- Make clear that the transition function of the Buchi is expected to be total.
type BATransitionFunc a st = MakeTotal (Map st (Set (a, st)))

-- Models subsets of a set of states.
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
          (trans, states) = determinize' (MakeTotal $ baTransitions ba) (Set.singleton initS) (Map.empty, Set.empty)
      in DEA {
          deaTransitions = MakeTotal trans,
          deaInit = initS
        }
      where
        determinize' :: (Eq a, Ord a, Eq st, Ord st) => BATransitionFunc a st -> Set (Set st) -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st)) -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st))
        determinize' ba remaining r
          | Set.null remaining = r
          | otherwise =
            let next = Set.findMax remaining
                (remaining', trans', qs') = buildTransition ba next r
            in determinize' ba (Set.union remaining' (Set.delete next remaining)) (trans', qs')

        buildTransition :: (Eq a, Ord a, Eq st, Ord st) => BATransitionFunc a st -> Set st -> (Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st)) -> (Set (PowSetSt st), Map (PowSetSt st) (Map a (PowSetSt st)), Set (PowSetSt st))
        buildTransition ba q (trans, qs) =
          let trans' = getTransitions ba q
              trans'' = mergeTransitions trans'
              newStates = (targetStates trans'') `Set.difference` qs
          in (newStates, Map.insert q trans'' trans, Set.insert q qs)

        -- Get the transitions in the BA which origin at the given set of states.
        getTransitions :: (Eq a, Ord a, Eq st, Ord st) => BATransitionFunc a st -> PowSetSt st -> Set (Map a (Set st))
        getTransitions ba = foldl (\trans s -> Set.insert (transform $ (ba !$ s)) trans) Set.empty
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

minimizeDEA :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DEA a st -> DEA a (PowSetSt st)
minimizeDEA dea =
  let initEqClasses = Set.fromList [states dea] -- if there would be any final states: `Set.difference` (deaFinals dea), deaFinals dea]
      eqClasses = findEqClasses dea initEqClasses
      trans' = buildMinDEA dea eqClasses
      init' = fromJust $ find (Set.member $ deaInit dea) eqClasses
  in DEA (MakeTotal trans') init'
  where
    states = (foldl (foldl $ flip Set.insert) Set.empty) . unTotal . deaTransitions

    getEquivClass eqClasses s = fromJust $ find (Set.member s) eqClasses -- the state is guaranteed to be in some class

    findEqClasses :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DEA a st -> Set (PowSetSt st) -> Set (PowSetSt st)
    findEqClasses dea eqClasses =
      let eqClasses' = foldl (\eqs' e -> eqs' `Set.union` (splitClass dea eqClasses e)) Set.empty eqClasses
      in if eqClasses /= eqClasses' then findEqClasses dea eqClasses' else eqClasses'

    splitClass :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DEA a st -> Set (Set st) -> Set st -> Set (Set st)
    splitClass dea eqClasses eqClass =
      let (next:rest) = Set.toList eqClass -- equivalence classes are never empty
      in splitClass' dea eqClasses (Set.singleton $ Set.singleton next) rest
      where
        splitClass' dea eqClasses eqClasses' eqClass = foldl (putIntoClass dea eqClasses) eqClasses' eqClass
        putIntoClass dea eqClasses eqClasses' s =
          let (eqClasses'', inserted) = foldl (\(cs,f) c -> if transMatch dea eqClasses (Set.findMin c) s then (Set.insert (Set.insert s c) cs, True) else (Set.insert c cs, f)) (Set.empty, False) eqClasses'
          in if not inserted then Set.insert (Set.singleton s) eqClasses'' else eqClasses''
        transMatch dea eqClasses s1 s2 =
          let t1 = (deaTransitions dea) !$ s1
              t2 = (deaTransitions dea) !$ s2
              d1 = Map.differenceWith (equiv eqClasses) t1 t2
              d2 = Map.differenceWith (equiv eqClasses) t2 t1
          in Map.null d1 && Map.null d2 -- symmetric difference
        equiv eqClasses s1 s2 = if Set.member s2 $ getEquivClass eqClasses s1 then Nothing else Just s1

    buildMinDEA :: (Eq a, Ord a, Eq st, Ord st) => DEA a st -> Set (PowSetSt st) -> Map (PowSetSt st) (Map a (PowSetSt st))
    buildMinDEA dea eqClasses = foldl (\trans s -> Map.insert s (buildTrans dea eqClasses s) trans) Map.empty eqClasses
      where
        -- Takes a state in the minimized DEA and builds the transitions originating there.
        buildTrans :: (Eq a, Ord a, Eq st, Ord st) => DEA a st -> Set (PowSetSt st) -> PowSetSt st -> Map a (PowSetSt st)
        buildTrans dea eqClasses = foldl (\trans s -> trans `Map.union` (Map.map (getEquivClass eqClasses) (deaTransitions dea !$ s))) Map.empty

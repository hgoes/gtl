{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, ScopedTypeVariables #-}

module Language.GTL.DFA (
    DFA(..), determinizeBA, minimizeDFA, renameDFAStates, unTotal
  )
  where

import Prelude hiding (foldl)
import Data.Set as Set
import Data.Map as Map
import Data.Maybe
import Data.Foldable (foldl, find)
import Language.GTL.Buchi
import Data.AtomContainer
import Data.List (sortBy)
import Data.Function (on)

-- Models total functions via mapping structures. The instances may not really be total,
-- this has to be ensured by the user (how should that be checked?).
-- But it should make the intention clear.
class TotalFunction a b c | a -> b, a -> c where
  (!$) :: a -> b -> c

-- Force total maps through type system.
data MakeTotal m = MakeTotal { unTotal :: m }

instance Ord a => TotalFunction (MakeTotal (Map a b)) a b where
  m !$ k = fromJust $ Map.lookup k $ unTotal m

type DFATransitionFunc a st = MakeTotal (Map st [(a,st)])

{-| Not a real DFA. Has no final states as they are not needed (the acceptance condition
    of the Buchi automaton can not be represented). The semantics are that the automaton
    should never stop (see below).

    Also the transition function is only partial regarding to the guards. The semantics
    are that there is a virtual failure state into which an executing algorithm will go
    if no transition can be taken. There the automaton stops and execution fails. -}
data DFA a st = DFA { dfaTransitions :: DFATransitionFunc a st
                    , dfaInit :: st
                      -- , dfaFinals :: Set st -- Not needed at the moment
                    }

instance (Show a,Show st,Ord st) => Show (DFA a st) where
  show dfa = unlines $ concat [ [(if st == (dfaInit dfa)
                                 then "initial "
                                 else "") ++
                                "state "++show st]++
                               [ "  "++show cond++" -> "++show trg | (cond,trg) <- trans ]
                             | (st,trans) <- Map.toList $ unTotal $ dfaTransitions dfa ]

states :: (Eq st, Ord st) => DFA a st -> Set st
states = Map.keysSet . unTotal . dfaTransitions

-- Make clear that the transition function of the Buchi is expected to be total.
type BATransitionFunc a st = MakeTotal (Map st (Set (a, st)))

-- Models subsets of a set of states.
type PowSetSt st = Set st

-- | Creates a new state /q/ which will be the only initial state of /ba/ and duplicates all
--  transitions from the old initial states but originating at q. Leaves the rest of the
--  automaton as it is. This follows the standard construction.
mergeInits :: (Eq a, Ord a, Eq st, Ord st, BAState st) => BA a st -> BA a st
mergeInits ba =
  let initTrans = foldl (\ts s -> ts ++ (fromJust $ (Map.lookup s $ baTransitions ba))) [] $ baInits ba
      initState = unusedBAState ba
  in ba {
    baTransitions = Map.insert initState initTrans $ baTransitions ba,
    baInits = Set.singleton initState
  }

-- | Tries to determinize a given B&#xFC;chi automaton. Only possible if all states are final.
-- If not possible it returns Nothing.
determinizeBA :: forall a st el. (Eq a, Ord a, Eq st, Ord st,AtomContainer a el,Show a,Show st) => BA a st -> Maybe (DFA a (PowSetSt st))
determinizeBA ba
  | (Set.size $ baFinals ba) /= (Map.size $ baTransitions ba) = Nothing
  | otherwise =
      let initS = baInits ba
          trans = determinize' (MakeTotal $ fmap Set.fromList $ baTransitions ba) Set.empty [initS] Map.empty
      in Just $ DFA {
          dfaTransitions = MakeTotal trans,
          dfaInit = initS
        }
      where
        determinize' :: MakeTotal (Map st (Set (a, st))) -> Set (PowSetSt st) -> [PowSetSt st] -> Map (PowSetSt st)	 [(a, PowSetSt st)] -> Map (PowSetSt st) [(a, PowSetSt st)]
        determinize' _ _ [] trans = trans
        determinize' ba visited (next:remaining) trans
          | Set.member next visited = determinize' ba visited remaining trans
          | otherwise = let trans' = mergeTransitions (concat $ fmap Map.toList $ Set.toList $ getTransitions ba next) []
                            trans'' = trans' `seq` (Map.insert next trans' trans)
                            newStates = fmap snd trans'
                            remaining' = newStates `seq` (newStates ++ remaining)
                        in determinize' ba (Set.insert next visited) remaining' trans''

        -- Get the transitions in the BA which origin at the given set of states.
        getTransitions ba = foldl (\trans s -> Set.insert (transform $ (ba !$ s)) trans) Set.empty
          where
            transform :: (Eq a, Ord a, Eq st, Ord st) => Set (a, st) -> Map a (Set st)
            transform = foldl putTransition Map.empty
            putTransition trans' (g, ts) = Map.alter (maybe (Just $ Set.singleton ts) (\ts' -> Just $ Set.insert ts ts')) g trans'

        -- Given a set of transitions merge these into transitions leading into the power set of states.
        mergeTransitions trans = fmap (\(t,trg,n) -> (t,trg))
                                    . sortBy (compare `on` \(_,_,x) -> x)
                                    . mergeTransitions' atomsTrue Set.empty trans 0
          where
            mergeTransitions' t trg [] n mp = if n==0
                                              then mp
                                              else insertTransition t trg n mp

            mergeTransitions' t trg ((t',trg'):trans) n mp = case mergeAtoms t t' of
              Nothing -> mergeTransitions' t trg trans n mp
              Just nt -> if nt==t
                         then mergeTransitions' t (Set.union trg trg') trans (n+1) mp
                         else (let nmp = mergeTransitions' nt (Set.union trg trg') trans (n+1) mp
                               in mergeTransitions' t trg trans n nmp)

        insertTransition t trg n [] = [(t,trg,n)]
        insertTransition t trg n ((t',trg',n'):ts) = case compareAtoms t t' of
          ELT -> (t',Set.union trg trg',max n n'):ts
          EGT -> (t, Set.union trg trg',max n n'):ts
          EEQ -> (t',Set.union trg trg',max n n'):ts
          _ -> (t',trg',n'):insertTransition t trg n ts

        targetStates :: (Eq st, Ord st) => Map a (PowSetSt st) -> Set (PowSetSt st)
        targetStates = foldl (flip Set.insert) Set.empty

minimizeDFA :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DFA a st -> DFA a (PowSetSt st)
minimizeDFA dfa =
  let initEqClasses = Set.fromList [states dfa] -- if there would be any final states: `Set.difference` (dfaFinals dfa), dfaFinals dfa]
      eqClasses = findEqClasses dfa initEqClasses
      trans' = buildMinDFA dfa eqClasses
      init' = fromJust $ find (Set.member $ dfaInit dfa) eqClasses
  in DFA (MakeTotal trans') init'
  where
    getEquivClass eqClasses s = fromJust $ find (Set.member s) eqClasses -- the state is guaranteed to be in some class

    findEqClasses :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DFA a st -> Set (PowSetSt st) -> Set (PowSetSt st)
    findEqClasses dfa eqClasses =
      let eqClasses' = foldl (\eqs' e -> eqs' `Set.union` (splitClass dfa eqClasses e)) Set.empty eqClasses
      in if eqClasses /= eqClasses' then findEqClasses dfa eqClasses' else eqClasses'

    splitClass :: (Eq a, Ord a, Eq st, Ord st, Show a, Show st) => DFA a st -> Set (Set st) -> Set st -> Set (Set st)
    splitClass dfa eqClasses eqClass =
      let (next:rest) = Set.toList eqClass -- equivalence classes are never empty
      in splitClass' dfa eqClasses (Set.singleton $ Set.singleton next) rest
      where
        splitClass' dfa eqClasses eqClasses' eqClass = foldl (putIntoClass dfa eqClasses) eqClasses' eqClass
        putIntoClass dfa eqClasses eqClasses' s =
          let (eqClasses'', inserted) = foldl (\(cs,f) c -> if transMatch dfa eqClasses (Set.findMin c) s then (Set.insert (Set.insert s c) cs, True) else (Set.insert c cs, f)) (Set.empty, False) eqClasses'
          in if not inserted then Set.insert (Set.singleton s) eqClasses'' else eqClasses''
        transMatch dfa eqClasses s1 s2 =
          let t1 = Map.fromList $ (dfaTransitions dfa) !$ s1
              t2 = Map.fromList $ (dfaTransitions dfa) !$ s2
              d1 = Map.differenceWith (equiv eqClasses) t1 t2
              d2 = Map.differenceWith (equiv eqClasses) t2 t1
          in Map.null d1 && Map.null d2 -- symmetric difference
        equiv eqClasses s1 s2 = if Set.member s2 $ getEquivClass eqClasses s1 then Nothing else Just s1

    buildMinDFA :: (Eq a, Ord a, Eq st, Ord st) => DFA a st -> Set (PowSetSt st) -> Map (PowSetSt st) [(a,PowSetSt st)]
    buildMinDFA dfa eqClasses = foldl (\trans s -> Map.insert s (buildTrans dfa eqClasses s) trans) Map.empty eqClasses
      where
        -- Takes a state in the minimized DFA and builds the transitions originating there.
        buildTrans :: (Eq a, Ord a, Eq st, Ord st) => DFA a st -> Set (PowSetSt st) -> PowSetSt st -> [(a,PowSetSt st)]
        buildTrans dfa eqClasses = Map.toList . foldl (\trans s -> trans `Map.union` (Map.map (getEquivClass eqClasses) (Map.fromList $ dfaTransitions dfa !$ s))) Map.empty

renameDFAStates :: (Eq st, Ord st) => DFA a st -> DFA a Integer
renameDFAStates dfa =
  let stateMap = MakeTotal $ fst $ foldl (\(sMap, i) s -> (Map.insert s i sMap, i + 1)) (Map.empty, 0::Integer) $ states dfa
      trans' = Map.mapKeysMonotonic (stateMap !$) $ Map.map (fmap (\(t,trg) -> (t,stateMap !$ trg))) $ unTotal $ dfaTransitions dfa
      init' = stateMap !$ (dfaInit dfa) :: Integer
  in DFA (MakeTotal trans') init'

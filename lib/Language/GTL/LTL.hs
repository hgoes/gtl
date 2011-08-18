{-| Implements Linear Time Logic and its translation into Buchi-Automaton.
 -}
{-# LANGUAGE FlexibleInstances,MultiParamTypeClasses,FunctionalDependencies,FlexibleContexts,ScopedTypeVariables #-}
module Language.GTL.LTL(
  -- * Formulas
  LTL(..),
  BinOp(..),
  UnOp(..),
  -- * Buchi translation
  ltl2vwaa,
  vwaa2gba,
  minimizeGBA,
  gba2ba,
  minimizeBA,
  optimizeTransitionsBA,
  ltl2ba,
  AtomContainer(..),
  mapLTL,
  baProduct,
  baMapAlphabet
  ) where

import Data.Set as Set
import Data.Map as Map
import qualified Data.List as List
import Data.Foldable
import Prelude hiding (foldl,mapM,foldl1,concat,foldr)
import Language.GTL.Buchi
import Language.GTL.Expression (ExprOrdering(..))
import qualified Data.IntMap as IMap
import qualified Data.IntSet as ISet
import Data.Graph.Inductive as Graph (Gr(..), mkGraph, Graph(..), LNode, LEdge, Path, lab)
import Data.Graph.Inductive.Query.MinSpanningPath (minSpanningPath)

-- | A LTL formula with atoms of type /a/.
data LTL a = Atom a
           | Bin BinOp (LTL a) (LTL a)
           | Un UnOp (LTL a)
           | Ground Bool
           | LTLAutomaton (BA [a] Integer)
           deriving (Eq,Ord)

-- | Minimal set of binary operators for LTL.
data BinOp = And
           | Or
           | Until
           | UntilOp
           deriving (Eq,Ord)

-- | Unary operators for LTL.
data UnOp = Not
          | Next
          deriving (Eq,Ord)

-- | Map over the variables in a LTL formula.
mapLTL :: (Ord a,Ord b) => (a -> b) -> LTL a -> LTL b
mapLTL f (Atom x) = Atom (f x)
mapLTL f (Bin op l r) = Bin op (mapLTL f l) (mapLTL f r)
mapLTL f (Un op x) = Un op (mapLTL f x)
mapLTL f (Ground p) = Ground p
mapLTL f (LTLAutomaton b) = LTLAutomaton $ b { baTransitions = fmap (Set.map (\(cond,trg) -> (fmap f cond,trg))) (baTransitions b) }
--mapLTL f (LTLSimpleAutomaton b) = LTLSimpleAutomaton $ fmap (\st -> st { vars = Set.map f (vars st) }) b

binPrec :: BinOp -> Int
binPrec And = 7
binPrec Or = 6
binPrec Until = 5
binPrec UntilOp = 5

unPrec :: UnOp -> Int
unPrec Not = 9
unPrec Next = 4

instance Show BinOp where
  {-
  show And = "\x2227"
  show Or = "\x2228" -}
  show Until = "U"
  show UntilOp = "V"
  show And = "and"
  show Or = "or"

instance Show UnOp where
  --show Not = "\xac"
  show Not = "not "
  show Next = "X "

instance Show a => Show (LTL a) where
  showsPrec p (Atom x) = showsPrec p x
  showsPrec p (Bin Until (Ground True) phi) = let str = showString "F " . showsPrec (binPrec Until) phi
                                              in if p >= binPrec Until
                                                 then showChar '(' . str . showChar ')'
                                                 else str
  showsPrec p (Bin UntilOp (Ground False) phi) = let str = showString "G " . showsPrec (binPrec UntilOp) phi
                                                 in if p >= binPrec UntilOp
                                                    then showChar '(' . str . showChar ')'
                                                    else str
  showsPrec p (Bin op l r) = let str = showsPrec (binPrec op) l .
                                       showChar ' ' .
                                       shows op .
                                       showChar ' ' .
                                       showsPrec (binPrec op) r
                             in if p >= binPrec op
                                then showChar '(' . str . showChar ')'
                                else str
  showsPrec p (Un op x) = let str = shows op .
                                    showsPrec (unPrec op) x
                          in if p >= unPrec op
                             then showChar '(' . str . showChar ')'
                             else str
  showsPrec _ (Ground x) = if x then showString "tt" --showChar '\x22a4'
                           else showString "ff" --showChar '\x22a5'

distributeNegation :: LTL a -> LTL a
distributeNegation (Atom x) = Atom x
distributeNegation (Ground p) = Ground p
distributeNegation (Bin op l r) = Bin op (distributeNegation l) (distributeNegation r)
distributeNegation (Un Not x) = pushNegation x
distributeNegation (Un op x) = Un op (distributeNegation x)
distributeNegation aut@(LTLAutomaton _) = aut

pushNegation :: LTL a -> LTL a
pushNegation (Atom x) = Un Not (Atom x)
pushNegation (Ground p) = Ground $ not p
pushNegation (Bin op l r) = Bin (case op of
                                    And -> Or
                                    Or -> And
                                    Until -> UntilOp
                                    UntilOp -> Until)
                            (pushNegation l)
                            (pushNegation r)
pushNegation (Un Not x) = distributeNegation x
pushNegation (Un Next x) = Un Next (pushNegation x)
--pushNegation (LTLSimpleAutomaton _) = error "Complementing automata is not yet implemented"
pushNegation (LTLAutomaton _) = error "Complementing automata is not yet implemented"

{-
-- | Extracts all until constructs from a LTL formula.
--   Each until gets a unique `Integer' identifier.
untils :: Ord a => LTL a -> (Map (LTL a,LTL a) Integer,Integer)
untils = untils' 0
  where
    untils' :: Ord a => Integer -> LTL a -> (Map (LTL a,LTL a) Integer,Integer)
    untils' n (Atom _) = (Map.empty,n)
    untils' n (Ground _) = (Map.empty,n)
    untils' n (Bin Until l r) = let (mpl,nl) = untils' n l
                                    (mpr,nr) = untils' nl r
                                in (Map.insert (l,r) nr (Map.union mpl mpr),nr+1)
    untils' n (Bin op l r) = let (mpl,nl) = untils' n l
                                 (mpr,nr) = untils' nl r
                             in (Map.union mpl mpr,nr+1)
    untils' n (Un op x) = untils' n x
    --untils' n (LTLSimpleAutomaton _) = (Map.empty,n)
    untils' n (LTLAutomaton buchi) = foldl (\(mp,n) co -> let (nmp,n') = untils' n (vars co)
                                                          in (Map.union mp nmp,n')
                                           ) (Map.empty,0)
                                     (Map.elems buchi)-}

ltlAtoms :: Ord b => (a -> [b]) -> LTL a -> Set b
ltlAtoms f (Atom x) = Set.fromList (f x)
ltlAtoms _ (Ground _) = Set.empty
ltlAtoms f (Bin _ l r) = Set.union (ltlAtoms f l) (ltlAtoms f r)
ltlAtoms f (Un _ x) = ltlAtoms f x

-- | Represents data structures which can store atomic expressions
class Ord b => AtomContainer a b | a -> b where
  atomsTrue :: a -- ^ The container representing all possible values
  atomSingleton :: Bool -> b -> a -- ^ A container containing just a single restriction on the values.
  compareAtoms :: a -> a -> ExprOrdering -- ^ Compare the value spaces defined by the containers
  mergeAtoms :: a -> a -> Maybe a -- ^ Merge the containers together, resulting in a container which represents the intersection between the two.

instance Ord a => AtomContainer (Map a Bool) a where
  atomsTrue = Map.empty
  atomSingleton t p = Map.singleton p t
  compareAtoms x y
    | x == y = EEQ
    | Map.isSubmapOf x y = EGT
    | Map.isSubmapOf y x = ELT
    | otherwise = ENEQ
  mergeAtoms = mergeAlphabet

-- | Merge redundant transitions in a B&#xFC;chi automaton.
optimizeTransitionsBA :: (Ord st,AtomContainer b a,Ord b) => BA b st -> BA b st
optimizeTransitionsBA ba = BA { baTransitions = ntrans
                              , baInits = baInits ba
                              , baFinals = baFinals ba
                              }
  where
    ntrans = fmap (\set -> Set.fromList $ minimizeTrans [] (Set.toList set)) (baTransitions ba)

    minimizeTrans d [] = d
    minimizeTrans d ((c,st):ts) = minimizeTrans' d c st [] ts

    minimizeTrans' d c st d' [] = minimizeTrans ((c,st):d) d'
    minimizeTrans' d c st d' ((c',st'):ts) = if st==st'
                                             then (case compareAtoms c' c of
                                                      EEQ -> minimizeTrans' d c st d' ts
                                                      ELT -> minimizeTrans' d c st d' ts
                                                      EGT -> minimizeTrans' d c' st' d' ts
                                                      _ -> minimizeTrans' d c st ((c',st'):d') ts)
                                             else minimizeTrans' d c st ((c',st'):d') ts

-- | Merge redundant states in a B&#xFC;chi automaton.
minimizeBA :: (AtomContainer b a,Ord st,Ord b) => BA b st -> BA b st
minimizeBA ba = BA { baTransitions = ntrans
                   , baInits = Set.intersection (baInits ba) (Map.keysSet ntrans)
                   , baFinals = Set.intersection (baFinals ba) (Map.keysSet ntrans)
                   }
  where
    ntrans = Map.fromList $ minimizeBA' False [] (Map.toList (baTransitions ba))

    minimizeBA' False d [] = d
    minimizeBA' True d [] = minimizeBA' False [] d
    minimizeBA' ch d ((st,trans):xs) = minimizeBA'' ch d st trans [] xs

    minimizeBA'' ch d st trans d' [] = minimizeBA' ch ((st,trans):d) d'
    minimizeBA'' ch d st trans d' ((st',trans'):xs) = if (trans==trans') && (Set.member st (baFinals ba) == Set.member st' (baFinals ba))
                                                      then minimizeBA'' True (updateTranss st st' d) st
                                                           (updateTrans st st' trans) (updateTranss st st' d') (updateTranss st st' xs)
                                                      else minimizeBA'' ch d st trans ((st',trans'):d') xs

    updateTrans st st' trans = Set.map (\(cond,trg) -> if trg==st'
                                                       then (cond,st)
                                                       else (cond,trg)) trans

    updateTranss st st' = fmap (\(cst,trans) -> (cst,updateTrans st st' trans))

-- | Translate a generalized B&#xFC;chi automaton into a regular one by introducing levels.
gba2ba :: (Ord st, AtomContainer b a, Ord b) => GBA b st -> BA b (Set st,Int)
gba2ba gba = BA { baInits = inits
                , baFinals = Set.map (\x -> (x,final_size)) (Map.keysSet (gbaTransitions gba))
                , baTransitions = buildTrans (Set.toList inits) Map.empty
                }
  where
    inits = Set.map (\x -> (x,0)) (gbaInits gba)
    finalList = optimizeFinalFamilyOrder $ buildFs (gbaTransitions gba)
    final_size = List.length finalList

    buildTrans [] mp = mp
    buildTrans ((st,i):sts) mp
      | Map.member (st,i) mp = buildTrans sts mp
      | otherwise = let ntrans = Set.map (\(cond,trg,fins) -> (cond,(trg,next i fins))) ((gbaTransitions gba)!st)
                    in buildTrans ([ trg | (_,trg) <- Set.toList ntrans ]++sts) (Map.insert (st,i) ntrans mp)

    next j fin = let j' = if j==final_size
                          then 0
                          else j

                     findNext k [] = k
                     findNext k (f:fs) = if Set.member f fin
                                         then findNext (k+1) fs
                                         else k
                 in findNext j' (drop j' finalList)

-- | delta : 2^Q -> 2^(S x 2^Q x 2^F), F ⊆ Q.
-- The transition are labeled with the index of the final set they belong to.
type LabeledHyperTransitionMap st a = Map (Set st) (Set (a, Set st, Set st))
-- | delta : 2^Q -> 2^(S x 2^Q), F ⊆ Q.
-- Hyper refers to hyper graphs as one edge points to multiple nodes.
type HyperTransitionMap st a = Map (Set st) (Set (a, Set st))
-- | delta : F -> 2^(S x 2^Q), F ⊆ Q.
-- Mapping from an final set index to assigned transitions for _one_ starting node.
type FinalTransitionMap st a = Map st (Set (a, Set st))
-- | T_f ⊆ (2^(S x 2^Q))^Q -- that is a subset of all mappings Q -> 2^(S x 2^Q)
type FinalSetFamily st a = Map st (HyperTransitionMap st a)

-- Mapping from sets of final transitions to the contained transitions
buildFs :: forall st a. (Ord st, Ord a) => LabeledHyperTransitionMap st a -> FinalSetFamily st a
buildFs trans
  = Map.foldlWithKey buildFinalSets Map.empty trans
  where
    -- StartingStates -> Transitions from these States -> Map from final states to map of transitions
    buildFinalSets :: FinalSetFamily st a -> Set st -> Set (a, Set st, Set st) -> FinalSetFamily st a
    buildFinalSets finTs s ts =
      mergeFinalSets finTs s $ foldl extendFinalTransitionMap Map.empty ts

    -- Given a mapping from the final sets to their assigned transitions and the states from which these
    -- transitions originate. Merge these into the global mapping of final sets.
    mergeFinalSets :: FinalSetFamily st a -> Set st -> FinalTransitionMap st a -> FinalSetFamily st a
    mergeFinalSets finTs orig someFinTs
      = Map.foldlWithKey (\ finTs' finSt tr -> Map.alter (insertOrCreateMap orig tr) finSt finTs') finTs someFinTs

    -- Given a mapping from the index of a final set to its so far assigned transitions
    -- for _one_ originating node. This function extends this map by all transitions given in
    -- by /(x, tgts)/.
    extendFinalTransitionMap :: FinalTransitionMap st a -> (a, Set st, Set st) -> FinalTransitionMap st a
    extendFinalTransitionMap partFinTs (x, tgts, fin)
      = unionFinals partFinTs $ buildFinalTransitionSets x tgts fin

    buildFinalTransitionSets :: a -> Set st -> Set st -> Map st (a, Set st)
    buildFinalTransitionSets x tgts fin
      = foldl (\finTrans f -> Map.insert f (x, tgts) finTrans) Map.empty fin

    -- Given a map of f transitions extends the existing transitions by the on given in g for each
    -- state q. f'(q) = f(q) ⋃ {g(q)}
    unionFinals :: FinalTransitionMap st a -> Map st (a, Set st) -> FinalTransitionMap st a
    unionFinals partFinTs finTrans
      = Map.foldlWithKey (\partFinTs' s tr -> Map.alter (insertOrCreateSet tr) s partFinTs') partFinTs finTrans

    insertOrCreateSet x = maybe (Just $ Set.singleton x) (Just . (Set.insert x))
    insertOrCreateMap k v = maybe (Just $ Map.singleton k v) (Just . (Map.insert k v))

deepIntersection :: (Ord a, Ord b) => Map a (Set b) -> Map a (Set b) -> Map a (Set b)
deepIntersection = Map.intersectionWith Set.intersection

deepSize :: Foldable f => f (Set b) -> Int
deepSize = foldl (\n set -> n + Set.size set) 0

buildIntersectionGraph :: forall gr st a. (Graph.Graph gr, Ord st, Ord a) => FinalSetFamily st a -> gr st Int
buildIntersectionGraph finals =
  let
    -- Build graph nodes: assign each state an arbitrary number and
    -- keep the state names as labels in the graph.
    nodeList = (fst $ Map.foldlWithKey (\(nodes, i) s _ -> ((i, s) : nodes, i+1)) ([], 0) finals) :: [LNode st]
    --nodeList = (List.map (\i -> (i, ())) $ ISet.toList nodes)
    -- Replaces keys of the map by an arbitrary numbering.
    numberedFinalFamily = IMap.fromAscList $ zip [0..] $ Map.elems finals
    nodes = IMap.keysSet numberedFinalFamily

    countIntersections :: HyperTransitionMap st a -> HyperTransitionMap st a -> Int
    countIntersections l = deepSize . (deepIntersection l)

    -- | Given a node and its transitions builds its context in the intersection
    -- graph by putting all possible edges to the nodes in /ns/ into the context.
    -- The context makes up an undirected graph. It is assumed, that /i/ is not in /restGraph/.
    makeContext :: Int -> HyperTransitionMap st a -> ([LEdge Int], ISet.IntSet) -> ([LEdge Int], ISet.IntSet)
    makeContext i tr (es, restGraph) =
      let
        restGraph' = ISet.delete i restGraph
        -- multiply by -1 because we take later the _minimum_ spanning path but want the _maximum_!
        family i' =
          case IMap.lookup i' numberedFinalFamily of
            Just fam -> fam
        commonTransitions i' = -1 * countIntersections tr (family i')
        es' = ISet.fold (\i' adj' -> (i', i, commonTransitions i') : (i, i', commonTransitions i') : adj') [] restGraph'
      in (es' ++ es, restGraph')

    edges = fst $ IMap.foldWithKey makeContext ([], nodes) numberedFinalFamily

  in mkGraph nodeList edges

optimizeFinalFamilyOrder :: forall st a. (Ord st, Ord a) => FinalSetFamily st a -> [st]
optimizeFinalFamilyOrder finals =
  let
    intersectionGraph = buildIntersectionGraph finals :: Graph.Gr st Int

    -- graph complete => it is connected => always a valid result
    Just msp = minSpanningPath intersectionGraph

    getLabel g n =
      case lab g n of
        Just l -> l

    pathLabels :: (Graph gr) => gr nl el -> Path -> [nl]
    pathLabels g p = List.map (\n -> getLabel g n) p

    -- Find optimal start node:
    -- generate a pseudo node f0 = ⋃f_i, f_i € F. That is it contains all transitions
    -- which are in some final set. If the maximum spanning path is p = (f_i1, ...., f_in) then
    -- the path is reversed iff |f_in ⋂ f0| > |f_i1 ⋂ f0|.
    needsReverse =
      let
        f0 = foldl (Map.unionWith Set.union) Map.empty finals
        intersI1 = deepIntersection f0 $ (finals ! (getLabel intersectionGraph $ head msp))
        intersIn = deepIntersection f0 $ (finals ! (getLabel intersectionGraph $ head $ reverse msp))
      in deepSize intersIn > deepSize intersI1

    msp' = if needsReverse then reverse msp else msp
  in pathLabels intersectionGraph msp'

showCond :: Show a => Map a Bool -> String
showCond cond = concat $ List.intersperse "," [ (if pos then "" else "!")++show var | (var,pos) <- Map.toList cond ]

-- | Minimize a generalized B&#xFC;chi automaton by merging redundant states.
minimizeGBA :: (Ord st,Ord b,AtomContainer b a) => GBA b st -> GBA b st
minimizeGBA gba = case minimizeGBA' gba of
  Nothing -> gba
  Just ngba -> minimizeGBA ngba

minimizeGBA' :: (Ord st,Ord b,AtomContainer b a) => GBA b st -> Maybe (GBA b st)
minimizeGBA' gba = if changed
                   then Just (GBA { gbaTransitions = Map.fromList ntrans
                                  , gbaInits = ninit
                                  })
                   else Nothing
  where
    (changed,ntrans,ninit) = minimizeTrans False [] (Map.toList (gbaTransitions gba)) (gbaInits gba)

    updateTrans old new = fmap (\(st,t) -> (st,Set.map (\(cond,trg,fin) -> (cond,if trg==old
                                                                                 then new
                                                                                 else trg,fin)) t))

    minimizeTrans ch res [] i = (ch,res,i)
    minimizeTrans ch res ((st,t):xs) i
      = let (ch',res',ni,nxs) = minimizeTrans' st t ch ((st,t):res) i [] xs
        in minimizeTrans ch' res' nxs ni

    minimizeTrans' st t cch cres ci cxs [] = (cch,cres,ci,cxs)
    minimizeTrans' st t cch cres ci cxs ((st',t'):ys)
      = if t==t'
        then minimizeTrans' st t True
             (updateTrans st' st cres)
             (if Set.member st' ci
              then Set.insert st (Set.delete st' ci)
              else ci)
             (updateTrans st' st cxs)
             (updateTrans st' st ys)
        else minimizeTrans' st t cch cres ci ((st',t'):cxs) ys


-- | Merge redundant transitions in a VWAA.
optimizeVWAATransitions :: (AtomContainer b a,Ord st) => [(b,Set st)] -> [(b,Set st)]
optimizeVWAATransitions mp = List.filter
                             (\(cond,trg)
                              -> case List.find (\(cond',trg') -> (compareAtoms cond cond' == ELT)
                                                                  && (Set.isSubsetOf trg' trg)) mp of
                                   Nothing -> True
                                   Just _ -> False) mp

insertGBATransition :: (AtomContainer b a,Ord st) => (b,Set st,Set st) -> [(b,Set st,Set st)] -> [(b,Set st,Set st)]
insertGBATransition x [] = [x]
insertGBATransition t@(cond,trg,fin) all@(t'@(cond',trg',fin'):ys)
  | trg==trg' = case compareAtoms cond cond' of
    EEQ
      | Set.isSubsetOf fin' fin -> all
      | Set.isSubsetOf fin fin' -> t:ys
      | otherwise -> t':(insertGBATransition t ys)
    ELT
      | Set.isSubsetOf fin' fin -> all
      | otherwise -> t':(insertGBATransition t ys)
    EGT
      | Set.isSubsetOf fin fin' -> t:ys
      | otherwise -> t':(insertGBATransition t ys)
    _ -> t':(insertGBATransition t ys)
  | otherwise = t':(insertGBATransition t ys)

-- | Merge redundant transitions a generalized B&#xFC;chi automaton.
optimizeGBATransitions :: (AtomContainer b a,Ord st) => [(b,Set st,Set st)] -> [(b,Set st,Set st)]
optimizeGBATransitions = foldl (\ts t -> insertGBATransition t ts) []

-- | Translate a VWAA into a GBA.
vwaa2gba :: (AtomContainer b a,Ord b) => VWAA b (LTL a) -> GBA b (LTL a)
vwaa2gba aut = GBA { gbaTransitions = buildTrans (Set.toList (vwaaInits aut)) Map.empty
                   , gbaInits = vwaaInits aut
                   }
  where
    buildTrans [] mp = mp
    buildTrans (x:xs) mp
      | Map.member x mp = buildTrans xs mp
      | otherwise = let trans = optimizeGBATransitions $ finalSet $ convertTrans x
                    in buildTrans ([ trg | (_,trg,_) <- trans ]++xs) (Map.insert x (Set.fromList trans) mp)

    convertTrans sts
      | Set.null sts = []
      | otherwise = foldl1 transProd [ Set.toList $ (vwaaTransitions aut)!st | st <- Set.toList sts ]

    finalSet trans = [(cond,trg,Set.filter (\f -> not (Set.member f trg) ||
                                                  not (List.null [ (cond,trg')
                                                                 | (cond',trg') <- delta f,
                                                                   (case compareAtoms cond cond' of
                                                                       EEQ -> True
                                                                       ELT -> True
                                                                       _ -> False) &&
                                                                   Set.isSubsetOf trg trg' &&
                                                                   not (Set.member f trg')
                                                                 ])
                                           ) (vwaaCoFinals aut))
                     | (cond,trg) <- trans ]

delta, delta' :: AtomContainer b a => LTL a -> [(b,Set (LTL a))]
delta (Ground True) = [(atomsTrue,Set.singleton (Ground True))]
delta (Ground False) = []
delta (Atom p) = [(atomSingleton True p,Set.singleton (Ground True))]
delta (Un Not (Atom p)) = [(atomSingleton False p,Set.singleton (Ground True))]
delta (Un Next f) = [ (atomsTrue,xs) | xs <- Set.toList (cform f) ]
delta (Bin Until l r) = transUnion (delta' r) (transProd (delta' l) [(atomsTrue,Set.singleton (Bin Until l r))])
delta (Bin UntilOp l r) = transProd (delta' r) (transUnion (delta' l) [(atomsTrue,Set.singleton (Bin UntilOp l r))])

delta' (Bin Or l r) = transUnion (delta' l) (delta' r)
delta' (Bin And l r) = transProd (delta' l) (delta' r)
delta' f = delta f

cform :: Ord  a => LTL a -> Set (Set (LTL a))
cform (Bin And lhs rhs) = Set.fromList [ Set.union e1 e2
                                       | e1 <- Set.toList (cform lhs)
                                       , e2 <- Set.toList (cform rhs) ]
cform (Bin Or lhs rhs) = Set.union (cform lhs) (cform rhs)
cform f = Set.singleton (Set.singleton f)

-- | Translate LTL into an alternating automaton.
ltl2vwaa :: (Ord b,AtomContainer b a) => LTL a -> VWAA b (LTL a)
ltl2vwaa ltl = VWAA { vwaaTransitions = trans'
                    , vwaaInits = inits'
                    , vwaaCoFinals = getFinals trans'
                    }
  where
    inits' = cform ltl
    trans' = buildTrans (concat [ Set.toList xs | xs <- Set.toList inits']) Map.empty

    buildTrans [] mp = mp
    buildTrans (x:xs) mp
      | Map.member x mp = buildTrans xs mp
      | otherwise = let ts = optimizeVWAATransitions $ delta x
                    in buildTrans (concat [ Set.toList c | (_,c) <- ts ]++xs) (Map.insert x (Set.fromList ts) mp)

    isFinal (Bin Until _ _) = True
    isFinal _ = False

    getFinals mp = Set.filter isFinal $ Map.keysSet mp

mergeAlphabet :: Ord a => Map a Bool -> Map a Bool -> Maybe (Map a Bool)
mergeAlphabet a1 a2
  = if confl
    then Nothing
    else Just nmp
      where (confl,nmp) = Map.mapAccum (\hasC (x,y) -> (hasC || x/=y,x)) False $ Map.unionWith (\(x1,_) (y1,_) -> (x1,y1))
                          (fmap (\x -> (x,x)) a1)
                          (fmap (\x -> (x,x)) a2)

transProd :: AtomContainer b a => [(b,Set (LTL a))] -> [(b,Set (LTL a))] -> [(b,Set (LTL a))]
transProd m1 m2 = [ (na,transAnd e1 e2)
                  | (a1,e1) <- m1
                  , (a2,e2) <- m2
                  , na <- case mergeAtoms a1 a2 of
                    Nothing -> []
                    Just p -> [p]
                  ]

transAnd :: Ord a => Set (LTL a) -> Set (LTL a) -> Set (LTL a)
transAnd s1 s2
  | Set.toList s1 == [Ground True] = s2
  | Set.toList s2 == [Ground True] = s1
  | otherwise = Set.union s1 s2

transUnion :: AtomContainer b a => [(b,Set (LTL a))] -> [(b,Set (LTL a))] -> [(b,Set (LTL a))]
transUnion = (++)

-- | Translate a LTL formula into a B&#xFC;chi automaton
ltl2ba :: AtomContainer [a] a => LTL a -> BA [a] Integer
ltl2ba f = let (f',auts) = extractAutomata f
               mprod b1 b2 = renameStates $ baProduct b1 b2
           in case f' of
             Nothing -> foldl1 mprod auts
             Just rf -> foldl mprod (renameStates $ optimizeTransitionsBA $
                                     minimizeBA $ gba2ba $ minimizeGBA $
                                     vwaa2gba $ ltl2vwaa $ distributeNegation rf) auts

-- | Construct the product automaton for two B&#xFC;chi automata.
baProduct :: (Ord a,Ord st,Ord st',AtomContainer a b) => BA a st -> BA a st' -> BA a (st,st',Bool)
baProduct b1 b2 = BA { baTransitions = trans'
                     , baInits = Set.fromList inits'
                     , baFinals = fins'
                     }
  where
    inits' = [ (i1,i2,False)
             | i1 <- Set.toList (baInits b1),
               i2 <- Set.toList (baInits b2)
             ]

    trans' = traceStates inits' Map.empty

    fins' = Set.filter (\(st1,st2,i) -> i && Set.member st2 (baFinals b2)) $ Map.keysSet trans'

    traceStates [] mp = mp
    traceStates (x@(s1,s2,i):xs) mp
      | Map.member x mp = traceStates xs mp
      | otherwise = let t1 = (baTransitions b1)!s1
                        t2 = (baTransitions b2)!s2
                        trgs = [ (c,(nst1,nst2,if ((not i) && (Set.member nst1 (baFinals b1)))
                                                  || (i && (Set.member nst2 (baFinals b2)))
                                               then not i
                                               else i))
                               | (c1,nst1) <- Set.toList t1
                               , (c2,nst2) <- Set.toList t2
                               , c <- case mergeAtoms c1 c2 of
                                 Nothing -> []
                                 Just x -> [x]
                               ]
                    in traceStates ((fmap snd trgs)++xs) (Map.insert (s1,s2,i) (Set.fromList trgs) mp)

extractAutomata :: LTL a -> (Maybe (LTL a),[BA [a] Integer])
extractAutomata (LTLAutomaton buchi) = (Nothing,[buchi])
extractAutomata (Bin And l r) = let (ml,al) = extractAutomata l
                                    (mr,ar) = extractAutomata r
                                in (case ml of
                                       Nothing -> mr
                                       Just rl -> case mr of
                                         Nothing -> Just rl
                                         Just rr -> Just (Bin And rl rr),al++ar)
extractAutomata x = (Just x,[])

module Language.GTL.Buchi where

import Data.Map as Map
import Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,concat)
import Data.Binary
import qualified Data.List as List

-- | A simple generalized buchi automaton.
type Buchi a = GBuchi Integer a (Set Integer)

-- | A buchi automaton parametrized over the state identifier /st/, the variable type /a/ and the final set type /f/
type GBuchi st a f = Map st (BuchiState st a f)

-- | A state representation of a buchi automaton.
data BuchiState st a f = BuchiState
                         { isStart :: Bool -- ^ Is the state an initial state?
                         , vars :: a -- ^ The variables that must be true in this state.
                         , finalSets :: f -- ^ In which final sets is this state a member?
                         , successors :: Set st -- ^ All following states
                         } deriving (Show,Eq,Ord)

instance (Ord st,Binary st,Binary a,Binary f) => Binary (BuchiState st a f) where
  put st = put (isStart st) >> put (vars st) >> put (finalSets st) >> put (successors st)
  get = do
    is <- get
    va <- get
    fi <- get
    suc <- get
    return (BuchiState is va fi suc)

-- | Transforms a generalized buchi automaton into a regular one.
translateGBA :: (Ord st,Ord f) => GBuchi st a (Set f) -> GBuchi (st,Int) a Bool
translateGBA buchi = let finals = Set.unions [ finalSets decl | decl <- Map.elems buchi ]
                         fsize = Set.size finals
                         finals_list = Set.toList finals
                         expand c f st decl mp = case Map.lookup (st,c) mp of
                           Just _ -> mp
                           Nothing -> let isFinal = Set.member f (finalSets decl)
                                          nsuccs = Set.map (\n -> (n,nc)) (successors decl)
                                          nmp = Map.insert (st,c) (BuchiState { isStart = isStart decl
                                                                              , vars = vars decl
                                                                              , finalSets = isFinal
                                                                              , successors = nsuccs
                                                                              }) mp
                                          nc = if isFinal
                                               then (c+1) `mod` fsize
                                               else c
                                          nf = if isFinal
                                               then finals_list!!nc
                                               else f
                                      in foldl (\cmp succ -> expand nc nf succ (buchi!succ) cmp) nmp (successors decl)
                     in if fsize == 0
                        then Map.fromAscList [ ((st,0),BuchiState { isStart = isStart decl
                                                                  , vars = vars decl
                                                                  , finalSets = True
                                                                  , successors = Set.map (\n -> (n,0)) (successors decl)
                                                                  })
                                             | (st,decl) <- Map.toAscList buchi ]
                        else foldl (\mp (st,decl) -> expand 0 (head finals_list) st decl mp) Map.empty [ st | st <- Map.toList buchi, isStart $ snd st ]

-- | Calculates the product automaton of two given buchi automatons.
buchiProduct :: (Ord st1,Ord f1,Ord st2,Ord f2)
                => GBuchi st1 a (Set f1) -- ^ First buchi automaton
                -> GBuchi st2 b (Set f2) -- ^ Second buchi automaton
                -> GBuchi (st1,st2) (a,b) (Set (Either f1 f2))
buchiProduct = buchiProduct' (\s1 s2 -> (s1,s2)) (\l r -> (l,r)) id

buchiProduct' :: (Ord st1,Ord f1,Ord st2,Ord f2,Ord f,Ord st)
                 => (st1 -> st2 -> st)
                 -> (a -> b -> c)
                 -> (Either f1 f2 -> f)
                 -> GBuchi st1 a (Set f1) -- ^ First buchi automaton
                 -> GBuchi st2 b (Set f2) -- ^ Second buchi automaton
                 -> GBuchi st c (Set f)
buchiProduct' cst cco cf b1 b2 = foldl (\tmp ((i1,st1),(i2,st2)) -> putIn tmp i1 i2 st1 st2) Map.empty
                                 [ ((i1,st1),(i2,st2)) | (i1,st1) <- Map.toList b1, isStart st1, (i2,st2) <- Map.toList b2, isStart st2 ]
  where
    putIn mp i1 i2 st1 st2
      = let succs = [ (i,j)
                    | i <- Set.toList $ successors st1,
                      j <- Set.toList $ successors st2]
            nmp = Map.insert (cst i1 i2) (BuchiState { isStart = isStart st1 && isStart st2
                                                     , vars = cco (vars st1) (vars st2)
                                                     , finalSets = Set.union
                                                                   (Set.map (cf.Left) (finalSets st1))
                                                                   (Set.map (cf.Right) (finalSets st2))
                                                     , successors = Set.fromList (fmap (uncurry cst) succs)
                                                     }) mp
        in foldl (\tmp (i,j) -> trace tmp i j) nmp succs
    trace mp i1 i2
      | Map.member (cst i1 i2) mp = mp
      | otherwise = putIn mp i1 i2 (b1!i1) (b2!i2)

buchiUndefinedStates :: Ord st => GBuchi st a f -> Set st
buchiUndefinedStates buchi = foldl (\undef st -> foldl (\undef2 var -> if Map.member var buchi
                                                                       then undef2
                                                                       else Set.insert var undef2) undef (successors st)) Set.empty buchi

buchiRestrictReachable :: Ord st => GBuchi st a f -> GBuchi st a f
buchiRestrictReachable buchi = Map.intersection buchi (buchiReachable buchi)

buchiReachable :: Ord st => GBuchi st a f -> Map st ()
buchiReachable buchi = foldl (\reached (name,co) -> if Map.member name reached
                                                    then reached
                                                    else buchiReachable' (Map.insert name () reached) co
                             ) Map.empty [ el | el@(_,co) <- Map.toList buchi, isStart co ]
  where
    buchiReachable' reached co = foldl (\reached' succ -> if Map.member succ reached'
                                                          then reached'
                                                          else buchiReachable' (Map.insert succ () reached') (buchi!succ)) reached (successors co)


buchiGC :: Ord st => GBuchi st a f -> GBuchi st a f
buchiGC buchi = fmap (\co -> co { successors = Set.filter (\succ -> Map.member succ buchi) (successors co) }) buchi

buchiMapStates :: (Ord st,Ord st') => (st -> st') -> GBuchi st a f -> GBuchi st' a f
buchiMapStates f buchi = Map.fromList [ (f name,co { successors = Set.map f (successors co) }) | (name,co) <- Map.toList buchi ]

buchiMapVars :: (a -> b) -> GBuchi st a f -> GBuchi st b f
buchiMapVars f = fmap (\co -> co { vars = f (vars co) })

-- NEW IMPLEMENTATION:

data VWAA a st = VWAA { vwaaTransitions :: Map st (Set (a,Set st))
                      , vwaaInits :: Set (Set st)
                      , vwaaCoFinals :: Set st
                      } deriving (Eq,Ord)

data GBA a st = GBA { gbaTransitions :: Map (Set st) (Set (a,Set st,Set st))
                    , gbaInits :: Set (Set st)
                    } deriving (Eq,Ord)

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

instance (Show a,Show st) => Show (GBA a st) where
  show gba = unlines $ (concat [ [ "state "++show st ] ++
                                 [ "  "++show cond++" ->"++show (Set.toList fins)++" "++show (Set.toList trg) | (cond,trg,fins) <- Set.toList trans ]
                               | (st,trans) <- Map.toList (gbaTransitions gba) ])++
             ["inits: "++concat (List.intersperse ", " [  show (Set.toList f) | f <- Set.toList $ gbaInits gba ])]

baMapAlphabet :: (Ord a,Ord b,Ord st) => (a -> b) -> BA a st -> BA b st
baMapAlphabet f ba = ba { baTransitions = fmap (Set.map (\(c,trg) -> (f c,trg))) (baTransitions ba) }

renameStates :: Ord st => BA a st -> BA a Integer
renameStates ba = let (_,stmp) = Map.mapAccum (\i _ -> (i+1,i)) 0 (baTransitions ba)
                      trans' = fmap (\trg -> Set.mapMonotonic (\(c,t) -> (c,stmp!t)) trg) $ Map.mapKeysMonotonic (\k -> stmp!k) (baTransitions ba)
                      inits' = Set.mapMonotonic (stmp!) (baInits ba)
                      fins' = Set.mapMonotonic (stmp!) (baFinals ba)
                  in BA { baTransitions = trans'
                        , baInits = inits'
                        , baFinals = fins'
                        }

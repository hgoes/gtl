module Language.GTL.Buchi where

import Data.Map as Map
import Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl)

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
buchiProduct b1 b2 = foldl (\tmp ((i1,st1),(i2,st2)) -> putIn tmp i1 i2 st1 st2) Map.empty
                     [ ((i1,st1),(i2,st2)) | (i1,st1) <- Map.toList b1, isStart st1, (i2,st2) <- Map.toList b2, isStart st2 ]
  where
    putIn mp i1 i2 st1 st2
      = let succs = [ (i,j)
                    | i <- Set.toList $ successors st1,
                      j <- Set.toList $ successors st2]
            nmp = Map.insert (i1,i2) (BuchiState { isStart = isStart st1 && isStart st2
                                                 , vars = (vars st1,vars st2)
                                                 , finalSets = Set.union
                                                               (Set.mapMonotonic (Left) (finalSets st1))
                                                               (Set.mapMonotonic (Right) (finalSets st2))
                                                 , successors = Set.fromList succs
                                                 }) mp
        in foldl (\tmp (i,j) -> trace tmp i j) nmp succs
    trace mp i1 i2
      | Map.member (i1,i2) mp = mp
      | otherwise = putIn mp i1 i2 (b1!i1) (b2!i2)

buchiUndefinedStates :: Ord st => GBuchi st a f -> Set st
buchiUndefinedStates buchi = foldl (\undef st -> foldl (\undef2 var -> if Map.member var buchi
                                                                       then undef2
                                                                       else Set.insert var undef2) undef (successors st)) Set.empty buchi
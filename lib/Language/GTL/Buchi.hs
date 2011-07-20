module Language.GTL.Buchi where

import Data.Map as Map
import Data.Set as Set
import Data.Foldable
import Prelude hiding (foldl,concat)
import Data.Binary
import qualified Data.List as List

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


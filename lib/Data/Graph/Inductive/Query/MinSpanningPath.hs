{-# LANGUAGE ScopedTypeVariables #-}
module Data.Graph.Inductive.Query.MinSpanningPath (
    minSpanningPath
) where

import Data.Graph.Inductive as Graph

import qualified Data.PQueue.Prio.Min as PQ
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe

-- Test data
t1 = ([(-1, 2), (-0, 3), (-1, 4)], 1, (), [(-1, 2), (-0, 3), (-1, 4)]) :: Context () Integer
t2 = ([(-2, 4), (-0, 3)], 2, (), [(-2, 4), (-0, 3)]) :: Context () Integer
t3 = ([(-3, 4)], 3, (), [(-3, 4)]) :: Context () Integer
t4 = ([], 4, (), []) :: Context () Integer
g = buildGr [t1, t2, t3, t4] :: Gr () Integer
msp1 = minSpanningPath g -- == [1, 2, 4, 3]

t2_1 = ([(-3, 2)], 1, (), [(-3, 2)]) :: Context () Integer
t2_2 = ([], 2, (), []) :: Context () Integer
g2 = buildGr [t2_1, t2_2] :: Gr () Integer
msp2 = minSpanningPath g2 -- == [1, 2]

-- | Given a simple undirected graph G calculates the minimum spanning path, that
-- is a mst where deg(u) <= 2 for all nodes u in G.
-- Returns Nothing iff the graph is not connected.
minSpanningPath :: (Graph gr, Ord l) => gr a l -> Maybe Path
minSpanningPath g =
  let q = edgeQueue g
      n = Map.fromList $ map (\n -> (n, 0)) (nodes g) :: Map.Map Node Int
      chosen = Map.empty :: Map.Map Node [Edge]
  in fmap mkPath $ mspEdges n q chosen

edgeQueue :: (Graph gr, Ord l) => gr a l -> PQ.MinPQueue l Edge
edgeQueue = ufold edgeQueue' PQ.empty
  where
  edgeQueue' :: Ord l => Context a l -> PQ.MinPQueue l Edge -> PQ.MinPQueue l Edge
  edgeQueue' (inE, currentNode, _, _) edges = -- assumes that ingoing and outgoing edges are the same, i.e. an undirected graph
    foldl (insEdge currentNode) edges inE
    where insEdge currentNode edges (label, node) = PQ.insert label (currentNode, node) edges

-- Kanten des minimalen, aufspannenden Pfades finden (analog zu Kruskal).
-- Erzeuge Graph mit Kanten aus q. Füge jeweils Minimum ein und nur, wenn Knoten Grad < 2 hat.
-- Solange n != ∅
--  Wähle e = min q : e = (u, v), u,v € n
--  Wenn e existiert:
--    Setze deg(u) += 1 und deg(v) += 1
--    Wenn deg(u) = 2: Setze n := n \ {u}
--    Wenn deg(v) = 2: Setze n := n \ {v}
--    Wenn n != ∅: -- Sonst entsteht ein Loop, da dann alle Knoten Grad 2 haben.
--      Füge e zu g' hinzu
--  Sonst: es ex. kein msp
--
-- Was passiert wenn einer der Knoten Grad 0 hat bzw. kann dies passieren? Nein!
-- Induktion über eingefügte Kanten?
--
-- Achtung Sonderfall: |n| <= 2 für den Gesamtgraphen.

mspEdges :: forall l. Ord l => Map.Map Node Int -> PQ.MinPQueue l Edge -> Map.Map Node [Edge] -> Maybe (Map.Map Node [Edge])
mspEdges n q chosen =
  if not(Map.null n) then
    let (me, q') = choose n q
    in case me of
      -- Achtung Sonderfall: |n| <= 2 für den Gesamtgraphen:
      -- Dann ist n zwar nicht leer, aber man kann auch keine Kante mehr einfügen.
      Nothing -> if Map.size n == 2 then Just chosen else Nothing
      Just e@(u,v) ->
        let n' = (updateDegree u v n)
        in
          if not(Map.null n') then
            mspEdges n' q' (Map.alter (insertOrCreate e) v $ Map.alter (insertOrCreate e) u chosen)
          else
            Just chosen
  else
    Just chosen
  where
    choose :: Map.Map Node Int -> PQ.MinPQueue l Edge -> (Maybe Edge, PQ.MinPQueue l Edge)
    choose n q =
      case PQ.getMin q of
        Nothing -> (Nothing, PQ.deleteMin q)
        Just (_, e@(u,v)) ->
          if (Map.member u n) && (Map.member v n) then
            (Just e, PQ.deleteMin q)
          else
            choose n (PQ.deleteMin q)
    updateDegree u v n =
      let incDegOrDelete d = if d < 1 then Just (d+1) else Nothing
          n' = Map.update incDegOrDelete u n
          n'' = Map.update incDegOrDelete v n'
      in n''
    insertOrCreate x Nothing = Just [x]
    insertOrCreate x (Just xs) = Just (x:xs)

-- Assumes, that /chosen/ is not a single loop so that at least one node exists with degree 0.
mkPath :: Map.Map Node [Edge] -> Path
mkPath chosen =
  let deg1Node node edges Nothing = if List.length edges == 1 then Just node else Nothing
      deg1Node _ _ n@(Just _) = n
      startNode = fromJust $ Map.foldrWithKey deg1Node Nothing chosen
  in mkPath' startNode chosen [startNode]
    where
      mkPath' :: Node -> Map.Map Node [Edge] -> Path -> Path
      mkPath' current remaining p
        | Map.null remaining = p
        | otherwise =
          let outEdges = Map.findWithDefault [] current remaining
              nextNode = case outEdges of
                -- [] -> error "unconnected node" -- Should not happen
                [e] -> next current e
                [e1, e2] -> nextChoose current e1 e2 chosen
          in if (Map.member nextNode remaining) then
              mkPath' nextNode (Map.delete current remaining) (nextNode : p)
            else p
      next curr (u,v) = if curr == u then v else u
      nextChoose curr (u1,v1) (u2,v2) chosen
        | u1 == curr && (Map.member v1 chosen) = v1
        | v1 == curr && (Map.member u1 chosen) = u1
        | u2 == curr && (Map.member v2 chosen) = v2
        | v2 == curr && (Map.member u2 chosen) = u2


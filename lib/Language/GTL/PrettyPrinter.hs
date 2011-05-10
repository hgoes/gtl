{-# LANGUAGE GADTs #-}
{-| This module provides functions to render GTL specifications to Tikz Latex drawing commands.
    It can thus be used to get a pretty image for a GTL file.
 -}
module Language.GTL.PrettyPrinter where

import Language.GTL.Model
import Language.GTL.Expression
import Language.GTL.LTL hiding (And)
import Language.GTL.Translation
import Data.GraphViz hiding (Model)
import Data.GraphViz.Printing
import Data.GraphViz.Parsing
import Data.Maybe
import Data.Map as Map hiding (mapMaybe)
import Data.Set as Set
import Data.List as List
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import System.Process
import Data.Typeable
import Data.Traversable
import Prelude hiding (mapM)

simplePrettyPrint :: GTLSpec String -> String
simplePrettyPrint spec
  = unlines $ concat [
     [name ++ "{"]++
     (fmap ("  "++) (simplePrettyPrintBuchi (ltlToBuchi (gtlToLTL (gtlModelContract mdl)))))++
     ["}"]
  | (name,mdl) <- Map.toList $ gtlSpecModels spec ]

simplePrettyPrintBuchi :: GBuchi Integer (Set (GTLAtom String,Bool)) (Set Integer) -> [String]
simplePrettyPrintBuchi buchi = concat
                               [ [(if isStart co then "initial " else "")++"state "++show st++" {"]++
                                 [ "  "++(if p then "" else "not ") ++ show at | (at,p) <- Set.toList (vars co) ]++
                                 [ "  -> "++show succ | succ <- Set.toList (successors co) ]++
                                 [ "  final "++show f | f <- Set.toList (finalSets co) ] ++
                                 ["}"]
                               | (st,co) <- Map.toList buchi ]

-- | Get the bounding box of a preprocessed graph.
getDotBoundingBox :: DotGraph a -> Rect
getDotBoundingBox gr
  = case concat (fmap (\attr -> case attr of
                          GraphAttrs gattr -> mapMaybe (\rattr -> case rattr of
                                                           Bb rect -> Just rect
                                                           _ -> Nothing) gattr
                          _ -> []
                      ) (attrStmts (graphStatements gr))) of
      [] -> error "No bounding box defined"
      (x:xs) -> x

-- | Convert a Buchi automaton into a Dot graph.
buchiToDot :: GBuchi Integer (Set (GTLAtom String,Bool)) f -> DotGraph String
buchiToDot buchi
  = DotGraph { strictGraph = False
             , directedGraph = True
             , graphID = Nothing
             , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap RemoveOverlaps
                                                                    ,Splines SplineEdges
                                                                    ]]
                                          , subGraphs = []
                                          , nodeStmts = [ DotNode (nd i) [Shape Ellipse
                                                                         ,Label $ StrLabel $
                                                                          unlines [replicate (estimateWidth (if tr
                                                                                                             then at
                                                                                                             else gtlAtomNot at)) ' '
                                                                                  | (at,tr) <- Map.toList (vars st)]
                                                                         ,Comment $ "\\begin{array}{c}" ++
                                                                          (concat $ intersperse "\\\\" [ atomToLatex (if tr
                                                                                                                      then at
                                                                                                                      else gtlAtomNot at)
                                                                                                       | (at,tr) <- Set.toList (vars st)]) ++
                                                                          "\\end{array}"
                                                                         ,Height 0.5,Width 0.5,Margin (DVal 0)
                                                                         ]
                                                        | (i,st) <- Map.toList buchi
                                                        ] ++
                                                        [ DotNode "start" [Shape PointShape
                                                                          ]
                                                        ]
                                          ,edgeStmts = [ DotEdge { edgeFromNodeID = nd f
                                                                 , edgeToNodeID = nd t
                                                                 , directedEdge = True
                                                                 , edgeAttributes = []
                                                                 }
                                                       | (f,st) <- Map.toList buchi
                                                       , t <- Set.toList (successors st)
                                                       ] ++
                                                       [ DotEdge { edgeFromNodeID = "start"
                                                                 , edgeToNodeID = nd t
                                                                 , directedEdge = True
                                                                 , edgeAttributes = []
                                                                 }
                                                       | (t,st) <- Map.toList buchi
                                                       , isStart st
                                                       ]
                                          }
             }
  where nd x = "nd"++show x

-- | Convert a GTL specification to Tikz drawing commands.
--   This needs to be IO because it calls graphviz programs to preprocess the picture.
gtlToTikz :: GTLSpec String -> IO String
gtlToTikz spec = do
  mp <- mapM (\m -> do
                 (repr,w,h) <- modelToTikz m
                 return (gtlModelInput m,gtlModelOutput m,repr,w,h)
             ) (gtlSpecModels spec)
  let gr = DotGraph { strictGraph = False
                    , directedGraph = True
                    , graphID = Nothing
                    , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap RemoveOverlaps
                                                                           ,Splines SplineEdges]]
                                                 , subGraphs = []
                                                 , nodeStmts = [ DotNode name [Shape Record
                                                                              ,Label $ RecordLabel $ (if Map.null inp
                                                                                                      then []
                                                                                                      else [FlipFields [ LabelledTarget (PN name) name
                                                                                                                       | name <- Map.keys inp
                                                                                                                       ]])++
                                                                               [FieldLabel (unlines $
                                                                                            replicate (ceiling $ h / 20)
                                                                                            (replicate (ceiling $ w / 9) 'a')) -- XXX: There doesn't seem to be a way to specify the width of a nested field so we have to resort to this ugly hack
                                                                               ]++
                                                                               (if Map.null outp
                                                                                then []
                                                                                else [FlipFields [ LabelledTarget (PN name) name
                                                                                                 | name <- Map.keys outp
                                                                                                 ]
                                                                                     ])
                                                                              ]
                                                               | (name,(inp,outp,repr,w,h)) <- Map.toList mp
                                                               ]
                                                 , edgeStmts = [DotEdge { edgeFromNodeID = f
                                                                        , edgeToNodeID = t
                                                                        , directedEdge = True
                                                                        , edgeAttributes = [TailPort (LabelledPort (PN fv) (Just East))
                                                                                           ,HeadPort (LabelledPort (PN tv) (Just West))
                                                                                           ]
                                                                        }
                                                               | (f,fv,t,tv) <- gtlSpecConnections spec
                                                               ]
                                                 }
                    }
  outp <- readProcess "sfdp" ["-Tdot"] (printIt gr)
  let dot = parseIt' outp :: DotGraph String
  return $ dotToTikz (Just mp) dot

-- | Convert a single model into Tikz drawing commands.
--   Also returns the width and height of the bounding box for the rendered picture.
modelToTikz :: GTLModel String -> IO (String,Double,Double)
modelToTikz m = do
  let ltl = gtlToLTL (gtlModelContract m)
      buchi = ltlToBuchi ltl
  outp <- readProcess "sfdp" ["-Tdot"] (printIt $ buchiToDot buchi)
  let dot = parseIt' outp :: DotGraph String
      Rect _ (Point px py _ _) = getDotBoundingBox dot
      res = dotToTikz Nothing dot
  return (res,px,py)

-- | Helper function to render a graphviz point in Tikz.
pointToTikz :: Point -> String
pointToTikz pt = "("++show (xCoord pt)++"bp,"++show (yCoord pt)++"bp)"

-- | Convert a graphviz graph to Tikz drawing commands.
dotToTikz :: (Show a,Ord a)
             => Maybe (Map a (Map String TypeRep,Map String TypeRep,String,Double,Double)) -- ^ Can provide interfaces for the contained models if needed.
             -> DotGraph a
             -> String
dotToTikz mtp gr
  = unlines
    ([case shape of
         Ellipse -> "\\draw [color=blue!50,very thick,fill=blue!20]"++pointToTikz pos++" ellipse ("++show w++"bp and "++show h++"bp);\n" ++
                    "\\draw "++pointToTikz pos++" node {$"++lbl++"$};"
         Record -> unlines ([ "\\draw[color=red!50,fill=red!20,thick] "++pointToTikz p1++" -- "++pointToTikz (p1 { xCoord = xCoord p2 })++
                              " -- "++pointToTikz p2++" -- "++pointToTikz (p1 { yCoord = yCoord p2 })++
                              " -- "++pointToTikz p1++";"
                            | Rect p1 p2 <- rects
                            ]++
                            [ "\\draw ("++show ((xCoord p1 + xCoord p2)/2)++"bp,"++show ((yCoord p1 + yCoord p2)/2)++"bp) node {"++name++"};"
                            | (Rect p1 p2,name) <- zip rects (Map.keys inp)
                            ]++
                            [ "\\draw ("++show ((xCoord p1 + xCoord p2)/2)++"bp,"++show ((yCoord p1 + yCoord p2)/2)++"bp) node {"++name++"};"
                            | (Rect p1 p2,name) <- zip (drop ((Map.size inp)+1) rects) (Map.keys outp)
                            ]++
                            [ "\\begin{scope}[shift={("++show ((xCoord m1 + xCoord m2 - rw)/2)++"bp,"++show ((yCoord m1 + yCoord m2 - rh)/2)++"bp)}]\n"
                              ++repr++
                              "\\end{scope}"
                            ]
                           )
         PointShape -> "\\draw [fill]"++pointToTikz pos++" ellipse ("++show w++"bp and "++show h++"bp);"
     | nd <- nodeStmts (graphStatements gr)
     , let pos = case List.find (\attr -> case attr of
                                    Pos _ -> True
                                    _ -> False) (nodeAttributes nd) of
                   Just (Pos (PointPos p)) -> p
                   Nothing -> error $ "No position defined for node "++show (nodeID nd)
           h = case List.find (\attr -> case attr of
                                  Height _ -> True
                                  _ -> False) (nodeAttributes nd) of
                 Just (Height x) -> 36.0*x
                 _ -> error "No height given"
           w = case List.find (\attr -> case attr of
                                  Width _ -> True
                                  _ -> False) (nodeAttributes nd) of
                 Just (Width x) -> 36.0*x
                 _ -> error "No width given"
           lbl = case List.find (\attr -> case attr of
                                  Comment _ -> True
                                  _ -> False) (nodeAttributes nd) of
                 Just (Comment x) -> x
                 _ -> "none" --error "No label given"
           shape = case List.find (\attr -> case attr of
                         Shape _ -> True
                         _ -> False) (nodeAttributes nd) of
                     Just (Shape x) -> x
                     _ -> Ellipse --error "No shape given"
           rlbl = case List.find (\attr -> case attr of
                                  Label _ -> True
                                  _ -> False) (nodeAttributes nd) of
                    Just (Label (RecordLabel x)) -> x
                    _ -> error "No record label given"
           rects = case List.find (\attr -> case attr of
                                  Rects _ -> True
                                  _ -> False) (nodeAttributes nd) of
                    Just (Rects x) -> x
                    _ -> error "No rects given"
           Just reprs = mtp
           (inp,outp,repr,rw,rh) = reprs!(nodeID nd)
           Rect m1 m2 = head (drop (Map.size inp) rects)
     ] ++
     [ "\\draw [-,thick] "++pointToTikz spl1++" .. controls "
       ++pointToTikz spl2++" and "++pointToTikz spl3
       ++" .. "++pointToTikz spl4++";"
     | ed <- edgeStmts (graphStatements gr)
     , let Spline sp ep pts = case List.find (\attr -> case attr of
                                                 Pos _ -> True
                                                 _ -> False) (edgeAttributes ed) of
                                Just (Pos (SplinePos [spl])) -> spl
                                Nothing -> error "Edge has no position"
     , (spl1,spl2,spl3,spl4) <- splinePoints pts
     ]++
     [ "\\draw [-latex,thick] "++pointToTikz (last pts)++" -- "++pointToTikz rep++";"
     | ed <- edgeStmts (graphStatements gr)
     , let Spline sp ep pts = case List.find (\attr -> case attr of
                                                 Pos _ -> True
                                                 _ -> False) (edgeAttributes ed) of
                                Just (Pos (SplinePos [spl])) -> spl
                                Nothing -> error "Edge has no position"
     , rep <- case ep of
       Nothing -> []
       Just p -> [p]
     ])

-- | Convert a list of points into a spline by grouping them.
splinePoints :: [a] -> [(a,a,a,a)]
splinePoints (x:xs) = splinePoints' x xs
  where
    splinePoints' _ [] = []
    splinePoints' p (x:y:z:xs) = (p,x,y,z):splinePoints' z xs

-- | Render a GTL atom to LaTeX.
atomToLatex :: GTLAtom String -> String
atomToLatex (GTLRel rel lhs rhs) = (exprToLatex lhs)++(case rel of
                                                          BinLT -> "<"
                                                          BinLTEq -> "\\leq "
                                                          BinGT -> ">"
                                                          BinGTEq -> "\\geq "
                                                          BinEq -> "="
                                                          BinNEq -> "\neq ")++(exprToLatex rhs)
  where
    exprToLatex :: Expr String t -> String
    exprToLatex (ExprVar v h) = v++(if h==0 then "" else "["++show h++"]")
    exprToLatex (ExprConst x) = show x
    exprToLatex (ExprBinInt rel lhs rhs) = (exprToLatex lhs)++(case rel of
                                                                  OpPlus -> "+"
                                                                  OpMinus -> "-"
                                                                  OpMult -> "\\cdot "
                                                                  OpDiv -> "/")++(exprToLatex rhs)
atomToLatex (GTLElem v vals t) = "\\mathit{"++v++"}"++(if t then "" else "\\not")++"\\in"++show vals
atomToLatex (GTLVar v h t) = (if t then "" else "\\lnot ")++v++(if h==0 then "" else "["++show h++"]")

-- | Estimate the visible width of a LaTeX rendering of a GTL atom in characters.
estimateWidth :: GTLAtom String -> Int
estimateWidth (GTLRel _ lhs rhs) = 3+(estimateWidth' lhs)+(estimateWidth' rhs)
  where
    estimateWidth' :: Expr String t -> Int
    estimateWidth' (ExprVar v h) = (length v)+(if h==0 then 0 else 2+(length (show h)))
    estimateWidth' (ExprConst x) = length (show x)
    estimateWidth' (ExprBinInt _ lhs rhs) = (estimateWidth' lhs)+(estimateWidth' rhs)
estimateWidth (GTLElem v vals t) = (if t then 3 else 7)+(length v)+(length (show vals))
estimateWidth (GTLVar v h t) = (if t then 0 else 1)+(length v)+(if h==0 then 0 else 2+(length (show h)))

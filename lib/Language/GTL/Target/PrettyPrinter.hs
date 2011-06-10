{-# LANGUAGE GADTs #-}
{-| This module provides functions to render GTL specifications to Tikz Latex drawing commands.
    It can thus be used to get a pretty image for a GTL file.
 -}
module Language.GTL.Target.PrettyPrinter where

import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.LTL hiding (And)
import Language.GTL.Translation
import Language.GTL.Types
import Data.GraphViz hiding (Model)
import qualified Data.GraphViz as GV
import Data.GraphViz.Printing
import Data.GraphViz.Parsing
import Data.Maybe
import Data.Map as Map hiding (mapMaybe)
import Data.Set as Set
import Data.List as List
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Tree
import System.Process
import Data.Traversable
import Prelude hiding (mapM)

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

removeBreaks :: String -> String
removeBreaks ('\\':'\n':xs) = removeBreaks xs
removeBreaks (x:xs) = x:removeBreaks xs
removeBreaks [] = []

-- | Convert a Buchi automaton into a Dot graph.
buchiToDot :: GBuchi Integer (Set (TypedExpr String,Bool)) f -> DotGraph String
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
                                                                                                             else distributeNot at)) ' '
                                                                                  | (at,tr) <- Set.toList (vars st)]
                                                                         ,Comment $ "\\begin{array}{c}" ++
                                                                          (concat $ intersperse "\\\\" [ exprToLatex (if tr
                                                                                                                      then at
                                                                                                                      else distributeNot at)
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

generatePorts :: Bool -> Map String GTLType -> RecordFields
generatePorts left mp
  | Map.null mp = []
  | otherwise = [FlipFields
                 [ generateTypePorts name [] tp
                 | (name,tp) <- Map.toList mp ]
                ]
    where
      generateTypePorts :: String -> [Integer] -> GTLType -> RecordField
      generateTypePorts name pos (GTLArray sz tp) 
        = let f1 = FieldLabel (case pos of
                                  [] -> name
                                  x:xs -> show x)
              f2 = FlipFields [ generateTypePorts name (p:pos) tp
                              | p <- [0..(sz-1)] ]
          in FlipFields $ if left then [f2,f1] else [f1,f2]
      generateTypePorts name pos (GTLTuple tps)
        = let f1 = FieldLabel (case pos of
                                  [] -> name
                                  x:xs -> show x)
              f2 = FlipFields [ generateTypePorts name (p:pos) tp
                              | (p,tp) <- zip [0..] tps ]
          in FlipFields $ if left then [f2,f1] else [f1,f2]
      generateTypePorts name pos _ = LabelledTarget (PN $ genPortName name (reverse pos))
                                     (case pos of
                                         [] -> name
                                         x:xs -> show x)

-- | Convert a GTL specification to Tikz drawing commands.
--   This needs to be IO because it calls graphviz programs to preprocess the picture.
gtlToTikz :: GTLSpec String -> IO String
gtlToTikz spec = do
  mp <- mapM (\i -> do
                 let m = (gtlSpecModels spec)!(gtlInstanceModel i)
                 (repr,w,h) <- modelToTikz m
                 return (gtlModelInput m,gtlModelOutput m,repr,w,h)
             ) (gtlSpecInstances spec)
  let gr = DotGraph { strictGraph = False
                    , directedGraph = True
                    , graphID = Nothing
                    , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap RemoveOverlaps
                                                                           ,Splines SplineEdges
                                                                           ,GV.Model Circuit
                                                                           ,Epsilon 0.0000001
                                                                           ,ESep (DVal 0.1)
                                                                           ,MaxIter 10000
                                                                           ,Sep (DVal 0.1)
                                                                           ,Start (StartStyle RandomStyle)
                                                                           ]]
                                                 , subGraphs = []
                                                 , nodeStmts = [ DotNode name [Shape Record
                                                                              ,FontSize 10.0
                                                                              ,Label $ RecordLabel $ (generatePorts True inp)++
                                                                               [FieldLabel (unlines $
                                                                                            replicate (ceiling $ h / 12)
                                                                                            (replicate (ceiling $ w / 5.8) 'a')) -- XXX: There doesn't seem to be a way to specify the width of a nested field so we have to resort to this ugly hack
                                                                               ]++
                                                                               (generatePorts False outp)
                                                                              ]
                                                               | (name,(inp,outp,repr,w,h)) <- Map.toList mp
                                                               ]
                                                 , edgeStmts = [DotEdge { edgeFromNodeID = f
                                                                        , edgeToNodeID = t
                                                                        , directedEdge = True
                                                                        , edgeAttributes = [TailPort (LabelledPort (PN $ genPortName fv fi) (Just East))
                                                                                           ,HeadPort (LabelledPort (PN $ genPortName tv ti) (Just West))
                                                                                           ]
                                                                        }
                                                               | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- gtlSpecConnections spec
                                                               ]
                                                 }
                    }
  outp <- readProcess "fdp" ["-Tdot"] (printIt gr)
  let dot = parseIt' outp :: DotGraph String
  return $ dotToTikz (Just mp) dot

genPortName :: String -> [Integer] -> String
genPortName var ind = var ++ concat (fmap (\i -> "_"++show i) ind)

-- | Convert a single model into Tikz drawing commands.
--   Also returns the width and height of the bounding box for the rendered picture.
modelToTikz :: GTLModel String -> IO (String,Double,Double)
modelToTikz m = do
  let ltl = gtlToLTL (gtlModelContract m)
      buchi = ltlToBuchi distributeNot ltl
  outp <- readProcess "sfdp" ["-Tdot"] (printIt $ buchiToDot buchi)
  let dot = parseIt' outp :: DotGraph String
      Rect _ (Point px py _ _) = getDotBoundingBox dot
      res = dotToTikz Nothing dot
  return (res,px,py)

-- | Helper function to render a graphviz point in Tikz.
pointToTikz :: Point -> String
pointToTikz pt = "("++show (xCoord pt)++"bp,"++show (yCoord pt)++"bp)"

layoutRects :: Bool -> [Rect] -> [(String,GTLType)] -> ([String],[Rect])
layoutRects left rects [] = ([],rects)
layoutRects left rects ((name,tp):rest) = let (out,rbox) = layoutRectsType rects name [] tp
                                              (outs,res) = layoutRects left rbox rest
                                          in (out++outs,res)
  where
    drawLabel :: Rect -> String -> String
    drawLabel (Rect p1 p2) lbl = "\\draw ("++show ((xCoord p1 + xCoord p2)/2)++"bp,"++show ((yCoord p1 + yCoord p2)/2)++"bp) node {"++lbl++"};"
    
    layoutRectsType :: [Rect] -> String -> [Integer] -> GTLType -> ([String],[Rect])
    layoutRectsType (r1:rest) name pos (GTLArray sz tp)
      = let f q = foldl (\(strs,(r:rs)) i -> ((drawBox r):(drawLabel r (show i)):strs,rs)) q [0..(sz-1)]
            (mbox,(out,rects')) = if left 
                                  then (let (o,r2:r3) = f ([],(r1:rest)) in (r2,(o,r3)))
                                  else (r1,f ([],rest))
        in ((drawBox mbox):(drawLabel mbox (case pos of
                                               [] -> name
                                               x:xs -> show x)):out,rects')
    layoutRectsType (r1:rest) name pos (GTLTuple tps)
      = let f q = foldl (\(strs,(r:rs)) (i,tp) -> ((drawBox r):(drawLabel r (show i)):strs,rs)) q (zip [0..] tps)
            (mbox,(out,rects')) = if left 
                                  then (let (o,r2:r3) = f ([],(r1:rest)) in (r2,(o,r3)))
                                  else (r1,f ([],rest))
        in ((drawBox mbox):(drawLabel mbox (case pos of
                                               [] -> name
                                               x:xs -> show x)):out,rects')
    layoutRectsType (r1:rest) name pos _ = ([drawBox r1,drawLabel r1 (case pos of
                                                                         [] -> name
                                                                         x:xs -> show x)],rest)

drawBox :: Rect -> String
drawBox (Rect p1 p2) = "\\draw[color=red!50,fill=red!20,thick] "++pointToTikz p1++" -- "++pointToTikz (p1 { xCoord = xCoord p2 })++
                       " -- "++pointToTikz p2++" -- "++pointToTikz (p1 { yCoord = yCoord p2 })++
                       " -- "++pointToTikz p1++";"

-- | Convert a graphviz graph to Tikz drawing commands.
dotToTikz :: (Show a,Ord a)
             => Maybe (Map a (Map String GTLType,Map String GTLType,String,Double,Double)) -- ^ Can provide interfaces for the contained models if needed.
             -> DotGraph a
             -> String
dotToTikz mtp gr
  = unlines
    ([case shape of
         Ellipse -> "\\draw [color=blue!50,very thick,fill=blue!20]"++pointToTikz pos++" ellipse ("++show w++"bp and "++show h++"bp);\n" ++
                    "\\draw "++pointToTikz pos++" node {$"++lbl++"$};"
         Record -> let (out1,mrect@(Rect m1 m2):rect1) = layoutRects True rects (Map.toList inp)
                       (out2,rect2) = layoutRects False rect1 (Map.toList outp)
                   in unlines ([drawBox mrect]++out1++out2
                               ++[ "\\begin{scope}[shift={("++show ((xCoord m1 + xCoord m2 - rw)/2)++"bp,"++show ((yCoord m1 + yCoord m2 - rh)/2)++"bp)}]\n"
                                   ++repr++
                                   "\\end{scope}"
                                 ])
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
                 Just (Comment x) -> removeBreaks x
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
exprToLatex :: TypedExpr String -> String
exprToLatex expr = case getValue expr of
  BinRelExpr rel l r -> (exprToLatex $ unfix l)
                        ++(case rel of
                              BinLT -> "<"
                              BinLTEq -> "\\leq "
                              BinGT -> ">"
                              BinGTEq -> "\\geq "
                              BinEq -> "="
                              BinNEq -> "\neq ")
                        ++(exprToLatex $ unfix r)
  Var v h -> v++(if h==0 then "" else "["++show h++"]")
  Value v -> case v of
    GTLIntVal x -> show x
    GTLBoolVal x -> show x
    GTLEnumVal x -> "\\textrm{"++x++"}"
  BinIntExpr rel lhs rhs -> (exprToLatex $ unfix lhs)
                            ++(case rel of
                                  OpPlus -> "+"
                                  OpMinus -> "-"
                                  OpMult -> "\\cdot "
                                  OpDiv -> "/")
                            ++(exprToLatex $ unfix rhs)
  UnBoolExpr GTL.Not p -> "\\lnot "++(exprToLatex $ unfix p)
  IndexExpr expr idx -> exprToLatex (unfix expr) ++ "_{"++show idx++"}"

-- | Estimate the visible width of a LaTeX rendering of a GTL atom in characters.
estimateWidth :: TypedExpr String -> Int
estimateWidth expr = case getValue expr of
  BinRelExpr _ lhs rhs -> 3+(estimateWidth $ unfix lhs)+(estimateWidth $ unfix rhs)
  Var v h -> (length v)+(if h==0 then 0 else 2+(length (show h)))
  Value (GTLBoolVal x) -> length (show x)
  Value (GTLIntVal x) -> length (show x)
  Value (GTLEnumVal x) -> 1+(length x)
  Value (GTLArrayVal xs) -> 1+(length xs)+sum (fmap (estimateWidth.unfix) xs)
  Value (GTLTupleVal xs) -> 1+(length xs)+sum (fmap (estimateWidth.unfix) xs)
  BinIntExpr _ lhs rhs -> 1+(estimateWidth $ unfix lhs)+(estimateWidth $ unfix rhs)
  IndexExpr expr idx -> estimateWidth (unfix expr) + ((length (show idx) + 1) `div` 2)
  UnBoolExpr GTL.Not e -> 1 + (estimateWidth (unfix e))
  _ -> error $ "Internal error: Can't estimate width of expression "++show expr


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
import Data.GraphViz
import Data.GraphViz.Printing
import Data.GraphViz.Parsing
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.PreProcessing
import qualified Data.GraphViz.Attributes.HTML as GH
import qualified Data.Text.Lazy as T
import Data.Int (Int64)
import Data.Maybe
import Data.Map as Map hiding (mapMaybe, foldl)
import Data.Set as Set hiding (foldl)
import Data.List as List
import Data.Text.Lazy.Internal
import System.Process
import Data.Traversable
import Prelude hiding (mapM)
import Language.GTL.Buchi

-- | Get the bounding box of a preprocessed graph.
getDotBoundingBox :: DotGraph a -> Rect
getDotBoundingBox gr
  = case concat (fmap (\attr -> case attr of
                          GraphAttrs gattr -> mapMaybe (\rattr -> case rattr of
                                                           BoundingBox rect -> Just rect
                                                           _ -> Nothing) gattr
                          _ -> []
                      ) (attrStmts (graphStatements gr))) of
      [] -> error "No bounding box defined"
      (x:xs) -> x

removeBreaks :: Text -> Text
removeBreaks = T.replace (T.pack "\\n") Empty

-- | Convert a Buchi automaton into a Dot graph.
buchiToDot :: BA [TypedExpr String] Integer -> DotGraph String
buchiToDot buchi
  = DotGraph { strictGraph = False
             , directedGraph = True
             , graphID = Nothing
             , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap $ VpscOverlap
                                                                    ,Splines SplineEdges
                                                                    ]]
                                          , subGraphs = []
                                          , nodeStmts = [ DotNode (nd i) [Shape Ellipse
                                                                         ,Height 0.5,Width 0.5,Margin (DVal 0)
									                                              , textLabel $ Empty
									                                              , Comment $ T.pack (nd i)
                                                                         ]
                                                        | (i,st) <- Map.toList $ baTransitions buchi 
                                                        ] ++
                                                        [ DotNode "start" [Shape PointShape
										                                            , textLabel $ Empty
                                                                          ]
                                                        ]
                                          ,edgeStmts = [ DotEdge { fromNode = nd st
                                                                 , toNode = nd trg
                                                                 , edgeAttributes = [
                                                                 textLabel $ T.unlines [exprToLatex te | (te) <- cond]
                                                                 , Comment $ 
									                                          T.append 
										                                          (T.append 
											                                          (T.pack $ "\\begin{array}{c}")
									 		                                          (T.concat $ 
										 		                                          intersperse (T.pack "\\\\") (
													                                       [exprToLatex te | te <- cond])
											                                          )
										                                          ) 
										                                          (T.pack $ "\\end{array}")
                                                                 ]
                                                                 }
                                                       | (st,trans) <- Map.toList $ baTransitions buchi
                                                       , (cond,trg) <- trans
                                                       ] 
													                ++
                                                       [ DotEdge { fromNode = "start"
                                                                 , toNode = nd st
                                                                 , edgeAttributes = []
                                                                 }
                                                       | (st,trans) <- Map.toList $ baTransitions buchi
                                                       , Set.member st (baInits buchi)
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
      generateTypePorts name pos (Fix (GTLArray sz tp))
        = let f1 = FieldLabel (case pos of
                                  [] -> T.pack name
                                  x:xs -> T.pack $ show x)
              f2 = FlipFields [ generateTypePorts name (p:pos) tp
                              | p <- [0..(sz-1)] ]
          in FlipFields $ if left then [f2,f1] else [f1,f2]
      generateTypePorts name pos (Fix (GTLTuple tps))
        = let f1 = FieldLabel (case pos of
                                  [] -> T.pack name
                                  x:xs -> T.pack $ show x)
              f2 = FlipFields [ generateTypePorts name (p:pos) tp
                              | (p,tp) <- zip [0..] tps ]
          in FlipFields $ if left then [f2,f1] else [f1,f2]
      generateTypePorts name pos _ = LabelledTarget (PN $ genPortName name (reverse pos))
                                     (case pos of
                                         [] -> T.pack name
                                         x:xs -> T.pack $ show x)

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
                    , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap $ PrismOverlap Nothing
                                                                           ,Splines SplineEdges
                                                                           ,Model Circuit
                                                                           ,Epsilon 0.0000001
                                                                           ,ESep (DVal 0.1)
                                                                           ,MaxIter 10000
                                                                           ,Sep (DVal 0.5)
                                                                           ,Start (StartStyle RandomStyle)
                                                                           ]]
                                                 , subGraphs = []
                                                 , nodeStmts = [ DotNode name [Shape PlainText
                                                                              ,FontSize 10.0
                                                                              , Label $ HtmlLabel (genHRecordShape inp outp w h)
                                                                              ]
                                                               | (name,(inp,outp,repr,w,h)) <- Map.toList mp
                                                               ]
                                                 , edgeStmts = [DotEdge { fromNode = f
                                                                        , toNode = t
                                                                        , edgeAttributes = [TailPort (LabelledPort (PN $ T.pack fv) (Just East))
                                                                                           ,HeadPort (LabelledPort (PN $ T.pack tv) (Just West))
                                                                                           ]
                                                                        }
                                                               | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- gtlSpecConnections spec
                                                               ]
                                                 }
                    }
  outp <- fmap (\i -> T.pack i) (readProcess "dot" ["-Tdot"] (T.unpack $ printIt gr))
  let dot = parseIt' $ preProcess outp :: DotGraph String
  return $ dotToTikz (Just mp) dot

-- | Creates the hole record object with its ports
--   2nd and 3rd parameters are height and width
genHRecordShape :: (RealFrac a) => Map String GTLType -> Map String GTLType -> a -> a -> GH.Label
genHRecordShape inp outp w h = GH.Table $ GH.HTable { GH.tableFontAttrs = Nothing
  , GH.tableAttrs = [GH.Border 0, GH.CellBorder 1, GH.CellSpacing 0, GH.CellPadding 0]
  , GH.tableRows = [
    GH.Cells $ concat [
	   firstcell++
		[GH.LabelCell [GH.Border 1, 
                     GH.RowSpan $ fromIntegral rows, 
							GH.Height $ round h, 
							GH.Width $ round w] (GH.Text [GH.Str $ T.pack " "])]++
		[GH.LabelCell [GH.RowSpan $ fromIntegral rows] (
			if (Map.size outp) > 0 then 
			GH.Table GH.HTable {
			  GH.tableFontAttrs = Nothing
			, GH.tableAttrs = [GH.Border 0, GH.CellBorder 1, GH.CellSpacing 0, GH.CellPadding 0]
			, GH.tableRows = [
             GH.Cells [
	            GH.LabelCell [GH.Border 0, GH.Port $ PN {portName = T.pack name}] (GH.Text [GH.Str $ T.pack name])
	          ]
           | (name,_) <- Map.toList outp
           ]
			}
			else
			(GH.Text [GH.Str Empty])
		)]
	 ]
  ]++
  [
    GH.Cells [
	   GH.LabelCell [GH.Border 1, GH.Port $ PN {portName = T.pack name}] (GH.Text [GH.Str $ T.pack name])
	 ]
  | (name,_) <- Map.toList inpnd
  ]
  }
  where 
    rows = Map.size inp
    fel = if rows > 0 then fst $ Map.elemAt 0 inp else ""
    inpnd = Map.delete fel inp --  get list of inp without first el
    firstcell = if rows > 0 
	               then
	 	              [GH.LabelCell [GH.Border 1, GH.Port $ PN {portName = T.pack fel}] (GH.Text [GH.Str $ T.pack fel])]
                  else
						  []

genPortName :: String -> [Integer] -> Text
genPortName var ind = T.append (T.pack var) (T.concat (fmap (\i -> T.pack ("_"++show i)) ind))

-- | Convert a single model into Tikz drawing commands
--   Also returns the width and height of the bounding box for the rendered picture.
modelToTikz :: GTLModel String -> IO (String,Double,Double)
modelToTikz m = do
  let ltl = gtlToLTL Nothing (gtlContractExpression $ gtlModelContract m)
      buchi = ltl2ba ltl
  outp <- fmap (\i -> T.pack i) (readProcess "fdp" ["-Tdot"] (T.unpack $ printIt $ buchiToDot buchi))
  let dot = parseIt' $ preProcess outp :: DotGraph String
      Rect _ (Point px py _ _) = getDotBoundingBox dot
      res = dotToTikz Nothing dot
  return (res,px*2.5,py*2.0)

-- | Helper function to render a graphviz point in Tikz.
pointToTikz :: Point -> String
pointToTikz pt = "("++show (xCoord pt)++"bp,"++show (yCoord pt)++"bp)"

pointToTikzAdd :: Point -> Double -> Double -> String
pointToTikzAdd pt x y = "("++show ((xCoord pt) + x)++"bp,"++show ((yCoord pt) +y)++"bp)"

getrecnames :: [(String, GTLType)] -> String
getrecnames vars = "{" ++ (list vars) ++ "}"
	where
		list :: [(String, GTLType)] -> String
		list [] = ""
		list ((name,tp):[]) = name
		list ((name,tp):rest) = name ++ "," ++ (list rest)

layoutRects :: Bool -> [Rect] -> [(String,GTLType)] -> ([String],[Rect])
layoutRects left rects [] = ([],rects)
layoutRects left rects ((name,tp):rest) = let (out,rbox) = layoutRectsType rects name [] tp
                                              (outs,res) = layoutRects left rbox rest
                                          in (out++outs,res)
  where
    drawLabel :: Rect -> String -> String
    drawLabel (Rect p1 p2) lbl = "\\draw ("++show ((xCoord p1 + xCoord p2)/2)++"bp,"++show ((yCoord p1 + yCoord p2)/2)++"bp) node {"++lbl++"}; "
    layoutRectsType :: [Rect] -> String -> [Integer] -> GTLType -> ([String],[Rect])
    layoutRectsType (r1:rest) name pos (Fix (GTLArray sz tp))
      = let f q = foldl (\(strs,(r:rs)) i -> ((drawBox r):(drawLabel r (show i)):strs,rs)) q [0..(sz-1)]
            (mbox,(out,rects')) = if left
                                  then (let (o,r2:r3) = f ([],(r1:rest)) in (r2,(o,r3)))
                                  else (r1,f ([],rest))
        in ((drawBox mbox):(drawLabel mbox (case pos of
                                               [] -> name
                                               x:xs -> show x)):out,rects')
    layoutRectsType (r1:rest) name pos (Fix (GTLTuple tps))
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
                       " -- "++pointToTikz p1++"; "

genConnectPortName:: (PrintDot a) => a -> Text -> String
genConnectPortName rec port = (genNodeID rec) ++ (T.unpack port)

genNodeID:: (PrintDot a) => a -> String
genNodeID nd = (T.unpack $ printIt nd)

ndToTikz :: (Show a,Ord a) => DotNode a ->
             Maybe (Map a (Map String GTLType,Map String GTLType,String,Double,Double)) -- ^ Can provide interfaces for the contained models if needed.
             -> String
ndToTikz nd mtp = concat [
                           "\\node at "++ (pointToTikzAdd pos (-1 * ((w/2.0))) ((-inph * (idx name inp))+(h/2.0)))  ++
                           " [draw,anchor=north west,name="++ name ++",rectangle, minimum width="++ 
                           (show inpw) ++"bp,minimum height="++ (show inph) ++"bp,transform shape] {"++name++"};"
                        | (name,_) <- Map.toList inp
                        ]++
                        concat [
                           "\\node at "++ (pointToTikzAdd pos ((w/2.0)-outpw) ((-outph * (idx name outp))+(h/2.0)))  ++
                           " [draw,anchor=north west,name="++ name ++",rectangle, minimum width="++ 
                           (show outpw) ++"bp,minimum height="++ (show outph) ++"bp,transform shape] {"++name++"};"
                        | (name,_) <- Map.toList outp
                        ]++
                        "\\node at "++ (pointToTikz pos)  ++" [draw,name="++ (show $ nodeID nd) ++",rectangle, minimum width="++ 
                        (show w) ++"bp,minimum height="++ (show h) ++"bp,transform shape] {};"
                        ++ unlines (
                              [ "\\node at " ++ pointToTikzAdd pos inpw 0.0 ++ " [name=auto"++(show $ nodeID nd)++"] {" ++
                              "\\begin{tikzpicture}\n"
                              ++repr++
                              "\\end{tikzpicture}"
                              ]) ++ "};"
  where 
      pos = case List.find (\attr -> case attr of
                            Pos _ -> True
                            _ -> False) (nodeAttributes nd) of
               Just (Pos (PointPos p)) -> p
               Nothing -> error $ "No position defined for node "++show (nodeID nd)
      h = case List.find (\attr -> case attr of
                          Height _ -> True
                          _ -> False) (nodeAttributes nd) of
               Just (Height x) -> 64.0*x
               _ -> error "No height given"
      w = case List.find (\attr -> case attr of
                          Width _ -> True
                          _ -> False) (nodeAttributes nd) of
               Just (Width x) -> 64.0*x
               _ -> error "No width given"
      outpEmpty = Map.null outp
      inpEmpty = Map.null inp
      inph = if inpEmpty then 0.0 else (h / fromIntegral (Map.size inp))
      outph = if outpEmpty then 0.0 else h / fromIntegral (Map.size outp)
      inpw = if inpEmpty then 0.0 else fromIntegral (maximum $ Prelude.map length (Map.keys inp))*15.0
      outpw = if outpEmpty then 0.0 else fromIntegral (maximum $ Prelude.map length (Map.keys outp))*15.0
      idx k l = fromIntegral $ Map.findIndex k l 
      Just reprs = mtp
      (inp,outp,repr,rw,rh) = reprs!(nodeID nd)

-- | Convert a graphviz graph to Tikz drawing commands.
dotToTikz :: (Show a,Ord a)
             => Maybe (Map a (Map String GTLType,Map String GTLType,String,Double,Double)) -- ^ Can provide interfaces for the contained models if needed.
             -> DotGraph a
             -> String
dotToTikz mtp gr
  = unlines
    ([case shape of
         Ellipse -> "\\draw [color=blue!50,very thick,fill=blue!20]"++pointToTikz pos++" ellipse ("++show w++"bp and "++show h++"bp);\n" ++
                    "\\draw "++pointToTikz pos++" node {};"
         PlainText -> (ndToTikz nd mtp) 
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
                 Just (Height x) -> 32.0*x
                 _ -> error "No height given"
           w = case List.find (\attr -> case attr of
                                  Width _ -> True
                                  _ -> False) (nodeAttributes nd) of
                 Just (Width x) -> 32.0*x
                 _ -> error "No width given"
           shape = case List.find (\attr -> case attr of
                         Shape _ -> True
                         _ -> False) (nodeAttributes nd) of
                     Just (Shape x) -> x
                     _ -> error "No shape given"
     ] ++
     [ unlines ["\\draw [-,thick] "++pointToTikz spl1++ ".. controls "++pointToTikz spl2++
	 " and "++pointToTikz spl3 ++" .. "++pointToTikz spl4++";"
	 | (spl1,spl2,spl3,spl4) <- splinePoints pts
	 ] ++ label
     | ed <- edgeStmts (graphStatements gr)
     , let Spline sp ep pts = case List.find (\attr -> case attr of
                                                 Pos _ -> True
                                                 _ -> False) (edgeAttributes ed) of
                                Just (Pos (SplinePos [spl])) -> spl
                                Nothing -> error "Edge has no position"
           lbl = case List.find (\attr -> case attr of
                                  Comment _ -> True
                                  _ -> False) (edgeAttributes ed) of
                 Just (Comment x) -> removeBreaks x
                 _ -> Empty
           label = case List.find (\attr -> case attr of
                                  LPos _ -> True
                                  _ -> False) (edgeAttributes ed) of
                 Just (LPos p) -> "\\draw "++pointToTikz p++" node {$"++(T.unpack lbl)++"$};"
                 Nothing -> ""
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
exprToLatex :: TypedExpr String -> T.Text
exprToLatex expr = case getValue $ unfix expr of
	BinRelExpr rel l r -> T.append (exprToLatex l)
                         (T.append
						  (T.pack (case rel of
                              BinLT -> "< "
                              BinLTEq -> "\\leq "
                              BinGT -> ">"
                              BinGTEq -> "\\geq "
                              BinEq -> "="
                              BinNEq -> "\\neq "                 -- bug displayed as 'eq' not \neq (mayby \\n is the problem)
                              BinAssign -> ":="))
                          (exprToLatex r)
						 )
	Var v h _ -> T.pack (v++(if h==0 then "" else "["++show h++"]"))
	Value v -> T.pack (case v of
		GTLIntVal x -> show x
		GTLBoolVal x -> show x
		GTLEnumVal x -> "\\textrm{"++x++"}")
	BinIntExpr rel lhs rhs -> T.append (exprToLatex lhs)
							(T.append 
							  (T.pack (case rel of
								OpPlus -> "+"
								OpMinus -> "-"
								OpMult -> "\\cdot "
								OpDiv -> "/"))
							 (exprToLatex rhs)
							)
	UnBoolExpr GTL.Not p -> T.append (T.pack "\\lnot ") (exprToLatex p)
	IndexExpr expr idx -> T.append (exprToLatex expr) (T.pack $ " \\lbrace "++show idx++" \\rbrace ")
	ClockRef clk -> T.pack ("clock("++(show clk)++")")
	ClockReset clk limit -> T.pack ("clock("++(show clk)++") := "++(show limit))

-- | convert int to int64
int2Int64 :: Int -> Int64
int2Int64 i = fromInteger $ toInteger i

-- | Estimate the visible width of a LaTeX rendering of a GTL atom in characters.
estimateWidth :: TypedExpr String -> Int64
estimateWidth expr = case getValue $ unfix expr of
  BinRelExpr _ lhs rhs -> 3+(estimateWidth lhs)+(estimateWidth rhs)
  Var v h _ -> int2Int64 $ (length v)+(if h==0 then 0 else 2+(length $ show h))
  Value (GTLBoolVal x) -> int2Int64 $ length (show x)
  Value (GTLIntVal x) -> int2Int64 $ length (show x)
  Value (GTLEnumVal x) -> 1+(int2Int64 $ length x)
  Value (GTLArrayVal xs) -> 1+(int2Int64 $ length xs)+sum (fmap (estimateWidth) xs)
  Value (GTLTupleVal xs) -> 1+(int2Int64 $ length xs)+sum (fmap (estimateWidth) xs)
  BinIntExpr _ lhs rhs -> 1+(estimateWidth lhs)+(estimateWidth rhs)
  IndexExpr expr idx -> (estimateWidth expr) + ((int2Int64 $ length (show idx) + 1) `div` 2)
  UnBoolExpr GTL.Not e -> 1 + (estimateWidth e)
  _ -> error $ "Internal error: Can't estimate width of expression " ++ show expr


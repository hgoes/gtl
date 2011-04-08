{-# LANGUAGE GADTs #-}
module Language.GTL.PrettyPrinter where

import Language.GTL.Syntax
import Language.GTL.LTL hiding (And)
import Language.GTL.Translation
import Language.GTL.ScadeAnalyzer
import qualified Language.Scade.Syntax as Sc
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

buchiGraphParams :: GraphvizParams (Map (GTLAtom String) Bool) () () (Map (GTLAtom String) Bool)
buchiGraphParams = Params
  { isDirected = True
  , globalAttributes = [GraphAttrs [Overlap RemoveOverlaps]]
  , clusterBy = N
  , clusterID = const Nothing
  , fmtCluster = const []
  , fmtNode = \(i,mp) -> [Height 0,Width 0,Margin (DVal 0)
                         ,Label $ StrLabel $ replicate (sum [estimateWidth at
                                                            | (at,tr) <- Map.toList mp]) ' '
                         ,Comment $ concat $ intersperse " " [ atomToLatex at
                                                             | (at,tr) <- Map.toList mp]]
  , fmtEdge = \(i,s,()) -> []
  }

buchiToGraph :: GBuchi Integer a f -> Gr a ()
buchiToGraph buchi = mkGraph 
                     [ (fromInteger i,vars st)
                     | (i,st) <- Map.toList buchi
                     ]
                     [ (fromInteger i,fromInteger s,())
                     | (i,st) <- Map.toList buchi
                     , s <- Set.toList (successors st)
                     ]

gtlToTikz gtl scade = declsToTikz gtl (typeMap gtl scade)

declsToTikz :: [Declaration] -> TypeMap -> IO String
declsToTikz decls tps = do
  let models = [ m | Model m <- decls ]
      connections = [ c | Connect c <- decls ]
  mp <- fmap Map.fromList $ mapM (\m -> do
                                     (repr,w,h) <- modelToTikz m
                                     return (modelName m,(repr,w,h))) models
  let gr = DotGraph { strictGraph = False
                    , directedGraph = True
                    , graphID = Nothing
                    , graphStatements = DotStmts { attrStmts = [GraphAttrs [Overlap RemoveOverlaps]]
                                                 , subGraphs = []
                                                 , nodeStmts = [ DotNode name [Shape Record
                                                                              ,Label $ RecordLabel $ (if Map.null inp
                                                                                                      then []
                                                                                                      else [FlipFields [ LabelledTarget (PN name) name
                                                                                                                       | name <- Map.keys inp
                                                                                                                       ]])++
                                                                               [FieldLabel (unlines $
                                                                                            replicate (round $ h / 20)
                                                                                            (replicate (round $ w / 9) 'a')) -- XXX: There doesn't seem to be a way to specify the width of a nested field so we have to resort to this ugly hack
                                                                               ]++
                                                                               (if Map.null outp
                                                                                then []
                                                                                else [FlipFields [ LabelledTarget (PN name) name
                                                                                                 | name <- Map.keys outp
                                                                                                 ]
                                                                                     ])
                                                                              ]
                                                               | (name,(repr,w,h)) <- Map.toList mp
                                                               , let (_,inp,outp) = tps!name
                                                               ]
                                                 , edgeStmts = [DotEdge { edgeFromNodeID = connectFromModel conn
                                                                        , edgeToNodeID = connectToModel conn
                                                                        , directedEdge = True
                                                                        , edgeAttributes = [TailPort (LabelledPort (PN $ connectFromVariable conn) (Just East))
                                                                                           ,HeadPort (LabelledPort (PN $ connectToVariable conn) (Just West))
                                                                                           ]
                                                                        }
                                                               | conn <- connections
                                                               ]
                                                 }
                    }
  outp <- readProcess "sfdp" ["-Tdot","/dev/stdin"] (printIt gr)
  let dot = parseIt' outp :: DotGraph String
  return $ dotToTikz (Just (tps,mp)) dot

modelToTikz :: ModelDecl -> IO (String,Double,Double)
modelToTikz m = do
  let rcontr = foldl1 (ExprBinBool And) (modelContract m)
      ltl = gtlToLTL rcontr
      buchi = ltlToBuchi ltl
  buchiToTikz buchi

buchiToTikz :: GBuchi Integer (Map (GTLAtom String) Bool) f -> IO (String,Double,Double)
buchiToTikz buchi = do
  outp <- readProcess "neato" ["-Tdot","/dev/stdin"] (printIt $ graphToDot buchiGraphParams (buchiToGraph buchi))
  let dot = parseIt' outp :: DotGraph Node
      Rect _ (Point px py _ _) = getDotBoundingBox dot
      res = dotToTikz Nothing dot
  return (res,px,py)
  
pointToTikz :: Point -> String
pointToTikz pt = "("++show (xCoord pt)++"bp,"++show (yCoord pt)++"bp)"

dotToTikz :: (Show a,Ord a) => Maybe (Map a (String,Map String Sc.TypeExpr,Map String Sc.TypeExpr),Map a (String,Double,Double)) -> DotGraph a -> String
dotToTikz mtp gr
  = unlines
    ([case shape of
         Ellipse -> "\\draw "++pointToTikz pos++" ellipse ("++show w++"bp and "++show h++"bp);\n" ++
                    "\\draw "++pointToTikz pos++" node {$"++lbl++"$};"
         Record -> unlines ([ "\\draw "++pointToTikz p1++" -- "++pointToTikz (p1 { xCoord = xCoord p2 })++
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
                 _ -> error "No label given"
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
           Just (rtp,reprs) = mtp
           (_,inp,outp) = rtp!(nodeID nd)
           (repr,rw,rh) = reprs!(nodeID nd)
           Rect m1 m2 = head (drop (Map.size inp) rects)
     ] ++
     [ "\\draw [-] "++pointToTikz spl1++" .. controls "
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
     [ "\\draw [->] "++pointToTikz (last pts)++" -- "++pointToTikz rep++";"
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
    
splinePoints :: [a] -> [(a,a,a,a)]
splinePoints (x:xs) = splinePoints' x xs
  where
    splinePoints' _ [] = []
    splinePoints' p (x:y:z:xs) = (p,x,y,z):splinePoints' z xs

atomToLatex :: GTLAtom String -> String 
atomToLatex (GTLRel rel lhs rhs) = (exprToLatex lhs)++(case rel of
                                                          BinLT -> "<"
                                                          BinLTEq -> "\\leq "
                                                          BinGT -> ">"
                                                          BinGTEq -> "\\geq "
                                                          BinEq -> "="
                                                          BinNEq -> "\neq ")++(exprToLatex rhs)
  where
    exprToLatex :: Expr String Int -> String
    exprToLatex (ExprVar v h) = v++(if h==0 then "" else "["++show h++"]")
    exprToLatex (ExprConst x) = show x
    exprToLatex (ExprBinInt rel lhs rhs) = (exprToLatex lhs)++(case rel of
                                                                  OpPlus -> "+"
                                                                  OpMinus -> "-"
                                                                  OpMult -> "\\cdot "
                                                                  OpDiv -> "/")++(exprToLatex rhs)
atomToLatex (GTLElem v vals t) = "\\mathit{"++v++"}"++(if t then "" else "\\not")++"\\in"++show vals
atomToLatex (GTLVar v h t) = (if t then "" else "\\lnot ")++v++(if h==0 then "" else "["++show h++"]")

estimateWidth :: GTLAtom String -> Int
estimateWidth (GTLRel _ lhs rhs) = 3+(estimateWidth' lhs)+(estimateWidth' rhs)
  where
    estimateWidth' :: Expr String Int -> Int
    estimateWidth' (ExprVar v h) = (length v)+(if h==0 then 0 else 2+(length (show h)))
    estimateWidth' (ExprConst x) = length (show x)
    estimateWidth' (ExprBinInt _ lhs rhs) = (estimateWidth' lhs)+(estimateWidth' rhs)
estimateWidth (GTLElem v vals t) = (if t then 3 else 7)+(length v)+(length (show vals))
estimateWidth (GTLVar v h t) = (if t then 0 else 1)+(length v)+(if h==0 then 0 else 2+(length (show h)))
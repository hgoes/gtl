module Language.GTL.PromelaContract where

import Data.Set as Set
import Data.Map as Map
import Language.GTL.Translation
import qualified Language.Promela.Syntax as Pr
import qualified Language.Scade.Syntax as Sc
import Data.BDD
import Data.BDD.Integer
import Data.BDD.Sets
import Data.Foldable
import Prelude hiding (foldl,concat)
import Language.GTL.Syntax
import Language.GTL.ScadeAnalyzer
import Data.Maybe (catMaybes)

import Debug.Trace

conditionBDD :: Monad m => Condition -> BDDM s Int m (Tree s Int)
conditionBDD (CondLT x)     = encodeSignedRange 0 (minBound::Int) (fromIntegral x - 1)
conditionBDD (CondLTEq x)   = encodeSignedRange 0 (minBound::Int) (fromIntegral x)
conditionBDD (CondGT x)     = encodeSignedRange 0 (fromIntegral x + 1) (maxBound::Int)
conditionBDD (CondGTEq x)   = encodeSignedRange 0 (fromIntegral x) (maxBound::Int)
conditionBDD (CondElem xs)  = encodeSet 0 (Set.fromList $ fmap fromIntegral xs :: Set Int)
conditionBDD (CondNElem xs) = encodeSet 0 (Set.fromList $ fmap fromIntegral xs :: Set Int) >>= not'

conditionsBDD :: Monad m => Set Condition -> BDDM s Int m (Tree s Int)
conditionsBDD xs = mapM conditionBDD (Set.toList xs) >>= and'

type VarMap = Map String Bool
type BDDFormula s = CanonFormulaT (Tree s Int)

canonBDD :: Monad m => CanonFormula -> BDDM s Int m (BDDFormula s)
canonBDD formula = mapM (\cl -> do
                            nvars <- mapM (\(k,cond) -> do 
                                              ncond <- conditionsBDD cond
                                              return (k,ncond))
                                     (Map.toAscList (clauseVars cl))
                            nnext <- canonBDD (clauseNext cl)                         
                            nalw <- canonBDD (clauseAlways cl)
                            return $ ClauseT
                                    { clauseVars = Map.fromAscList nvars
                                    , clauseNext = nnext
                                    , clauseAlways = nalw
                                    }
                        ) (Set.toList formula)
                   >>= return.(Set.fromList)

type StateMachine s = Map Integer (Set (Map String (Tree s Int),Integer))
type StateCache s = Map (BDDFormula s) Integer
{-
type InOutBDD s = Map String (Map String (Set (Tree s Int)),Map String (Set (Tree s Int)))
type DecisionTable s = Map (Tree s Int,Tree s Int) Compatibility
type ConnectionMap = (Map String (Map String [Integer]),Map Integer (String,String,String,String),Integer)
type IncomingBDD s = Map String (Map String (Set (Tree s Int)))-}

translateContracts :: [Sc.Declaration] -> [Declaration] -> [Pr.Module]
translateContracts scade decls
  = runIdBDDM $ do
    prog <- buildTransProgram scade decls
    translateContracts' prog

translateContracts' :: Monad m => TransProgram s -> BDDM s Int m [Pr.Module]
translateContracts' prog
  = do
    let decls = Pr.Decl $ Pr.Declaration Nothing Pr.TypeInt [("conn_"++name++"_"++var,Nothing,Nothing) | (name,mdl) <- Map.toList prog,(var,_) <- Map.toList (incVars mdl) ]
    mapM (\(name,mdl) -> do
             do_stps <- mapM (\(st,follows) -> do
                                 if_stps <- mapM (getIfSteps name mdl) (Set.toList follows)
                                 return $ [ Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr Pr.BinEquals
                                                        (Pr.RefExpr $ Pr.VarRef "state" Nothing Nothing)
                                                         (Pr.ConstExpr $ Pr.ConstInt st)
                                                       ) Nothing,
                                            Pr.StepStmt (Pr.StmtIf if_stps) Nothing
                                          ]
                             ) (Map.toList (stateMachine mdl))
             return $ Pr.ProcType 
               { Pr.proctypeActive = Just Nothing -- active without priority
               , Pr.proctypeName = name
               , Pr.proctypeArguments = []
               , Pr.proctypePriority = Nothing
               , Pr.proctypeProvided = Nothing
               , Pr.proctypeSteps = [Pr.StepDecl $ Pr.Declaration Nothing Pr.TypeInt [("state",Nothing,Nothing)],
                                     Pr.StepStmt (Pr.StmtDo do_stps) Nothing ]
               }
         ) (Map.toList prog) >>= return.(decls:)
    where
      getIfSteps name mdl (cond,follow) = do
        cond_stps <- mapM (getConds name mdl) (Map.toList cond)
        return $ (concat cond_stps) ++ [ Pr.StepStmt (Pr.StmtAssign (Pr.VarRef "state" Nothing Nothing)
                                                      (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral follow)) Nothing
                                       ]
      getConds name mdl (var,tree) = case Map.lookup var (incVars mdl) of
        Nothing -> case Map.lookup var (outVars mdl) of
          Nothing -> return []
          Just ns -> return [ Pr.StepStmt (Pr.StmtAssign
                                           (Pr.VarRef ("conn_"++mname++"_"++var) Nothing Nothing)
                                           (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral (nodeHash tree))) Nothing
                            | (mname,var) <- ns ]
        Just inc -> mapM (\i -> do
                             nv <- i #=> tree
                             t <- true
                             f <- false
                             if nv == t
                               then return $ Just $ checkVar Pr.BinEquals name var i
                               else (do
                                        nv <- i #&& tree
                                        if nv == f
                                          then return $ Just $ checkVar Pr.BinNotEquals name var i
                                          else traceShow nv $ return Nothing)
                         ) (Set.toList inc) >>= return.catMaybes
      checkVar op name var i = Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr op
                                            (Pr.RefExpr (Pr.VarRef ("conn_"++name++"_"++var) Nothing Nothing))
                                            (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral $ nodeHash i)
                                           ) Nothing

data TransModel s = TransModel
                    { incVars :: Map String (Set (Tree s Int))
                    , outVars :: Map String [(String,String)]
                    , stateMachine :: StateMachine s
                    }
                    deriving Show

type TransProgram s = Map String (TransModel s)

bddsForVar :: StateMachine s -> String -> Set (Tree s Int)
bddsForVar machine var = Set.fromList $ catMaybes [ Map.lookup var trans | (_,transs) <- Map.toList machine, (trans,_) <- Set.toList transs ]

buildTransProgram :: Monad m => [Sc.Declaration] -> [Declaration] -> BDDM s Int m (TransProgram s)
buildTransProgram scade decls
  = do
    prog <- mapM (\m -> do
                     traceShow (translateContract (modelContract m)) $ return ()
                     bdd <- canonBDD $ translateContract (modelContract m)
                     st <- buildST bdd
                     return (modelName m,TransModel { incVars = Map.empty 
                                                    , outVars = Map.empty
                                                    , stateMachine = st
                                                    })
                 ) models >>= return.(Map.fromList)
    return $ foldl (\cprog c -> let fromMdl = cprog!(connectFromModel c)
                                    nprog1 = Map.adjust
                                             (\mdl -> mdl { incVars = Map.insertWith Set.union
                                                                      (connectToVariable c)
                                                                      (bddsForVar (stateMachine fromMdl) (connectFromVariable c))
                                                                      (incVars mdl)
                                                          }) (connectToModel c) cprog
                                    nprog2 = Map.adjust
                                             (\mdl -> mdl { outVars = Map.insertWith (++)
                                                                      (connectFromVariable c)
                                                                      [(connectToModel c,connectToVariable c)]
                                                                      (outVars mdl)
                                                          }) (connectFromModel c) nprog1
                                    in nprog2
                   ) prog conns
  where
    models = [ m | Model m <- decls ]
    conns = [ c | Connect c <- decls ]
{-
test :: Formula -> String
test f = runIdBDDM (do
                       bf <- canonBDD (translateFormula f)
                       st <- buildST bf
                       return $ renderST st)

renderST :: StateMachine s -> String
renderST st = unlines [ unlines $ ["State "++show k] ++ [ "  " ++ show (Map.keys mp) ++ " -> "++show nxt | (mp,nxt) <- Set.toList v ]
                      | (k,v) <- Map.toList st ]

data Compatibility = Compatible
                   | Incompatible
                   | Undecidable
                   deriving Show

translateContracts :: [Sc.Declaration] -> [Declaration] -> [Pr.Module]
translateContracts scade decls
  = runIdBDDM $ do
    machines <- mapM (\m -> do
                         bdd <- canonBDD $ translateContract (modelContract m)
                         st <- buildST bdd
                         return (modelName m,st)
                     ) models >>= return.(Map.fromList)
    let tp = typeMap decls scade
        bdds = possibleBDDs tp machines
        connmap = connectionMap conns
    decision <- buildDecisionTable bdds conns
    return $ translateContracts' connmap machines bdds decision
  where 
    models = [ m | Model m <- decls ]
    conns = [ c | Connect c <- decls ]

translateContracts' :: ConnectionMap -> Map String (StateMachine s) -> InOutBDD s -> DecisionTable s -> [Pr.Module]
translateContracts' (conns,conns_inv,count_conns) machines bdds decs
  = [ Pr.Decl $ Pr.Declaration Nothing Pr.TypeInt [("conn"++show n,Nothing,Nothing) | n <- [0..count_conns-1]]
    ]++
    [ Pr.ProcType
      { Pr.proctypeActive = Just Nothing -- active without priority
      , Pr.proctypeName = name
      , Pr.proctypeArguments = []
      , Pr.proctypePriority = Nothing
      , Pr.proctypeProvided = Nothing
      , Pr.proctypeSteps = [Pr.StepDecl $ Pr.Declaration Nothing Pr.TypeInt [("state",Nothing,Nothing)]]++
                           [Pr.StepStmt (Pr.StmtDo
                                         [ [Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr Pr.BinEquals
                                                         (Pr.RefExpr $ Pr.VarRef "state" Nothing Nothing)
                                                         (Pr.ConstExpr $ Pr.ConstInt st)
                                                        ) Nothing,
                                            Pr.StepStmt (Pr.StmtIf
                                                         [ [ 
                                                           | (var,tree) <- Map.toList cond ]
                                                         | (cond,follow) <- Set.toList follows]
                                                        ) Nothing
                                           ]
                                         | (st,follows) <- Map.toList machine
                                         ]) Nothing
                           ]
      }
    | (name,machine) <- Map.toList machines ]

connectionMap :: [ConnectDecl] -> ConnectionMap
connectionMap = build 0 Map.empty
  where
    build n (mp1,mp2) [] = (mp1,mp2,n)
    build n (mp1,mp2) (c:cs) = build (n+1) (put (connectFromModel c) (connectFromVariable c) n $
                                            put (connectToModel c) (connectToVariable c) n mp1,
                                            Map.insert n (connectFromModel c,connectFromVariable c,
                                                          connectToModel c,connectToVariable c) mp2
                                           ) cs
    put model var n mp = Map.alter (\sm -> Just $ case sm of
                                       Nothing -> Map.singleton var [n]
                                       Just sm' -> Map.alter (\nm -> Just $ case nm of
                                                                 Nothing -> [n]
                                                                 Just nm' -> (n:nm')
                                                             ) var sm'
                                   ) model mp

incomingBDDs :: InOutBDD s -> ConnectionMap -> IncomingBDD s
incomingBDDs iot (conns,conns_inv,_) = foldM (\

buildDecisionTable :: Monad m => InOutBDD s -> [ConnectDecl] -> BDDM s Int m (DecisionTable s)
buildDecisionTable bdds = foldlM (\mp c -> do
                                     let (_,outs) = bdds!(connectFromModel c)
                                         (inps,_) = bdds!(connectToModel c)
                                         out = outs!(connectFromVariable c)
                                         inp = inps!(connectToVariable c)
                                     foldlM (\mp' (l,r) -> if Map.member (l,r) mp' 
                                                           then return mp'
                                                           else (do
                                                                    tree <- l #=> r
                                                                    t <- true
                                                                    f <- false
                                                                    return $ Map.insert (l,r) (if tree == t
                                                                                               then Compatible
                                                                                               else (if tree == f
                                                                                                     then Incompatible
                                                                                                     else Undecidable)
                                                                                              ) mp'
                                                                )
                                            ) mp [ (l,r) | l <- Set.toList out, r <- Set.toList inp ]
                                 ) Map.empty

possibleBDDs :: TypeMap -> Map String (StateMachine s) -> InOutBDD s
possibleBDDs tps models = Map.mapWithKey (\name stm -> let (mdl_name,inp,outp) = tps!name 
                                                           trees = possibleBDDs' stm
                                                       in (Map.mapWithKey (\var tp -> trees!var) inp, 
                                                           Map.mapWithKey (\var tp -> trees!var) outp)) models

possibleBDDs' :: StateMachine s -> Map String (Set (Tree s Int))
possibleBDDs' = foldl (\cur nxt -> Map.unionWith Set.union cur (Map.unionsWith Set.union [ fmap Set.singleton mp | (mp,_) <- Set.toList nxt])) Map.empty
-}

buildST :: Monad m => BDDFormula s -> BDDM s Int m (StateMachine s)
buildST f = do
  (res,_,_,_) <- buildST' 0 Map.empty Map.empty f
  return res

buildST' :: Monad m => Integer -> StateCache s -> StateMachine s -> BDDFormula s -> BDDM s Int m (StateMachine s,StateCache s,Integer,Integer)
buildST' next cache st f = case Map.lookup f cache of
  Just r -> return (st,cache,next,r)
  Nothing -> do
    (s,ncache2,nst2,nnext2) <- foldlM (\(cur,ccache,cst,cnext) cl -> do
                                          nxt_f1 <- canonAndM (#&&) (clauseNext cl) (clauseAlways cl)
                                          nxt_f2 <- canonAndM (#&&) nxt_f1 (Set.singleton (ClauseT { clauseVars = Map.empty
                                                                                                   , clauseNext = Set.empty
                                                                                                   , clauseAlways = clauseAlways cl
                                                                                                   }))
                                          (nst,ncache,nnext,nxt_id) <- buildST' cnext ccache cst nxt_f2
                                          return (Set.insert (clauseVars cl,nxt_id) cur,ncache,nst,nnext)
                                      ) (Set.empty,Map.insert f next cache,st,next+1) f
    return (Map.insert next s nst2,ncache2,nnext2,next)

clauseConditions :: Monad m => Clause -> BDDM s Int m (Map String (Tree s Int))
clauseConditions cl = mapM (\(var,conds) -> do
                               tconds <- conditionsBDD conds
                               return (var,tconds)
                           ) (Map.toAscList (clauseVars cl))
                      >>= return.(Map.fromAscList)


clauseFollowing :: Clause -> CanonFormula
clauseFollowing cl1 = let cl2 = (clauseNext cl1) `canonAnd` (clauseAlways cl1)
                      in Set.fromList [ cl { clauseAlways = (clauseAlways cl) `canonAnd` (clauseAlways cl1)
                                           } | cl <- Set.toList cl2 ]




{-
buildCache :: TypeMap -> StateCache -> Integer -> CanonFormula -> (Integer,StateCache)
buildCache vars cache n formula = case Map.lookup formula cache of
  Just r -> (r,cache)
  Nothing -> let ncache = Map.insert formula (n,[ (clauseVars clause,) | clause <- formula ]

clauseToCache :: TypeMap -> StateCache -> Integer -> Clause -> (Map String [Condition],Integer)
clauseToCache vars cache n clause =

clauseToPromela :: TypeMap -> Map CanonFormula Clause -> [Step]
clauseToPromela vars cl = -}
module Language.GTL.PromelaContract where

import Data.BDD
import Data.BDD.Integer
import Data.BDD.Sets
import Language.GTL.Syntax as GTL
import Language.GTL.LTL
import Language.GTL.Translation
import Language.Scade.Syntax as Sc
import Language.Promela.Syntax as Pr

import Data.Map as Map
import Data.Set as Set
import Data.Traversable (mapM)
import Data.Foldable (foldl,foldlM)
import Prelude hiding (mapM,foldl)
import Data.Maybe (catMaybes)

data TransModel s = TransModel
                    { varsIn :: Map String (Set (Tree s Int))
                    , varsOut :: Map String [(String,String)]
                    , stateMachine :: Buchi (Map String (Tree s Int))
                    } deriving Show
                               
type TransProgram s = Map String (TransModel s)

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Pr.Module]
translateContracts scade decls
  = runIdBDDM $ do
    prog <- buildTransProgram scade decls
    translateContracts' prog

translateContracts' :: Monad m => TransProgram s -> BDDM s Int m [Pr.Module]
translateContracts' prog
  = do
    let decls = Pr.Decl $ Pr.Declaration Nothing Pr.TypeInt [("conn_"++name++"_"++var,Nothing,Nothing) | (name,mdl) <- Map.toList prog,(var,_) <- Map.toList (varsIn mdl) ]
    mapM (\(name,mdl) -> do
             do_stps <- mapM (\(st,decl) -> do
                                 let follows = [ (vars $ (stateMachine mdl)!succ,succ) | succ <- Set.toList $ successors decl ]
                                 if_stps <- mapM (getIfSteps name mdl) follows
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
                                     Pr.StepStmt (Pr.StmtIf [ [Pr.StepStmt (Pr.StmtAssign (VarRef "state" Nothing Nothing) (Pr.ConstExpr $ Pr.ConstInt name)) Nothing]
                                                            | (name,st) <- Map.toList (stateMachine mdl), isStart st ]) Nothing,
                                     Pr.StepStmt (Pr.StmtDo do_stps) Nothing ]
               }
         ) (Map.toList prog) >>= return.(decls:)
    where
      getIfSteps name mdl (cond,follow) = do
        cond_stps <- mapM (getConds name mdl) (Map.toList cond)
        return $ (concat cond_stps) ++ [ Pr.StepStmt (Pr.StmtAssign (Pr.VarRef "state" Nothing Nothing)
                                                      (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral follow)) Nothing
                                       ]
      getConds name mdl (var,tree) = case Map.lookup var (varsIn mdl) of
        Nothing -> case Map.lookup var (varsOut mdl) of
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
                                          else return Nothing)
                         ) (Set.toList inc) >>= return.catMaybes
      checkVar op name var i = Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr op
                                            (Pr.RefExpr (Pr.VarRef ("conn_"++name++"_"++var) Nothing Nothing))
                                            (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral $ nodeHash i)
                                           ) Nothing


buildTransProgram :: Monad m => [Sc.Declaration] -> [GTL.Declaration] -> BDDM s Int m (TransProgram s)
buildTransProgram scade decls
  = do
    prog <- mapM (\m -> do
                     machine <- gtlsToBuchi (\lst -> do
                                                res <- mapM relToBDD lst
                                                mapM (\(x:xs) -> foldlM (#&&) x xs) (Map.fromListWith (\old new -> new ++ old) (fmap (\(name,tree) -> (name,[tree])) res))
                                            ) (modelContract m)
                     return (modelName m,TransModel { varsIn = Map.empty 
                                                    , varsOut = Map.empty
                                                    , stateMachine = machine
                                                    })
                 ) models >>= return.(Map.fromList)
    return $ foldl (\cprog c -> let fromMdl = cprog!(connectFromModel c)
                                    nprog1 = Map.adjust
                                             (\mdl -> mdl { varsIn = Map.insertWith Set.union
                                                                      (connectToVariable c)
                                                                      (bddsForVar (connectFromVariable c) (stateMachine fromMdl))
                                                                      (varsIn mdl)
                                                          }) (connectToModel c) cprog
                                    nprog2 = Map.adjust
                                             (\mdl -> mdl { varsOut = Map.insertWith (++)
                                                                      (connectFromVariable c)
                                                                      [(connectToModel c,connectToVariable c)]
                                                                      (varsOut mdl)
                                                          }) (connectFromModel c) nprog1
                                    in nprog2
                   ) prog conns
  where
    models = [ m | Model m <- decls ]
    conns = [ c | Connect c <- decls ]

bddsForVar :: String -> Buchi (Map String (Tree s Int)) -> Set (Tree s Int)
bddsForVar var buchi = foldl (\mp st -> case Map.lookup var (vars st) of
                                 Nothing -> mp
                                 Just tree -> Set.insert tree mp
                             ) Set.empty buchi

{-
relsToBDD :: Monad m => Buchi (GTL.Relation,GTL.Lit,GTL.Lit) -> BDDM s Int m (Buchi (String,Tree s Int))
relsToBDD buchi = mapM
                  (\st -> do
                      ntrue <- mapM relToBDD (Set.toList (trueVars st))
                      nfalse <- mapM (\x -> do
                                         (name,tree) <- relToBDD x
                                         tree' <- not' tree
                                         return (name,tree')
                                     ) (Set.toList (falseVars st))
                      return $ BuchiState
                        { isStart = isStart st
                        , trueVars = Set.fromList ntrue
                        , falseVars = Set.fromList nfalse
                        , finalSets = finalSets st
                        , successors = successors st
                        })
                  buchi-}


relToBDD :: Monad m => GTLAtom -> BDDM s Int m (String,Tree s Int)
relToBDD (GTLRel rel (Variable v) (Constant c)) = do
  bdd <- relToBDD' rel c
  return (v,bdd)
relToBDD (GTLRel rel (Constant c) (Variable v)) = do
  bdd <- relToBDD' (relNot rel) c
  return (v,bdd)
relToBDD (GTLElem v lits p) = do
  bdd <- encodeSet 0 (Set.fromList $ fmap (\(Constant x) -> fromIntegral x::Int) lits)
  if p
    then return (v,bdd)
    else (do
             bdd' <- not' bdd
             return (v,bdd'))
relToBDD _ = error "Invalid relation detected"

relToBDD' :: Monad m => GTL.Relation -> Integer -> BDDM s Int m (Tree s Int)
relToBDD' GTL.BinLT n   = encodeSignedRange 0 (minBound::Int) (fromIntegral n - 1)
relToBDD' GTL.BinLTEq n = encodeSignedRange 0 (minBound::Int) (fromIntegral n)
relToBDD' GTL.BinGT n   = encodeSignedRange 0 (fromIntegral n + 1) (maxBound::Int)
relToBDD' GTL.BinGTEq n = encodeSignedRange 0 (fromIntegral n) (maxBound::Int)
relToBDD' GTL.BinEq n   = encodeSingleton 0 (fromIntegral n::Int)
relToBDD' GTL.BinNEq n  = encodeSingleton 0 (fromIntegral n::Int) >>= not'
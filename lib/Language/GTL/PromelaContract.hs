{- Ein Vögelchen, dem noch die Glieder zu zart und weich
 - erhebt umsonst sein zitterndes Gefider, den Alten gleich
 - den höh'ren Kreis der Lüfte zu zerteilen,
 - obgleich der Wille da, den selben nachzueilen.
 - Ganz ähnlich geht's uns allhier mit unserem Witz und Wissen;
 - die nimmer ruhende Begier ist nach dem Höh'ren stets beflissen.
 - Der angebor'ne Stolz will auch die schwersten Sachen sich federleicht,
 - ja was unmöglich fällt,
 - sich möglich machen.
 - Da unserem Witz wie unserem Leben von Gott allhier ein Ziel gestellt
 - das nicht zu überstreben.
 - Es kennt die Welt nur einen Salomon
 - den Gott, um dessen Thron die höchste Weisheit strahlt
 - den Weisesten gennenet
 - der doch sein Schwachsein selbst bekennet.
 - Achja, in dieser reicht das Erkenntnis nicht zu seiner Völligkeit.
 - Gott lässt uns durch das Sterben, dass uns zu nichts zu machen scheint,
 - erst alles erben.
 - Was dunkel war, wird dann ein heller Schein.
 - Was Stückwerk hieß, wird ganz.
 - Was kindisch, männlich sein.
 -                                  -- Telemann
 -}
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

import Debug.Trace

data TransModel s = TransModel
                    { varsIn :: Map String (Set (Tree s Int))
                    , varsOut :: Map String (Set (Maybe (String,String)))
                    , stateMachine :: Buchi (Map String (Tree s Int))
                    } deriving Show
                               
data TransProgram s = TransProgram
                      { transModels :: Map String (TransModel s)
                      , transClaims :: [Buchi (Map (String,String) (Tree s Int))]
                      } deriving Show

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Pr.Module]
translateContracts scade decls
  = runIdBDDM $ do
    prog <- buildTransProgram scade decls
    translateContracts' prog

claimInVars :: TransProgram s -> Buchi (Map (String,String) (Tree s Int)) -> Map (String,String) (Set (Tree s Int))
claimInVars prog buchi = Map.fromList [ ((mname,var),bddsForVar var (stateMachine $ (transModels prog)!mname)) | (mname,var) <- Set.toList $ usedVars buchi ]

translateClaim :: Monad m => Map (String,String) (Set (Tree s Int)) -> Buchi (Map (String,String) (Tree s Int)) -> BDDM s Int m [Pr.Step]
translateClaim varsIn machine = do
  do_stps <- mapM (\(st,decl) -> do
                      let follows = [ (vars $ machine!succ,succ) | succ <- Set.toList $ successors decl ]
                      if_stps <- mapM getIfSteps follows
                      let stps = Pr.StmtLabel ("st"++show st) (Pr.StmtIf if_stps)
                      return $ Pr.StepStmt (if Set.null (finalSets decl) -- XXX: This is terrible wrong :(
                                            then stps
                                            else Pr.StmtLabel ("accept"++show st) stps) Nothing
                  ) (Map.toList machine)
  return $ [Pr.StepStmt (Pr.StmtIf [ [Pr.StepStmt (Pr.StmtGoto ("st"++show name)) Nothing]
                                   | (name,st) <- Map.toList machine, isStart st ]) Nothing
           ] ++ do_stps
  where
    getIfSteps (cond,follow) = do
      cond_stps <- mapM getConds (Map.toList cond)
      return $ (concat cond_stps) ++ [ Pr.StepStmt (Pr.StmtGoto ("st"++show follow)) Nothing ]
    getConds ((mdl,var),tree) = mapM (\i -> do
                                         nv <- i #=> tree
                                         t <- true
                                         f <- false
                                         if nv == t
                                           then return $ Just $ checkVar Pr.BinEquals mdl var i
                                           else (do
                                                    nv <- i #&& tree
                                                    if nv == f
                                                      then return $ Just $ checkVar Pr.BinNotEquals mdl var i
                                                      else return Nothing)
                                     ) (Set.toList $ varsIn!(mdl,var)) >>= return.catMaybes
    checkVar op mdl var i = Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr op
                                         (Pr.RefExpr (Pr.VarRef ("never_"++mdl++"_"++var) Nothing Nothing))
                                         (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral $ nodeHash i)
                                        ) Nothing

translateModel :: Monad m => String -> TransModel s -> BDDM s Int m [Pr.Step]
translateModel name mdl = do
  do_stps <- mapM (\(st,decl) -> do
                      stps <- getSteps (vars decl)
                      return $ Pr.StepStmt
                        (Pr.StmtLabel
                         ("st"++show st)
                         (Pr.StmtDStep $ stps ++ getFollows (Set.toList $ successors decl))
                        ) Nothing
                  ) (Map.toList $ stateMachine mdl)
  return $ [Pr.StepStmt (Pr.StmtIf [ [Pr.StepStmt (Pr.StmtGoto ("st"++ show name)) Nothing]
                                   | (name,st) <- Map.toList (stateMachine mdl), isStart st ]) Nothing
           ] ++ do_stps
    where
      getFollows succs = [ Pr.StepStmt (Pr.StmtIf [ [Pr.StepStmt (Pr.StmtGoto $ "st"++show s) Nothing ] | s <- succs ]) Nothing ]
      getSteps cond = do
        cond_stps <- mapM getConds (Map.toList cond)
        return $ concat cond_stps
      getConds (var,tree) = case Map.lookup var (varsIn mdl) of
        Nothing -> case Map.lookup var (varsOut mdl) of
          Nothing -> return []
          Just ns -> return [ Pr.StepStmt (Pr.StmtAssign
                                           (Pr.VarRef (case target of
                                                          Just (mname,var) -> "conn_"++mname++"_"++var
                                                          Nothing -> "never_"++name++"_"++var
                                                      ) Nothing Nothing)
                                           (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral (nodeHash tree))) Nothing
                            | target <- Set.toList ns ]
        Just inc -> mapM (\i -> do
                             nv <- i #=> tree
                             t <- true
                             f <- false
                             if nv == t
                               then return $ Just $ checkVar Pr.BinEquals var i
                               else (do
                                        nv <- i #&& tree
                                        if nv == f
                                          then return $ Just $ checkVar Pr.BinNotEquals var i
                                          else return Nothing)
                         ) (Set.toList inc) >>= return.catMaybes
      checkVar op var i = Pr.StepStmt (Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr op
                                       (Pr.RefExpr (Pr.VarRef ("conn_"++name++"_"++var) Nothing Nothing))
                                       (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral $ nodeHash i)
                                      ) Nothing

translateContracts' :: Monad m => TransProgram s -> BDDM s Int m [Pr.Module]
translateContracts' prog
  = do
    let decls = Pr.Decl $ Pr.Declaration Nothing Pr.TypeInt $
                [ ("conn_"++name++"_"++var,Nothing,Nothing)
                | (name,mdl) <- Map.toList $ transModels prog
                , (var,_) <- Map.toList (varsIn mdl) ] ++
                [ ("never_"++name++"_"++var,Nothing,Nothing)
                | (name,mdl) <- Map.toList $ transModels prog
                , (var,set) <- Map.toList (varsOut mdl)
                , Set.member Nothing set]
    model_procs <- mapM (\(name,mdl) -> do
                            steps <- translateModel name mdl
                            return $ Pr.ProcType { Pr.proctypeActive = Just Nothing -- active without priority
                                                 , Pr.proctypeName = name
                                                 , Pr.proctypeArguments = []
                                                 , Pr.proctypePriority = Nothing
                                                 , Pr.proctypeProvided = Nothing
                                                 , Pr.proctypeSteps = steps
                                                 }
                        ) (Map.toList $ transModels prog)
    nevers <- mapM (\claim -> do
                       steps <- translateClaim (claimInVars prog claim) claim
                       return $ Pr.Never steps) (transClaims prog)
    return (decls:model_procs++nevers)


buildTransProgram :: Monad m => [Sc.Declaration] -> [GTL.Declaration] -> BDDM s Int m (TransProgram s)
buildTransProgram scade decls
  = do
    prog <- mapM (\m -> do
                     machine <- gtlsToBuchi (\lst -> do
                                                res <- mapM relToBDD lst
                                                mapM (\(x:xs) -> foldlM (#&&) x xs) (Map.fromListWith (\old new -> new ++ old)
                                                                                     (fmap (\(qual,name,tree) -> case qual of
                                                                                               Nothing -> (name,[tree])
                                                                                               Just _ -> error "Contracts can't contain qualified variables"
                                                                                           ) res))
                                            ) (modelContract m)
                     return (modelName m,TransModel { varsIn = Map.empty 
                                                    , varsOut = Map.empty
                                                    , stateMachine = machine
                                                    })
                 ) models >>= return.(Map.fromList)
    nevers <- mapM (\claim -> gtlsToBuchi (\lst -> do
                                              res <- mapM relToBDD lst
                                              mapM (\(x:xs) -> foldlM (#&&) x xs) (Map.fromListWith (\old new -> new ++ old)
                                                                                   (fmap (\(qual,name,tree) -> case qual of
                                                                                             Nothing -> error "Verify formulas must only contain qualified names"
                                                                                             Just rq -> ((rq,name),[tree])) res))
                                          ) (fmap (GTL.Not) $ verifyFormulas claim)
                   ) claims
    let prog1 = foldl (\cprog c -> let fromMdl = cprog!(connectFromModel c)
                                       nprog1 = Map.adjust
                                                (\mdl -> mdl { varsIn = Map.insertWith Set.union
                                                                        (connectToVariable c)
                                                                        (bddsForVar (connectFromVariable c) (stateMachine fromMdl))
                                                                        (varsIn mdl)
                                                             }) (connectToModel c) cprog
                                       nprog2 = Map.adjust
                                                (\mdl -> mdl { varsOut = Map.insertWith Set.union
                                                                         (connectFromVariable c)
                                                                         (Set.singleton $ Just (connectToModel c,connectToVariable c))
                                                                         (varsOut mdl)
                                                             }) (connectFromModel c) nprog1
                                   in nprog2
                      ) prog conns
        prog2 = foldl (\tprog never -> foldl (\cprog (_,st) -> foldl (\cprog' ((mname,var),_) -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union var
                                                                                                                                     (Set.singleton Nothing)
                                                                                                                                     (varsOut mdl)
                                                                                                                         }) mname cprog'
                                                                     ) cprog (Map.toList (vars st))
                                             ) prog1 (Map.toList never)
                      ) prog1 nevers
    return $ TransProgram
      { transModels = prog2
      , transClaims = nevers
      }
  where
    models = [ m | Model m <- decls ]
    conns = [ c | Connect c <- decls ]
    claims = [ v | Verify v <- decls ]

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


relToBDD :: Monad m => GTLAtom -> BDDM s Int m (Maybe String,String,Tree s Int)
relToBDD (GTLRel rel (Variable v) (Constant c)) = do
  bdd <- relToBDD' rel c
  return (Nothing,v,bdd)
relToBDD (GTLRel rel (Qualified m v) (Constant c)) = do
  bdd <- relToBDD' rel c
  return (Just m,v,bdd)
relToBDD (GTLRel rel (Constant c) (Variable v)) = do
  bdd <- relToBDD' (relNot rel) c
  return (Nothing,v,bdd)
relToBDD (GTLRel rel (Constant c) (Qualified m v)) = do
  bdd <- relToBDD' (relNot rel) c
  return (Just m,v,bdd)
relToBDD (GTLElem v lits p) = do
  bdd <- encodeSet 0 (Set.fromList $ fmap (\(Constant x) -> fromIntegral x::Int) lits)
  if p
    then return (Nothing,v,bdd)
    else (do
             bdd' <- not' bdd
             return (Nothing,v,bdd'))
relToBDD _ = error "Invalid relation detected"

relToBDD' :: Monad m => GTL.Relation -> Integer -> BDDM s Int m (Tree s Int)
relToBDD' GTL.BinLT n   = encodeSignedRange 0 (minBound::Int) (fromIntegral n - 1)
relToBDD' GTL.BinLTEq n = encodeSignedRange 0 (minBound::Int) (fromIntegral n)
relToBDD' GTL.BinGT n   = encodeSignedRange 0 (fromIntegral n + 1) (maxBound::Int)
relToBDD' GTL.BinGTEq n = encodeSignedRange 0 (fromIntegral n) (maxBound::Int)
relToBDD' GTL.BinEq n   = encodeSingleton 0 (fromIntegral n::Int)
relToBDD' GTL.BinNEq n  = encodeSingleton 0 (fromIntegral n::Int) >>= not'

usedVars :: Ord a => Buchi (Map a b) -> Set a
usedVars buchi = foldl (\set st -> Set.union set (Map.keysSet (vars st))) Set.empty (Map.elems buchi)
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
{-# LANGUAGE GADTs #-}
module Language.GTL.PromelaContract where

import Data.BDD
import Data.BDD.Integer
import Data.BDD.Sets
import Language.GTL.Syntax as GTL
import Language.GTL.LTL
import Language.GTL.Translation
import Language.Scade.Syntax as Sc
import Language.Promela.Syntax as Pr
import Language.Promela.Pretty (prettyPromela)
import Language.GTL.ScadeAnalyzer
import Language.GTL.ErrorRefiner

import Data.Map as Map hiding (mapMaybe)
import Data.Set as Set
import Data.Traversable (mapM)
import Data.Foldable (foldl,foldlM)
import Prelude hiding (mapM,foldl,catch)
import Data.Maybe (catMaybes,mapMaybe)
import System.Process
import Control.Monad.Trans
import System.FilePath
import System.Directory
import Control.Exception.Extensible
import System.IO.Error (isDoesNotExistError)
import System.Environment
import Control.Monad (unless)

import Debug.Trace

data TransModel s = TransModel
                    { varsIn :: Map String (Set (Tree s Int))
                    , varsOut :: Map String (Set (Maybe (String,String)))
                    , varsInit :: Map String (Tree s Int)
                    , stateMachine :: Buchi (Map (String,Integer) (Tree s Int))
                    } deriving Show
                               
data TransProgram s = TransProgram
                      { transModels   :: Map String (TransModel s)
                      , transClaims   :: [Buchi (Map (String,(String,Integer)) (Tree s Int))]
                      } deriving Show

deleteTmp :: FilePath -> IO ()
deleteTmp fp = catchJust (\e -> if isDoesNotExistError e
                                then Just ()
                                else Nothing) (removeFile fp) (const $ return ())
  

verifyModel :: Bool -> String -> [Sc.Declaration] -> [GTL.Declaration] -> IO ()
verifyModel keep name scade decls = runBDDM $ do
  prog <- buildTransProgram scade decls
  pr <- translateContracts' prog
  lift $ writeFile (name <.> "pr") (show $ prettyPromela pr)
  lift $ rawSystem "spin" ["-a",name <.> "pr"]
  let verifier = name++"-verifier"
  gcc <- lift $ catch (getEnv "CC") (\e -> const (return "gcc") (e::SomeException))
  lift $ rawSystem gcc ["pan.c","-o",verifier]
  unless keep $ lift $ do
    deleteTmp "pan.c"
    deleteTmp "pan.h"
    deleteTmp "pan.m"
    deleteTmp "pan.t"
    deleteTmp "pan.b"
  outp <- lift $ readProcess ("./"++verifier) ["-a","-e"] ""
  unless keep $ lift $ deleteTmp verifier
  let trace_files = filterTraces outp
  traces <- mapM (\trace -> lift $ do
                     res <- fmap (traceToBDD prog) $ parseTrace (name <.> "pr") trace
                     unless keep $ deleteTmp trace
                     return res
                 ) trace_files
  unless keep $ lift $ deleteTmp (name <.> "pr")
  case traces of
    [] -> lift $ putStrLn "No errors found."
    _  -> do
      lift $ putStrLn $ show (length traces) ++ " errors found"
      lift $ writeTraces (name <.> "gtltrace") traces
      lift $ putStrLn $ "Written to "++(name <.> "gtltrace")
  return ()

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Pr.Module]
translateContracts scade decls
  = runIdBDDM $ do
    prog <- buildTransProgram scade decls
    translateContracts' prog

traceToBDD :: TransProgram s -> [(String,Integer)] -> [(String,Map (String,Integer) (Tree s Int))]
traceToBDD prog trace = fmap (\(mdl,st) -> let tmdl = (transModels prog)!mdl
                                               entr = (stateMachine tmdl)!st
                                           in (mdl,Map.filterWithKey (\(name,lvl) e -> not $ Map.member name (varsIn tmdl)) (vars entr))) trace

claimInVars :: TransProgram s -> Buchi (Map (String,(String,Integer)) (Tree s Int)) -> Map (String,(String,Integer)) (Set (Tree s Int))
claimInVars prog buchi = Map.fromList [ ((mname,var),bddsForVar var (stateMachine $ (transModels prog)!mname))
                                      | (mname,var) <- Set.toList $ usedVars buchi ]

translateClaim :: Monad m => Map (String,(String,Integer)) (Set (Tree s Int)) -> SBuchi (Map (String,(String,Integer)) (Tree s Int)) -> BDDM s Int m [Pr.Step]
translateClaim varsIn machine = do
  do_stps <- mapM (\((sth,stl),decl) -> do
                      stps <- getSteps (vars decl)
                      let nstps = Pr.StmtLabel ("st"++show sth++"_"++show stl)
                                  (prAtomic $ stps ++ getFollows (Set.toList $ successors decl))
                      return $ if finalSets decl
                               then Pr.StmtLabel ("accept"++show sth++"_"++show stl) nstps
                               else nstps
                  ) (Map.toList machine)
  return $ fmap toStep $ [prIf [ [Pr.StmtGoto ("st"++show nameh++"_"++show namel)]
                               | ((nameh,namel),st) <- Map.toList machine, isStart st ]
                         ] ++ do_stps
  where
    getFollows succs = [ prIf [ [ Pr.StmtGoto $ "st"++show sh++"_"++show sl ] | (sh,sl) <- succs ] ]
    getSteps cond = do
        cond_stps <- mapM getConds (Map.toList cond)
        let check_stps = case buildConditionCheck (concat cond_stps) of
              Nothing -> []
              Just expr -> [Pr.StmtExpr $ Pr.ExprAny expr]
        return $ check_stps
    getConds ((mdl,(var,lvl)),tree) = mapM (\i -> do
                                         let rname = "never_"++mdl++"_"++var
                                         nv <- i #=> tree
                                         t <- true
                                         f <- false
                                         if nv == t
                                           then return (True,rname,fromIntegral $ nodeHash i)
                                           else (do
                                                    nv <- i #&& tree
                                                    if nv == f
                                                      then return (False,rname,fromIntegral $ nodeHash i)
                                                      else return (True,rname,fromIntegral $ nodeHash i))
                                     ) (Set.toList $ varsIn!(mdl,(var,lvl)))

buildConditionCheck :: [(Bool,String,Integer)] -> Maybe Pr.AnyExpression
buildConditionCheck conds = let pos = [ Pr.BinExpr Pr.BinEquals
                                        (Pr.RefExpr (Pr.VarRef var Nothing Nothing))
                                        (Pr.ConstExpr $ Pr.ConstInt i)
                                      | (True,var,i) <- conds ]
                                neg = [ Pr.BinExpr Pr.BinNotEquals
                                        (Pr.RefExpr (Pr.VarRef var Nothing Nothing))
                                        (Pr.ConstExpr $ Pr.ConstInt i) 
                                      | (False,var,i) <- conds ]
                                pf = foldl1 (Pr.BinExpr Pr.BinOr) pos
                                nf = foldl1 (Pr.BinExpr Pr.BinAnd) neg
                            in case pos of
                              [] -> case neg of
                                [] -> Nothing
                                _ -> Just nf
                              _ -> case neg of
                                [] -> Just pf
                                _ -> Just $ Pr.BinExpr Pr.BinAnd pf nf

translateModel :: Monad m => String -> TransModel s -> BDDM s Int m [Pr.Step]
translateModel name mdl = do
  inits <- sequence [ genEntry st decl | (st,decl) <- Map.toList $ stateMachine mdl, isStart decl ]
  sts <- sequence [ do
                       jumps <- sequence [ genEntry succ (stateMachine mdl!succ) | succ <- Set.toList $ successors decl ]
                       return $ Pr.StmtLabel ("st"++show st) (prIf jumps)
                  | (st,decl) <- Map.toList $ stateMachine mdl ]
  return $ fmap toStep $ [ prIf inits ] ++ sts
  where
    genEntry st decl = do
      stps <- getSteps (vars decl)
      return [ prAtomic $ [ prDStep $ stps ++ [Pr.StmtPrintf ("ENTER "++name++" "++show st++"\n") []]
                          , Pr.StmtGoto $ "st"++show st ] ]
    getSteps cond = do
      cond_stps <- mapM getConds (Map.toList cond)
      let checks = [ cond | Right cond <- cond_stps ]
          check_stps = case buildConditionCheck $ concat checks of
            Nothing -> []
            Just expr -> [Pr.StmtExpr $ Pr.ExprAny expr]
          assigns = [ assign | Left assign <- cond_stps ]
      return $ check_stps ++ (concat assigns)
    getConds ((var,lvl),tree) = case Map.lookup var (varsIn mdl) of
      Nothing -> case Map.lookup var (varsOut mdl) of
        Nothing -> error $ "Internal error: Variable "++show var++" is neither input nor output"
        Just ns -> return $ Left [ Pr.StmtAssign
                                   (Pr.VarRef (case target of
                                                  Just (mname,var) -> "conn_"++mname++"_"++var
                                                  Nothing -> "never_"++name++"_"++var
                                              ) Nothing Nothing)
                                   (Pr.ConstExpr $ Pr.ConstInt $ fromIntegral (nodeHash tree))
                                 | target <- Set.toList ns ]
      Just inc -> mapM (\i -> do
                           let rname = "conn_"++name++"_"++var
                           nv <- i #=> tree
                           t <- true
                           f <- false
                           if nv == t -- The input matches the condition perfectly
                             then return (True,rname,fromIntegral $ nodeHash i)
                             else (do
                                      nv <- i #&& tree
                                      if nv == f -- The input doesn't match the condition at all
                                        then return (False,rname,fromIntegral $ nodeHash i)
                                        else return (True,rname,fromIntegral $ nodeHash i))
                       ) (Set.toList inc) >>= return.(Right)

translateContracts' :: Monad m => TransProgram s -> BDDM s Int m [Pr.Module]
translateContracts' prog
  = do
    t <- true
    let decls = Pr.Decl $ Pr.Declaration Nothing Pr.TypeInt $
                [ ("conn_"++name++"_"++var,Nothing,Just $ ConstExpr $ ConstInt $ fromIntegral $ nodeHash (case Map.lookup var (varsInit mdl) of 
                                                                                                             Nothing -> t
                                                                                                             Just init -> init))
                | (name,mdl) <- Map.toList $ transModels prog
                , (var,_) <- Map.toList (varsIn mdl) ] ++
                [ ("never_"++name++"_"++var,Nothing,Just $ ConstExpr $ ConstInt $ fromIntegral $ nodeHash (case Map.lookup var (varsInit mdl) of 
                                                                                                              Nothing -> t
                                                                                                              Just init -> init))
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
                       steps <- translateClaim (claimInVars prog claim) (translateGBA claim)
                       return $ Pr.Never steps) (transClaims prog)
    return (decls:model_procs++nevers)


buildTransProgram :: Monad m => [Sc.Declaration] -> [GTL.Declaration] -> BDDM s Int m (TransProgram s)
buildTransProgram scade decls
  = do
    t <- true
    prog <- mapM (\m -> do
                     let (inp_vars,outp_vars) = scadeInterface ((modelArgs m)!!0) scade
                         inp_map = Map.fromList inp_vars
                         outp_map = Map.fromList outp_vars
                     machine <- gtlsToBuchi (\lst -> do
                                                res <- mapM relToBDD lst
                                                mapM (\(x:xs) -> foldlM (#&&) x xs) (Map.fromListWith (\old new -> new ++ old)
                                                                                     (fmap (\(qual,name,lvl,tree) -> case qual of
                                                                                               Nothing -> ((name,lvl),[tree])
                                                                                               Just _ -> error "Contracts can't contain qualified variables"
                                                                                           ) res))
                                            ) (modelContract m) >>= completeCases outp_map
                     inits <- mapM (\(v,i) -> do
                                       r <- case i of
                                         InitAll -> true
                                         InitOne x -> encodeSingleton 0 (fromIntegral x::Int)
                                       return (v,r)
                                   ) (modelInits m)
                     return (modelName m,TransModel { varsIn = Map.empty
                                                    , varsOut = Map.empty
                                                    , stateMachine = machine
                                                    , varsInit = Map.fromList inits
                                                    })
                 ) models >>= return.(Map.fromList)
    nevers <- mapM (\claim -> gtlsToBuchi (\lst -> do
                                              res <- mapM relToBDD lst
                                              mapM (\(x:xs) -> foldlM (#&&) x xs) (Map.fromListWith (\old new -> new ++ old)
                                                                                   (fmap (\(qual,name,lvl,tree) -> case qual of
                                                                                             Nothing -> error "Verify formulas must only contain qualified names"
                                                                                             Just rq -> ((rq,(name,lvl)),[tree])) res))
                                          ) (fmap (GTL.ExprNot) $ verifyFormulas claim)
                   ) claims
    let prog1 = foldl (\cprog c
                       -> let fromMdl = cprog!(connectFromModel c)
                              nprog1 = Map.adjust
                                       (\mdl -> mdl { varsIn = Map.insertWith Set.union
                                                               (connectToVariable c)
                                                               (bddsForVar (connectFromVariable c,0) (stateMachine fromMdl))
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
        prog2 = foldl (\tprog never -> foldl (\cprog (_,st) -> foldl (\cprog' ((mname,(var,lvl)),_)
                                                                      -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union var
                                                                                                             (Set.singleton Nothing)
                                                                                                             (varsOut mdl)
                                                                                                 }) mname cprog'
                                                                     ) cprog (Map.toList (vars st))
                                             ) tprog (Map.toList never)
                      ) prog1 nevers
        prog3 = fmap (\mdl -> mdl { varsIn = Map.mapWithKey (\k ins -> case Map.lookup k (varsInit mdl) of
                                                                Nothing -> ins
                                                                Just i -> Set.insert i ins) (varsIn mdl)
                                  }) prog2
    return $ TransProgram
      { transModels   = prog3
      , transClaims   = nevers
      }
  where
    models = [ m | Model m <- decls ]
    conns = [ c | Connect c <- decls ]
    claims = [ v | Verify v <- decls ]

completeCases :: Monad m => Map String Sc.TypeExpr -> Buchi (Map (String,Integer) (Tree s Int)) -> BDDM s Int m (Buchi (Map (String,Integer) (Tree s Int)))
completeCases outp machine = do
  t <- true
  let outpmp = Map.fromList $ fmap (\(v,_) -> ((v,0),t)) (Map.toList outp)
  return $ fmap (\st -> st { vars = Map.union (vars st) outpmp }) machine

bddsForVar :: (String,Integer) -> Buchi (Map (String,Integer) (Tree s Int)) -> Set (Tree s Int)
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


relToBDD :: Monad m => GTLAtom -> BDDM s Int m (Maybe String,String,Integer,Tree s Int)
relToBDD (GTLRel rel (ExprVar q v lvl) (ExprConst c)) = do
  bdd <- relToBDD' rel c
  return (q,v,lvl,bdd)
relToBDD (GTLRel rel (ExprConst c) (ExprVar q v lvl)) = do
  bdd <- relToBDD' (relNot rel) c
  return (q,v,lvl,bdd)
relToBDD (GTLElem q v lits p) = do
  bdd <- encodeSet 0 (Set.fromList $ fmap (fromIntegral::Integer->Int) lits)
  if p
    then return (q,v,0,bdd)
    else (do
             bdd' <- not' bdd
             return (q,v,0,bdd'))
relToBDD (GTLVar q n lvl v) = do
  bdd <- unit 0 v
  return (q,n,lvl,bdd)
relToBDD _ = error "Invalid relation detected"

relToBDD' :: Monad m => GTL.Relation -> Int -> BDDM s Int m (Tree s Int)
relToBDD' GTL.BinLT n   = encodeSignedRange 0 (minBound::Int) (n - 1)
relToBDD' GTL.BinLTEq n = encodeSignedRange 0 (minBound::Int) n
relToBDD' GTL.BinGT n   = encodeSignedRange 0 (n + 1) (maxBound::Int)
relToBDD' GTL.BinGTEq n = encodeSignedRange 0 n (maxBound::Int)
relToBDD' GTL.BinEq n   = encodeSingleton 0 n
relToBDD' GTL.BinNEq n  = encodeSingleton 0 n >>= not'

usedVars :: Ord a => Buchi (Map a b) -> Set a
usedVars buchi = foldl (\set st -> Set.union set (Map.keysSet (vars st))) Set.empty (Map.elems buchi)

getOutputAutomatas :: TransProgram s -> Map String (Buchi (Map (String,Integer) (Tree s Int)))
getOutputAutomatas prog = fmap (\mdl -> fmap (\entr -> entr
                                                       { vars = Map.filterWithKey (\(var,_) _ -> not $ Map.member var (varsIn mdl)) (vars entr)
                                                       }) (stateMachine mdl)) (transModels prog)
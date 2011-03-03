{-# LANGUAGE GADTs #-}
module Language.GTL.PromelaBuddy where

import Language.GTL.Translation
import Language.Scade.Syntax as Sc
import Language.Promela.Syntax as Pr
import Language.GTL.LTL
import Language.GTL.ScadeAnalyzer
import Language.GTL.Syntax as GTL

import Data.Map as Map
import Data.Set as Set
import Control.Monad.Identity
import Control.Monad.State
import Prelude hiding (foldl)
import Data.Foldable
import Data.List (intersperse)

data TransModel = TransModel
                  { varsInit :: Map String GTLAtom
                  , varsIn :: Set String
                  , varsOut :: Map String (Set (Maybe (String,String)))
                  , stateMachine :: Buchi ([Integer],[Integer]) --[GTLAtom]
                  , checkFunctions :: [String]
                  } deriving Show

data TransProgram = TransProgram
                    { transModels :: Map String TransModel
                    , transClaims :: [Buchi [GTLAtom]]
                    } deriving Show

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Pr.Module]
translateContracts scade decls = translateContracts' (buildTransProgram scade decls)

translateContracts' :: TransProgram -> [Pr.Module]
translateContracts' prog 
  = let include = Pr.CDecl $ unlines ["\\#include <cudd/cudd.h>"
                                     ,"DdManager* manager;"]
        states = [ Pr.CState ("DdNode* conn_"++name++"_"++var) "Global" Nothing
                 | (name,mdl) <- Map.toList $ transModels prog
                 , var <- Set.toList (varsIn mdl) ] ++
                 [ Pr.CState ("DdNode* never_"++name++"_"++var) "Global" Nothing
                 | (name,mdl) <- Map.toList $ transModels prog
                 , (var,set) <- Map.toList (varsOut mdl)
                 , Set.member Nothing set]
        procs = fmap (\(name,mdl) -> let steps = translateModel name mdl
                                         proc = Pr.ProcType { Pr.proctypeActive = Nothing
                                                            , Pr.proctypeName = name
                                                            , Pr.proctypeArguments = []
                                                            , Pr.proctypePriority = Nothing
                                                            , Pr.proctypeProvided = Nothing
                                                            , Pr.proctypeSteps = steps
                                                            }
                                     in (name,proc)) (Map.toList (transModels prog))
        check_funcs = Pr.CDecl $ unlines $
                      [ impl | mdl <- Map.elems (transModels prog), impl <- checkFunctions mdl ] ++
                      [ unlines $ ["void reset_"++name++"() {"] ++
                        ["  "++(case to of
                                   Just (q,n) -> "conn_"++q++"_"++n
                                   Nothing -> "never_"++name++"_"++from
                               )++" = DD_ONE(manager);" | (from,tos) <- Map.toList (varsOut mdl), to <- Set.toList tos ]++
                        ["}"]
                      | (name,mdl) <- Map.toList (transModels prog) ]
        init = prInit [ prAtomic $ [ StmtCCode "manager = Cudd_Init(32,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);" ] 
                        ++ [ StmtRun name [] | (name,_) <- procs ]
                      ]
    in [include,check_funcs]++states++[ pr | (_,pr) <- procs]++[init]

translateModel :: String -> TransModel -> [Pr.Step]
translateModel name mdl
  = let states = fmap (\(st,entr)
                       -> Pr.StmtLabel ("st"++show st) $
                          prAtomic [ Pr.StmtCCode $ unlines $ ["reset_"++name++"();" ] ++ [ "assign_"++name++show n++"();" | n <- snd $ vars entr ],
                                     prIf [ (if not $ Prelude.null $ fst $ vars nentr
                                             then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                                    [ "cond_"++name++show n++"()" | n <- fst $ vars nentr ] ]
                                             else []) ++ [Pr.StmtGoto $ "st"++show succ ]
                                          | succ <- Set.toList $ successors entr, let nentr = (stateMachine mdl)!succ ]
                                   ]
                      ) (Map.toList $ stateMachine mdl)
        inits = prIf [ [prAtomic $ (if not $ Prelude.null $ fst $ vars entr
                                    then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                           [ "cond_"++name++show n++"()" | n <- fst $ vars entr ] ]
                                    else []) ++ [Pr.StmtGoto $ "st"++show st ] ]
                     | (st,entr) <- Map.toList $ stateMachine mdl, isStart entr ]
    in fmap toStep $ inits:states

parseGTLAtom :: Map GTLAtom (Integer,Bool,String) -> String -> Map String (Set (Maybe (String,String))) -> GTLAtom -> ((Integer,Bool),Map GTLAtom (Integer,Bool,String))
parseGTLAtom mp name outps at
  = case Map.lookup at mp of
    Just (i,isinp,_) -> ((i,isinp),mp)
    Nothing -> case at of
      GTLRel rel lhs rhs -> let lvars = [ v | (Nothing,v) <- getVars lhs, Map.member v outps ]
                                rvars = [ v | (Nothing,v) <- getVars rhs, Map.member v outps ]
                                idx = fromIntegral $ Map.size mp
                                (res,isinp) = (case lvars of
                                                  [] -> case rhs of
                                                    ExprVar Nothing n -> if Map.member n outps
                                                                         then (createBuddyAssign idx name n (outps!n) (relTurn rel) lhs,False)
                                                                         else error "No output variable in relation"
                                                    _ -> case rvars of
                                                      [] -> (createBuddyCompare idx name rel lhs rhs,True)
                                                      _ -> error "Output variables must be alone"
                                                  _ -> case lhs of
                                                    ExprVar Nothing n -> (createBuddyAssign idx name n (outps!n) rel rhs,False)
                                                    _ -> case lvars of
                                                      [] -> (createBuddyCompare idx name  rel lhs rhs,True)
                                                      _ -> error "Output varibales must be alone"
                                              ) :: (String,Bool)
                            in ((idx,isinp),Map.insert at (idx,isinp,res) mp)

createBuddyAssign :: Integer -> String -> String -> Set (Maybe (String,String)) -> Relation -> GTL.Expr Int -> String
createBuddyAssign count q n outs rel expr
  = let (cmd,de,_,e) = createBuddyExpr 0 q expr
        trgs = fmap (maybe ("never_"++q++"_"++n) (\(q',n') -> "conn_"++q'++"_"++n')) $ Set.toList outs
    in unlines ([ "void assign_"++q++show count++"() {"] ++
                fmap ("  "++) cmd ++
                ["  "++head trgs++" = "++e++";"]++
                fmap (\trg -> "  "++trg++" = "++head trgs++";") (tail trgs)++
                ["  Cudd_Ref(conn_"++q++"_"++n++");"
                ]++
                fmap ("  "++) de ++
                ["}"])

createBuddyCompare :: Integer -> String -> Relation -> GTL.Expr Int -> GTL.Expr Int -> String
createBuddyCompare count q rel expr1 expr2
  = let (cmd1,de1,v,e1) = createBuddyExpr 0 q expr1
        (cmd2,de2,_,e2) = createBuddyExpr v q expr2
    in unlines $ ["int cond_"++q++show count++"() {"]++
       fmap ("  "++) (cmd1++cmd2)++
       ["  DdNode* lhs = "++e1++";"
       ,"  Cudd_Ref(lhs);"
       ,"  DdNode* rhs = "++e2++";"
       ,"  Cudd_Ref(rhs);"
       ,"  int res;"
       ]++(case rel of
              GTL.BinEq -> ["  res = Cudd_bddAnd(manager,lhs,rhs)!=Cudd_Not(Cudd_ReadOne(manager));"]
              GTL.BinLT -> ["  CUDD_ARITH_TYPE lval = Cudd_bddMinimum(mgr,lhs,0);",
                            "  CUDD_ARITH_TYPE rval = Cudd_bddMaximum(mgr,rhs,0);",
                            "  res = lval < rval;"]
              GTL.BinGTEq -> ["  CUDD_ARITH_TYPE lval = Cudd_bddMaximum(mgr,lhs,0);",
                              "  CUDD_ARITH_TYPE rval = Cudd_bddMinimum(mgr,rhs,0);",
                              "  res = lval >= rval;"]
              _ -> ["  //Unimplemented relation: "++show rel]
          )++
       ["  Cudd_RecursiveDeref(manager,rhs);",
        "  Cudd_RecursiveDeref(manager,lhs);"]++
       fmap ("  "++) (de2++de1)++
       ["  return res;",
        "}"]

createBuddyExpr :: Integer -> String -> GTL.Expr Int -> ([String],[String],Integer,String)
createBuddyExpr v mdl (ExprConst i) = ([],[],v,"Cudd_bddSingleton(manager,"++show i++",0)")
createBuddyExpr v mdl (ExprVar _ n) = ([],[],v,"conn_"++mdl++"_"++n)
createBuddyExpr v mdl (ExprBinInt op lhs rhs)
  = let (cmd1,de1,v1,e1) = createBuddyExpr v mdl lhs
        (cmd2,de2,v2,e2) = createBuddyExpr v1 mdl rhs
    in (cmd1++cmd2++["DdNode* tmp"++show v2++" = "++e1++";",
                     "Cudd_Ref(tmp"++show v2++");",
                     "DdNode* tmp"++show (v2+1)++" = "++e2++";",
                     "Cudd_Ref(tmp"++show (v2+1)++");"],
        ["Cudd_RecursiveDeref(manager,tmp"++show (v2+1)++");"
        ,"Cudd_RecursiveDeref(manager,tmp"++show v2++");"]++de2++de1,
        v2+2,
        (case op of
            OpPlus -> "Cudd_bddPlus"
            OpMinus -> "Cudd_bddMinus"
            OpMult -> "Cudd_bddTimes"
            OpDiv -> "Cudd_bddDivide"
        )++"(manager,tmp"++show v2++",tmp"++show (v2+1)++",0)")

--solveForLHS :: Maybe String -> String -> Expr Int -> Expr Int -> x

buildTransProgram :: [Sc.Declaration] -> [GTL.Declaration] -> TransProgram
buildTransProgram scade decls
  = let models = [ m | Model m <- decls ]
        conns = [ c | Connect c <- decls ]
        claims = [ v | Verify v <- decls ]
        
        tmodels1 = Map.fromList $ fmap (\m -> let (inp_vars,outp_vars) = scadeInterface ((modelArgs m)!!0) scade
                                                  outp_map = Map.fromList $ fmap (\(var,_) -> (var,Set.empty)) outp_vars
                                              in (modelName m,
                                                  TransModel { varsInit = Map.empty
                                                             , varsIn = Set.fromList $ fmap fst inp_vars
                                                             , varsOut = outp_map
                                                             , stateMachine = undefined
                                                             , checkFunctions = undefined
                                                             })) models
        tclaims = fmap (\claim -> runIdentity $ gtlsToBuchi return (fmap (GTL.ExprNot) $ verifyFormulas claim)) claims
        
        tmodels2 = foldl (\cmdls c -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union
                                                                          (connectFromVariable c)
                                                                          (Set.singleton $ Just (connectToModel c,connectToVariable c))
                                                                          (varsOut mdl)
                                                              }) (connectFromModel c) cmdls) tmodels1 conns
        tmodels3 = foldl (\cmdls never ->
                           foldl (\cmdls' st ->
                                   foldl (\cmdls'' at ->
                                           foldl (\cmdls''' (Just q,n) -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union
                                                                                                              n (Set.singleton Nothing)
                                                                                                              (varsOut mdl)
                                                                                                  }) q cmdls'''
                                                 ) cmdls'' (getAtomVars at)
                                         ) cmdls' (vars st)
                                 ) cmdls never
                         ) tmodels2 tclaims
        tmodels4 = foldl (\cur m -> Map.adjust
                                    (\entr -> let (sm,fm) = runState (gtlsToBuchi
                                                                      (\ats -> do
                                                                          mp <- get
                                                                          let (c,a,nmp) = foldl (\(chks,ass,cmp) at
                                                                                                 -> let ((n,f),nmp) = parseGTLAtom cmp (modelName m) (varsOut entr) at
                                                                                                    in (if f then (n:chks,ass,nmp)
                                                                                                        else (chks,n:ass,nmp))
                                                                                                ) ([],[],mp) ats
                                                                          put nmp
                                                                          return (c,a)
                                                                      ) (modelContract m)) Map.empty
                                              in entr { stateMachine = sm
                                                      , checkFunctions = fmap (\(_,_,f) -> f) (Map.elems fm)
                                                      }
                                    ) (modelName m) cur) tmodels3 models
    in TransProgram { transModels = tmodels4
                    , transClaims = tclaims
                    }
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
import Prelude hiding (foldl,concat)
import Data.Foldable
import Data.List (intersperse)

data TransModel = TransModel
                  { varsInit :: Map String String
                  , varsIn :: Set String
                  , varsOut :: Map String (Set (Maybe (String,String)))
                  , stateMachine :: Buchi ([Integer],[Integer]) --[GTLAtom]
                  , checkFunctions :: [String]
                  } deriving Show

data TransProgram = TransProgram
                    { transModels :: Map String TransModel
                    , transClaims :: [Buchi [Integer]]
                    , claimChecks :: [String]
                    } deriving Show

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Pr.Module]
translateContracts scade decls = translateContracts' (buildTransProgram scade decls)

translateContracts' :: TransProgram -> [Pr.Module]
translateContracts' prog 
  = let include = Pr.CDecl $ unlines ["\\#include <cudd/cudd.h>"
                                     ,"\\#include <cudd_arith.h>"
                                     ,"\\#include <assert.h>"
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
        check_funcs = Pr.CCode $ unlines $
                      [ impl | mdl <- Map.elems (transModels prog), impl <- checkFunctions mdl ] ++
                      claimChecks prog ++
                      [ unlines $ ["void reset_"++name++"(State* now) {"] ++
                        ["  "++(case to of
                                   Just (q,n) -> "now->conn_"++q++"_"++n
                                   Nothing -> "now->never_"++name++"_"++from
                               )++" = DD_ONE(manager);" | (from,tos) <- Map.toList (varsOut mdl), to <- Set.toList tos ]++
                        ["}"]
                      | (name,mdl) <- Map.toList (transModels prog) ]
        init = prInit [ prAtomic $ [ StmtCCode $ unlines $
                                     [ "manager = Cudd_Init(32,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);"] ++ 
                                     concat [ let trgs = if Set.member var (varsIn mdl)
                                                         then ["now.conn_"++name++"_"++var]
                                                         else [ case outp of
                                                                   Nothing -> "now.never_"++name++"_"++var
                                                                   Just (q,n) -> "now.conn_"++q++"_"++n
                                                              | outp <- Set.toList ((varsOut mdl)!var) ]
                                              in [ head trgs++" = "++e++";"
                                                 , "Cudd_Ref("++head trgs++");"] ++
                                                 [ trg++" = "++head trgs | trg <- tail trgs ]
                                            | (name,mdl) <- Map.toList (transModels prog),
                                              (var,e) <- Map.toList (varsInit mdl) ]
                                   ]
                        ++ [ StmtRun name [] | (name,_) <- procs ]
                      ]
        nevers = [ prNever $ translateNever never
                 | never <- transClaims prog ]
    in [include]++states++[check_funcs]++[ pr | (_,pr) <- procs]++[init]++nevers

translateModel :: String -> TransModel -> [Pr.Step]
translateModel name mdl
  = let states = fmap (\(st,entr)
                       -> Pr.StmtLabel ("st"++show st) $
                          prAtomic [ Pr.StmtCCode $ unlines $ ["reset_"++name++"(&now);" ] ++ [ "assign_"++name++show n++"(&now);" | n <- snd $ vars entr ],
                                     prIf [ (if not $ Prelude.null $ fst $ vars nentr
                                             then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                                    [ "cond_"++name++show n++"(&now)" | n <- fst $ vars nentr ] ]
                                             else []) ++ [Pr.StmtGoto $ "st"++show succ ]
                                          | succ <- Set.toList $ successors entr, let nentr = (stateMachine mdl)!succ ]
                                   ]
                      ) (Map.toList $ stateMachine mdl)
        inits = prIf [ [prAtomic $ (if not $ Prelude.null $ fst $ vars entr
                                    then [ Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                           [ "cond_"++name++show n++"(&now)" | n <- fst $ vars entr ] ]
                                    else []) ++ [Pr.StmtGoto $ "st"++show st ] ]
                     | (st,entr) <- Map.toList $ stateMachine mdl, isStart entr ]
    in fmap toStep $ inits:states

translateNever :: Buchi [Integer] -> [Pr.Step]
translateNever buchi
  = let rbuchi = translateGBA buchi
        showSt (i,j) = show i++"_"++show j
        states = fmap (\(st,entr)
                        -> let body = prAtomic [ prIf [ (if Prelude.null (vars nentr)
                                                        then []
                                                        else [Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                                                              [ "cond__never"++show n++"(&now)" | n <- vars nentr ]]) ++
                                                        [Pr.StmtGoto $ "st"++showSt succ]
                                                      | succ <- Set.toList $ successors entr, 
                                                        let nentr = rbuchi!succ ]
                                               ]
                           in Pr.StmtLabel ("st"++showSt st) $ if finalSets entr
                                                               then Pr.StmtLabel ("accept"++showSt st) body
                                                               else body
                      ) (Map.toList rbuchi)
        inits = prIf [ (if Prelude.null (vars entr)
                        then []
                        else [Pr.StmtCExpr Nothing $ unwords $ intersperse "&&"
                              [ "cond__never"++show n++"(&now)" | n <- vars entr ]]) ++
                       [Pr.StmtGoto $ "st"++showSt st]
                     | (st,entr) <- Map.toList rbuchi,
                       isStart entr
                     ]
    in fmap toStep $ inits:states

parseGTLAtom :: Map GTLAtom (Integer,Bool,String) -> Maybe (String,Map String (Set (Maybe (String,String)))) -> GTLAtom -> ((Integer,Bool),Map GTLAtom (Integer,Bool,String))
parseGTLAtom mp arg at
  = case Map.lookup at mp of
    Just (i,isinp,_) -> ((i,isinp),mp)
    Nothing -> case at of
      GTLRel rel lhs rhs -> let lvars = [ v | (Nothing,v) <- getVars lhs, Map.member v outps ]
                                rvars = [ v | (Nothing,v) <- getVars rhs, Map.member v outps ]
                                idx = fromIntegral $ Map.size mp
                                (res,isinp) = (case lvars of
                                                  [] -> case rhs of
                                                    ExprVar Nothing n -> if Map.member n outps
                                                                         then (createBuddyAssign idx rname n (outps!n) (relTurn rel) lhs,False)
                                                                         else error "No output variable in relation"
                                                    _ -> case rvars of
                                                      [] -> (createBuddyCompare idx name rel lhs rhs,True)
                                                      _ -> error "Output variables must be alone"
                                                  _ -> case lhs of
                                                    ExprVar Nothing n -> (createBuddyAssign idx rname n (outps!n) rel rhs,False)
                                                    _ -> case lvars of
                                                      [] -> (createBuddyCompare idx name  rel lhs rhs,True)
                                                      _ -> error "Output varibales must be alone"
                                              ) :: (String,Bool)
                                 in ((idx,isinp),Map.insert at (idx,isinp,res) mp)
      where
        name = case arg of
          Nothing -> Nothing
          Just (n,_) -> Just n
        rname = case name of
          Nothing -> error "Invalid use of unqualified variable"
          Just n -> n
        outps = case arg of
          Nothing -> Map.empty
          Just (_,s) -> s

createBuddyAssign :: Integer -> String -> String -> Set (Maybe (String,String)) -> Relation -> GTL.Expr Int -> String
createBuddyAssign count q n outs rel expr
  = let (cmd,de,_,e) = createBuddyExpr 0 (Just q) expr
        trgs = fmap (maybe ("now->never_"++q++"_"++n) (\(q',n') -> "now->conn_"++q'++"_"++n')) $ Set.toList outs
        (cmd2,te) = case rel of
          BinEq -> ([],e)
          BinNEq -> ([],"Cudd_Not("++e++")")
          GTL.BinGT -> (["DdNode* extr = "++e++";",
                         "Cudd_Ref(extr);",
                         "CUDD_ARITH_TYPE min;",
                         "int min_found = Cudd_bddMinimum(manager,extr,0,&min);",
                         "assert(min_found);",
                         "Cudd_RecursiveDeref(manager,extr);"
                        ],"Cudd_Not(Cudd_bddLessThanEqual(manager,min,0))")
          BinGTEq -> (["DdNode* extr = "++e++";",
                       "Cudd_Ref(extr);",
                       "CUDD_ARITH_TYPE min;",
                       "int min_found = Cudd_bddMinimum(manager,extr,0,&min);",
                       "assert(min_found);",
                       "Cudd_RecursiveDeref(manager,extr);"
                      ],"Cudd_Not(Cudd_bddLessThan(manager,min,0))")
          GTL.BinLT -> (["DdNode* extr = "++e++";",
                         "Cudd_Ref(extr);",
                         "CUDD_ARITH_TYPE max;",
                         "int max_found = Cudd_bddMaximum(manager,extr,0,&max);",
                         "assert(max_found);",
                         "Cudd_RecursiveDeref(manager,extr);"
                        ],"Cudd_bddLessThan(manager,max,0)")
          BinLTEq -> (["DdNode* extr = "++e++";",
                       "Cudd_Ref(extr);",
                       "CUDD_ARITH_TYPE max;",
                       "int max_found = Cudd_bddMaximum(manager,extr,0,&max);",
                       "assert(max_found);",
                       "Cudd_RecursiveDeref(manager,extr);"
                      ],"Cudd_bddLessThanEqual(manager,max,0)")
    in unlines ([ "void assign_"++q++show count++"(State* now) {"] ++
                fmap ("  "++) (cmd++cmd2) ++
                ["  "++head trgs++" = "++te++";"]++
                fmap (\trg -> "  "++trg++" = "++head trgs++";") (tail trgs)++
                ["  Cudd_Ref("++head trgs++");"
                ]++
                ["  printf(\"Assert %s.%s %s %s\\n\","++show q++","++show n++","++show (show rel)++","++show (show expr)++");"]++
                fmap ("  "++) de ++
                ["}"])

createBuddyCompare :: Integer -> Maybe String -> Relation -> GTL.Expr Int -> GTL.Expr Int -> String
createBuddyCompare count q rel expr1 expr2
  = let (cmd1,de1,v,e1) = createBuddyExpr 0 q expr1
        (cmd2,de2,_,e2) = createBuddyExpr v q expr2
    in unlines $ ["int cond_"++(maybe "_never" id q)++show count++"(State* now) {"]++
       fmap ("  "++) (cmd1++cmd2)++
       ["  DdNode* lhs = "++e1++";"
       ,"  Cudd_Ref(lhs);"
       ,"  DdNode* rhs = "++e2++";"
       ,"  Cudd_Ref(rhs);"
       ,"  int res;"
       ]++(case rel of
              GTL.BinEq -> ["  res = Cudd_bddAnd(manager,lhs,rhs)!=Cudd_Not(Cudd_ReadOne(manager));"]
              GTL.BinNEq -> ["  res = !((lhs==rhs) && Cudd_bddIsSingleton(manager,lhs,0));"]
              GTL.BinLT -> ["  CUDD_ARITH_TYPE lval,rval;",
                            "  int lval_found = Cudd_bddMinimum(manager,lhs,0,&lval);",
                            "  int rval_found = Cudd_bddMaximum(manager,rhs,0,&rval);",
                            "  res = lval_found && rval_found && (lval < rval);"]
              GTL.BinGTEq -> ["  CUDD_ARITH_TYPE lval,rval;",
                              "  int lval_found = Cudd_bddMaximum(manager,lhs,0,&lval);",
                              "  int rval_found = Cudd_bddMinimum(manager,rhs,0,&rval);",
                              "  printf(\"because %d >= %d\\n\",lval,rval);",
                              "  res = lval_found && rval_found && (lval >= rval);"]
              _ -> ["  //Unimplemented relation: "++show rel]
          )++
       ["  printf(\"%s %s %s == %d\\n\","++show (show expr1)++","++show (show rel)++","++show (show expr2)++",res);"]++
       ["  Cudd_RecursiveDeref(manager,rhs);",
        "  Cudd_RecursiveDeref(manager,lhs);"]++
       fmap ("  "++) (de2++de1)++
       ["  return res;",
        "}"]

createBuddyExpr :: Integer -> Maybe String -> GTL.Expr Int -> ([String],[String],Integer,String)
createBuddyExpr v mdl (ExprConst i) = ([],[],v,"Cudd_bddSingleton(manager,"++show i++",0)")
createBuddyExpr v mdl (ExprVar q n) = case mdl of
                                        Nothing -> case q of
                                          Just rq -> ([],[],v,"now->never_"++rq++"_"++n)
                                          Nothing -> error "verify claims must not contain qualified variables"
                                        Just rmdl -> ([],[],v,"now->conn_"++rmdl++"_"++n)
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
                                                  TransModel { varsInit = Map.fromList [ (name,case e of
                                                                                             InitAll -> "DD_ONE(manager)"
                                                                                             InitOne i -> "Cudd_bddSingleton(manager,"++show i++",0)")
                                                                                       | (name,e) <- modelInits m ]
                                                             , varsIn = Set.fromList $ fmap fst inp_vars
                                                             , varsOut = outp_map
                                                             , stateMachine = undefined
                                                             , checkFunctions = undefined
                                                             })) models
        (tclaims,fclaims) = foldl (\(sms,cmp1) claim
                                   -> let (sm,fm) = runState
                                                    (gtlsToBuchi (\ats -> do 
                                                                     mp <- get
                                                                     let (c,nmp) = foldl (\(cs,cmp2) at -> let ((n,True),nmp) = parseGTLAtom cmp2 Nothing at
                                                                                                           in (n:cs,nmp)
                                                                                         ) ([],mp) ats
                                                                     put nmp
                                                                     return c
                                                                 ) (fmap (GTL.ExprNot) $ verifyFormulas claim))
                                                    cmp1
                                      in (sm:sms,fm)
                                  ) ([],Map.empty) claims
        
        tmodels2 = foldl (\cmdls c -> Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union
                                                                          (connectFromVariable c)
                                                                          (Set.singleton $ Just (connectToModel c,connectToVariable c))
                                                                          (varsOut mdl)
                                                              }) (connectFromModel c) cmdls) tmodels1 conns
        tmodels3 = foldl (\cmdls never ->
                           foldl (\cmdls' (Just q,n) ->
                                   Map.adjust (\mdl -> mdl { varsOut = Map.insertWith Set.union
                                                                       n (Set.singleton Nothing)
                                                                       (varsOut mdl)
                                                           }) q cmdls'
                                 ) cmdls $ concat (fmap getVars (verifyFormulas never))
                         ) tmodels2 claims
        tmodels4 = foldl (\cur m -> Map.adjust
                                    (\entr -> let (sm,fm) = runState (gtlsToBuchi
                                                                      (\ats -> do
                                                                          mp <- get
                                                                          let (c,a,nmp) = foldl (\(chks,ass,cmp) at
                                                                                                 -> let ((n,f),nmp) = parseGTLAtom cmp (Just (modelName m,varsOut entr)) at
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
                    , claimChecks = fmap (\(_,_,f) -> f) $ Map.elems fclaims
                    }
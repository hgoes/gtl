module Language.GTL.ScadeContract
       (translateContracts)
       where

import Data.Foldable
import Data.Map as Map
import Data.Set as Set
import Language.Scade.Syntax as Sc
import Language.GTL.Syntax as GTL
import Language.GTL.Translation
import Language.GTL.ScadeAnalyzer
import Prelude hiding (foldl,foldl1,concat)

import Debug.Trace

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Sc.Declaration]
translateContracts scade gtl
  = let tp = typeMap gtl scade
    in [ translateContractScade (modelName m)
         (tp!(modelName m)) (translateContract (modelContract m))
       | Model m <- gtl ]

translateContractScade :: String -> (String,Map String TypeExpr,Map String TypeExpr) -> CanonFormula -> Sc.Declaration
translateContractScade name (_,ins,outs) f
  = let (states,_,_,_) = translateContract' f Map.empty 0 []
    in UserOpDecl
    { userOpKind = Node
    , userOpImported = False
    , userOpInterface = InterfaceStatus Nothing False
    , userOpName = name++"_testnode"
    , userOpSize = Nothing
    , userOpParams = [ VarDecl [VarId n False False] tp Nothing Nothing
                     | (n,tp) <- Map.toList ins ++ Map.toList outs ]
    , userOpReturns = [VarDecl { varNames = [VarId "test_result" False False]
                               , varType = TypeBool
                               , varDefault = Nothing
                               , varLast = Nothing
                               }]
    , userOpNumerics = []
    , userOpContent = DataDef { dataSignals = []
                              , dataLocals = []
                              , dataEquations = [StateEquation (StateMachine Nothing states) [] False]
                              }
    }

translateContract' :: CanonFormula -> Map CanonFormula Integer -> Integer -> [Sc.State] -> ([Sc.State],Map CanonFormula Integer,Integer,Integer)
translateContract' f cache cur res = case Map.lookup f cache of
  Just r -> (res,cache,r,cur)
  Nothing -> let (trans,nres,ncache,ncur)
                   = foldl (\(ctrans,cres,ccache,ccur) cl
                            -> let nxt_f1 = canonAnd (clauseNext cl) (clauseAlways cl)
                                   nxt_f2 = canonAnd nxt_f1 (Set.singleton (ClauseT { clauseVars = Map.empty
                                                                                    , clauseNext = Set.empty
                                                                                    , clauseAlways = clauseAlways cl
                                                                                    }))
                                   (rres,rcache,next_st,rcur) = translateContract' nxt_f2 ccache ccur cres
                               in ((next_st,clauseVars cl):ctrans,rres,rcache,rcur)
                           ) ([],res,Map.insert f cur cache,cur+1) f
                 new = Sc.State { stateInitial = case cur of
                                     0 -> True
                                     _ -> False
                                , stateFinal = False
                                , stateName = "st"++show cur
                                , stateData = DataDef { dataSignals = []
                                                      , dataLocals = []
                                                      , dataEquations = [SimpleEquation [Named "test_result"] (ConstBoolExpr True)]
                                                      }
                                , stateUnless = [Transition (varsToExpr v) Nothing (TargetFork Restart ("st"++show nxt))
                                                | (nxt,v) <- trans]
                                , stateUntil = []
                                , stateSynchro = Nothing
                                }
             in (new:nres,ncache,cur,cur+1)

varsToExpr :: Map String (Set Condition) -> Sc.Expr
varsToExpr mp
  | Map.null mp = ConstBoolExpr True
  | otherwise
           = foldl1 (BinaryExpr BinAnd) $ concat
             [ [ case cond of 
                    CondLT x -> BinaryExpr BinLesser nameE (ConstIntExpr x)
                    CondLTEq x -> BinaryExpr BinLessEq nameE (ConstIntExpr x)
                    CondGT x -> BinaryExpr BinGreater nameE (ConstIntExpr x)
                    CondGTEq x -> BinaryExpr BinGreaterEq nameE (ConstIntExpr x)
                    CondElem lst -> foldl1 (BinaryExpr BinOr)
                                    (fmap ((BinaryExpr BinEquals nameE).ConstIntExpr) lst)
                    CondNElem lst -> foldl1 (BinaryExpr BinAnd)
                                     (fmap ((BinaryExpr BinDifferent nameE).ConstIntExpr) lst)
               | cond <- Set.toList conds,
                 let nameE = IdExpr $ Path [name]
               ]
             | (name,conds) <- Map.toList mp ]
module Language.GTL.ScadeContract where

import Data.Map as Map
import Data.Set as Set
import Data.List as List hiding (foldl1)
import Data.Foldable
import Prelude hiding (foldl1)
import Control.Monad.Identity

import Language.GTL.LTL as LTL
import Language.GTL.Syntax as GTL
import Language.Scade.Syntax as Sc
import Language.GTL.ScadeAnalyzer
import Language.GTL.Translation

translateContracts :: [Sc.Declaration] -> [GTL.Declaration] -> [Sc.Declaration]
translateContracts scade gtl
  = let tp = typeMap gtl scade
    in [ buchiToScade (modelName m) ins outs (runIdentity $ gtlsToBuchi (return . Set.fromList) (modelContract m))
       | Model m <- gtl, let (_,ins,outs) = tp!(modelName m) ]

buchiToScade :: String -> Map String TypeExpr -> Map String TypeExpr
                -> Buchi (Set (GTL.Relation,GTL.Lit,GTL.Lit))
                -> Sc.Declaration
buchiToScade name ins outs buchi
  = UserOpDecl
    { userOpKind = Sc.Node
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
                              , dataEquations = [StateEquation
                                                 (StateMachine Nothing (buchiToStates buchi))
                                                 [] False
                                                ]
                              }
    }

startState :: Buchi (Set (GTL.Relation,GTL.Lit,GTL.Lit)) -> Sc.State
startState buchi = Sc.State
  { stateInitial = True
  , stateFinal = False
  , stateName = "init"
  , stateData = DataDef { dataSignals = []
                        , dataLocals = []
                        , dataEquations = [SimpleEquation [Named "test_result"] (ConstBoolExpr True)]
                        }
  , stateUnless = [ stateToTransition i st
                  | (i,st) <- List.filter (isStart . snd) (Map.toList buchi) ]++
                  [failTransition]
  , stateUntil = []
  , stateSynchro = Nothing
  }

failTransition :: Sc.Transition
failTransition = Transition (ConstBoolExpr True) Nothing (TargetFork Restart "fail")

failState :: Sc.State
failState = Sc.State
  { stateInitial = False
  , stateFinal = False
  , stateName = "fail"
  , stateData = DataDef { dataSignals = []
                        , dataLocals = []
                        , dataEquations = [SimpleEquation [Named "test_result"] (ConstBoolExpr False)]
                        }
  , stateUnless = []
  , stateUntil = []
  , stateSynchro = Nothing
  }

buchiToStates :: Buchi (Set (GTL.Relation,GTL.Lit,GTL.Lit)) -> [Sc.State]
buchiToStates buchi = startState buchi :
                      failState :
                      [ Sc.State
                       { stateInitial = False
                       , stateFinal = False
                       , stateName = "st"++show num
                       , stateData = DataDef { dataSignals = []
                                             , dataLocals = []
                                             , dataEquations = [SimpleEquation [Named "test_result"] (ConstBoolExpr True)]
                                             }
                       , stateUnless = [ stateToTransition to (buchi!to)
                                       | to <- Set.toList $ successors st ] ++
                                       [failTransition]
                       , stateUntil = []
                       , stateSynchro = Nothing
                       }
                     | (num,st) <- Map.toList buchi ]

stateToTransition :: Integer -> BuchiState (Set (GTL.Relation,GTL.Lit,GTL.Lit)) -> Sc.Transition
stateToTransition name st
  = Transition
    (relsToExpr $ Set.toList (vars st))
    Nothing
    (TargetFork Restart ("st"++show name))
    
                       

litToExpr :: GTL.Lit -> Sc.Expr
litToExpr (Constant n) = ConstIntExpr n
litToExpr (Variable x) = IdExpr $ Path [x]

relToExpr :: (GTL.Relation,GTL.Lit,GTL.Lit) -> Sc.Expr
relToExpr (rel,l,r)
  = BinaryExpr (case rel of
                   BinLT -> BinLesser
                   BinLTEq -> BinLessEq
                   BinGT -> BinGreater
                   BinGTEq -> BinGreaterEq
                   BinEq -> BinEquals
                   BinNEq -> BinDifferent
               ) (litToExpr l) (litToExpr r)

relsToExpr :: [(GTL.Relation,GTL.Lit,GTL.Lit)] -> Sc.Expr
relsToExpr [] = ConstBoolExpr True
relsToExpr xs = foldl1 (BinaryExpr BinAnd) (fmap relToExpr xs)

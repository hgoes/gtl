{-# LANGUAGE GADTs #-}
{-| Translate a GTL contract into a SCADE testnode.
 -  The buchi automaton representing the contract is translated into a
 -  SCADE state automaton.
 -}
module Language.GTL.ScadeContract where

import Data.Map as Map
import Data.Set as Set
import Data.List as List hiding (foldl,foldl1,find,concat)
import Data.Foldable
import Prelude hiding (foldl,foldl1,concat)
import Control.Monad.Identity
import Data.Typeable
import Data.Dynamic
import Data.Maybe

import Language.GTL.LTL as LTL
import Language.GTL.Syntax as GTL
import Language.Scade.Syntax as Sc
import Language.GTL.ScadeAnalyzer
import Language.GTL.Translation

-- | Convert all contracts of a given GTL model into SCADE testnodes.
translateContracts :: [Sc.Declaration] -- ^ The SCADE source code
                      -> [GTL.Declaration] -- ^ The content of the GTL model
                      -> [Sc.Declaration]
translateContracts scade gtl
  = let tp = typeMap gtl scade
    in concat [ [buchiToScade (modelArgs m!!0) ins outs (runIdentity $ gtlsToBuchi (return . Set.fromList) (modelContract m)),
                 buildTest (modelArgs m!!0) (userOpParams op) (userOpReturns op)
                ]
              | Model m <- gtl, let (_,ins,outs) = tp!(modelName m),
                let Just op = find (\op -> case op of 
                                       UserOpDecl {} -> userOpName op == modelArgs m!!0
                                       _ -> False) scade
              ]

-- | Constructs a SCADE node that connects the testnode with the actual implementation SCADE node.
buildTest :: String -- ^ Name of the SCADE node
             -> [Sc.VarDecl] -- ^ Input variables of the node
             -> [Sc.VarDecl] -- ^ Output variables of the node
             -> Sc.Declaration
buildTest opname ins outs = UserOpDecl
  { userOpKind = Sc.Node
  , userOpImported = False
  , userOpInterface = InterfaceStatus Nothing False
  , userOpName = opname++"_test"
  , userOpSize = Nothing
  , userOpParams = ins
  , userOpReturns = [ VarDecl { varNames = [VarId "test_result" False False]
                              , varType = TypeBool
                              , varDefault = Nothing
                              , varLast = Nothing
                              } ]
  , userOpNumerics = []
  , userOpContent = DataDef { dataSignals = []
                            , dataLocals = outs
                            , dataEquations = [SimpleEquation [ Named $ Sc.name var | varDecl <- outs,var <- varNames varDecl ]
                                               (ApplyExpr (PrefixOp $ PrefixPath $ Path [opname])
                                                [IdExpr (Path [Sc.name n]) | varDecl <- ins, n <- varNames varDecl]),
                                               SimpleEquation [ Named "test_result" ]
                                               (ApplyExpr (PrefixOp $ PrefixPath $ Path [opname++"_testnode"])
                                                ([IdExpr (Path [Sc.name n]) | varDecl <- ins, n <- varNames varDecl] ++
                                                 [IdExpr (Path [Sc.name n]) | varDecl <- outs, n <- varNames varDecl]))
                                              ]
                            }
  }

-- | Convert a buchi automaton to SCADE.
buchiToScade :: String -- ^ Name of the resulting SCADE node
                -> Map String TypeExpr -- ^ Input variables
                -> Map String TypeExpr -- ^ Output variables
                -> Buchi (Set (GTLAtom String)) -- ^ The buchi automaton
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
                                                 [] True
                                                ]
                              }
    }

-- | The starting state for a contract automaton.
startState :: Buchi (Set (GTLAtom String)) -> Sc.State
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

-- | Constructs a transition into the `failState'.
failTransition :: Sc.Transition
failTransition = Transition (ConstBoolExpr True) Nothing (TargetFork Restart "fail")

-- | The state which is entered when a contract is violated.
--   There is no transition out of this state.
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

-- | Translates a buchi automaton into a list of SCADE automaton states.
buchiToStates :: Buchi (Set (GTLAtom String)) -> [Sc.State]
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

-- | Given a state this function creates a transition into the state.
stateToTransition :: Integer -> BuchiState st (Set (GTLAtom String)) f -> Sc.Transition
stateToTransition name st
  = Transition
    (relsToExpr $ Set.toList (vars st))
    Nothing
    (TargetFork Restart ("st"++show name))

baseConstr :: Map TypeRep (Dynamic -> Sc.Expr)
baseConstr = Map.fromList [
    (typeOf (undefined::Bool), (\c -> ConstBoolExpr (unsafeFromDyn c))),
    (typeOf (undefined::Int), (\c -> ConstIntExpr (unsafeFromDyn c)))
  ]

litToExpr :: GTL.BaseType a => GTL.Expr String a -> Sc.Expr
litToExpr (ExprConst n) = fromJust (construct n baseConstr) -- FIXME: unsafe
litToExpr (ExprVar x lvl) = foldl (\e _ -> UnaryExpr UnPre e) (IdExpr $ Path [x]) [1..lvl]
litToExpr (ExprBinInt op l r) = BinaryExpr (case op of
                                               OpPlus -> BinPlus
                                               OpMinus -> BinMinus
                                               OpMult -> BinTimes
                                               OpDiv -> BinDiv) (litToExpr l) (litToExpr r)

relToExpr :: GTLAtom String -> Sc.Expr
relToExpr (GTLRel rel l r)
  = BinaryExpr (case rel of
                   BinLT -> BinLesser
                   BinLTEq -> BinLessEq
                   BinGT -> BinGreater
                   BinGTEq -> BinGreaterEq
                   BinEq -> BinEquals
                   BinNEq -> BinDifferent
               ) (litToExpr l) (litToExpr r)

relsToExpr :: [GTLAtom String] -> Sc.Expr
relsToExpr [] = ConstBoolExpr True
relsToExpr xs = foldl1 (BinaryExpr BinAnd) (fmap relToExpr xs)

{-# LANGUAGE TypeFamilies,GADTs #-}
module Language.GTL.Backend.Scade where

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.GTL.Backend
import Language.GTL.Translation
import Language.GTL.Types
import Language.Scade.Syntax as Sc
import Language.Scade.Pretty
import Language.GTL.Expression as GTL
import Language.GTL.LTL as LTL
import Data.Map as Map
import Data.Set as Set
import Data.List as List
import Data.Dynamic
import Control.Monad.Identity
import Data.Dynamic
import Data.Maybe

data Scade = Scade deriving (Show)

instance GTLBackend Scade where
  data GTLBackendModel Scade = ScadeData String [Sc.Declaration]
  backendName Scade = "scade"
  initBackend Scade [file,name] = do
    str <- readFile file
    return $ ScadeData name (scade $ alexScanTokens str)
  typeCheckInterface Scade (ScadeData name decls) (ins,outs) = do
    let (sc_ins,sc_outs) = scadeInterface name decls
    mp_ins <- scadeTypeMap sc_ins
    mp_outs <- scadeTypeMap sc_outs
    rins <- mergeTypes ins mp_ins
    routs <- mergeTypes outs mp_outs
    return (rins,routs)
  cInterface Scade (ScadeData name decls) = let (inp,outp) = scadeInterface name decls
                                            in CInterface { cIFaceIncludes = [name++".h"]
                                                          , cIFaceStateType = ["outC_"++name]
                                                          , cIFaceInputType = if Prelude.null inp
                                                                              then []
                                                                              else ["inC_"++name]
                                                          , cIFaceStateInit = \[st] -> name++"_reset(&("++st++"))"
                                                          , cIFaceIterate = \[st] inp -> case inp of
                                                               [] -> name++"(&("++st++"))"
                                                               [rinp] -> name++"(&("++rinp++"),&("++st++"))"
                                                          , cIFaceGetInputVar = \[inp] var -> inp++"."++var
                                                          , cIFaceGetOutputVar = \[st] var -> st++"."++var
                                                          , cIFaceTranslateType = scadeTranslateTypeC
                                                          , cIFaceTranslateValue = scadeTranslateValueC
                                                          }
  backendVerify Scade (ScadeData name decls) expr
    = let (inp,outp) = scadeInterface name decls
          scade = buchiToScade name (Map.fromList inp) (Map.fromList outp) (runIdentity $ gtlToBuchi (return . Set.fromList) expr)
      in do
        print $ prettyScade [scade]
        return $ Nothing

scadeTranslateTypeC :: GTLType -> String
scadeTranslateTypeC GTLInt = "kcg_int"
scadeTranslateTypeC GTLBool = "kcg_bool"
scadeTranslateTypeC rep = error $ "Couldn't translate "++show rep++" to C-type"

scadeTranslateValueC :: Dynamic -> String
scadeTranslateValueC d = case fromDynamic d of
  Just v -> show (v::Int)
  Nothing -> case fromDynamic d of
    Just v -> if v then "1" else "0"
    Nothing -> error $ "Couldn't translate "++show d++" to C-value"

scadeTypeToGTL :: Sc.TypeExpr -> Maybe GTLType
scadeTypeToGTL Sc.TypeInt = Just GTLInt
scadeTypeToGTL Sc.TypeBool = Just GTLBool
scadeTypeToGTL _ = Nothing

scadeTypeMap :: [(String,Sc.TypeExpr)] -> Either String (Map String GTLType)
scadeTypeMap tps = do
  res <- mapM (\(name,expr) -> case scadeTypeToGTL expr of
                  Nothing -> Left $ "Couldn't convert SCADE type "++show expr++" to GTL"
                  Just tp -> Right (name,tp)) tps
  return $ Map.fromList res

-- | Extract type information from a SCADE model.
--   Returns two list of variable-type pairs, one for the input variables, one for the outputs.
scadeInterface :: String -- ^ The name of the Scade model to analyze
                  -> [Sc.Declaration] -- ^ The parsed source code
                  -> ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)])
scadeInterface name (op@(Sc.UserOpDecl {}):xs)
  | Sc.userOpName op == name = (varNames' (Sc.userOpParams op),varNames' (Sc.userOpReturns op))
  | otherwise = scadeInterface name xs
    where
      varNames' :: [Sc.VarDecl] -> [(String,Sc.TypeExpr)]
      varNames' (x:xs) = (fmap (\var -> (Sc.name var,Sc.varType x)) (Sc.varNames x)) ++ varNames' xs
      varNames' [] = []
scadeInterface name (_:xs) = scadeInterface name xs
scadeInterface name [] = error $ "Couldn't find model "++show name

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
  , userOpReturns = [ VarDecl { Sc.varNames = [VarId "test_result" False False]
                              , Sc.varType = TypeBool
                              , Sc.varDefault = Nothing
                              , Sc.varLast = Nothing
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
    , userOpReturns = [VarDecl { Sc.varNames = [VarId "test_result" False False]
                               , Sc.varType = TypeBool
                               , Sc.varDefault = Nothing
                               , Sc.varLast = Nothing
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

termToExpr :: Term String -> Sc.Expr
termToExpr (VarExpr var) = foldl (\e _ -> UnaryExpr UnPre e) (IdExpr $ Path [GTL.name var]) [1..(time var)]
termToExpr (ConstExpr c) = case value c of
  IntVal x -> ConstIntExpr (fromIntegral x)
  BoolVal x -> ConstBoolExpr x
termToExpr (BinExpr tp (IntOp op) l r) = BinaryExpr (case op of
                                                        OpPlus -> BinPlus
                                                        OpMinus -> BinMinus
                                                        OpMult -> BinTimes
                                                        OpDiv -> BinDiv) (termToExpr l) (termToExpr r)

relToExpr :: GTLAtom String -> Sc.Expr
relToExpr (GTLBoolExpr expr p)
  = case expr of
  RelExpr rel l r
    -> BinaryExpr (case (if p then id else relNot) rel of
                      BinLT -> BinLesser
                      BinLTEq -> BinLessEq
                      BinGT -> BinGreater
                      BinGTEq -> BinGreaterEq
                      BinEq -> BinEquals
                      BinNEq -> BinDifferent
                  ) (termToExpr l) (termToExpr r)
  BoolConst x -> (if p then id else UnaryExpr UnNot) (ConstBoolExpr x)
  BoolVar var -> (if p then id else UnaryExpr UnNot) (termToExpr (VarExpr var))

relsToExpr :: [GTLAtom String] -> Sc.Expr
relsToExpr [] = ConstBoolExpr True
relsToExpr xs = foldl1 (BinaryExpr BinAnd) (fmap relToExpr xs)

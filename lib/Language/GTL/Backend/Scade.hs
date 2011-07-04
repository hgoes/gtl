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
import Data.Map as Map hiding (map)
import Data.Set as Set hiding (map)
import Data.List as List
import Control.Monad.Identity

import System.FilePath
import System.Process as Proc
import System.Exit (ExitCode(..))

import Text.XML.HXT.Core hiding (when)
import Text.XML.HXT.Arrow.XmlState.RunIOStateArrow (initialState)
import Text.XML.HXT.Arrow.XmlState.TypeDefs (xioUserState)
import Text.XML.HXT.DOM.TypeDefs ()

import Misc.ProgramOptions

data Scade = Scade deriving (Show)

instance GTLBackend Scade where
  data GTLBackendModel Scade = ScadeData String [Sc.Declaration] ScadeTypeMapping FilePath
  backendName Scade = "scade"
  initBackend Scade [file,name] = do
    str <- readFile file
    let decls = scade $ alexScanTokens str
    return $ ScadeData name decls (scadeTypes decls) file
  typeCheckInterface Scade (ScadeData name decls tps opFile) (ins,outs) = do
    let (sc_ins,sc_outs) = scadeInterface (scadeParseNodeName name) decls
        Just local = scadeMakeLocal (scadeParseNodeName name) tps
    mp_ins <- scadeTypeMap tps local sc_ins
    mp_outs <- scadeTypeMap tps local sc_outs
    rins <- mergeTypes ins mp_ins
    routs <- mergeTypes outs mp_outs
    return (rins,routs)
  cInterface Scade (ScadeData name decls tps opFile)
    = let (inp,outp) = scadeInterface (scadeParseNodeName name) decls
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
  backendVerify Scade (ScadeData name decls tps opFile) expr opts gtlName
    = let (inp,outp) = scadeInterface (scadeParseNodeName name) decls
          scade = buchiToScade name (Map.fromList inp) (Map.fromList outp) (runIdentity $ gtlToBuchi (return . Set.fromList) expr)
      in do
        let outputDir = (outputPath opts)
            testNodeFile = outputDir </> (gtlName ++ "-" ++ name) <.> "scade"
            proofNodeFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof") <.> "scade"
            scenarioFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof-counterex") <.> "sss"
        writeFile testNodeFile (show $ prettyScade [scade])
        writeFile proofNodeFile (show $ prettyScade [generateProver name inp outp])
        case scadeRoot opts of
          Just p -> do
            report' <- verifyScadeNodes opts p gtlName name opFile testNodeFile proofNodeFile
            case report' of
              Nothing -> return Nothing
              Just report -> do
                when (not (verified report))
                  (generateScenario scenarioFile report)
                return $ Just $ verified report
          Nothing -> return Nothing

generateProver :: String -> [(String,Sc.TypeExpr)] -> [(String,Sc.TypeExpr)] -> Sc.Declaration
generateProver name ins outs
  = UserOpDecl
    { userOpKind = Sc.Node
    , userOpImported = False
    , userOpInterface = InterfaceStatus Nothing False
    , userOpName = name ++ "_proof"
    , userOpSize = Nothing
    , userOpParams = interfaceToDeclaration ins
    , userOpReturns = [VarDecl { Sc.varNames = [VarId "test_result" False False]
                               , Sc.varType = TypeBool
                               , Sc.varDefault = Nothing
                               , Sc.varLast = Nothing
                               }]
    , userOpNumerics = []
    , userOpContent = DataDef { dataSignals = []
                              , dataLocals = interfaceToDeclaration outs
                              , dataEquations = [
                                  SimpleEquation (map (Named . fst) outs) (ApplyExpr (PrefixOp $ PrefixPath $ Path [name]) (map (IdExpr . Path . (:[]) . fst) ins))
                                  , SimpleEquation [(Named "test_result")] (ApplyExpr (PrefixOp $ PrefixPath $ Path [name ++ "_testnode"]) (map (IdExpr . Path . (:[]) . fst) (ins ++ outs)))
                                ]
                              }
    }

interfaceToDeclaration :: [(String,Sc.TypeExpr)] -> [VarDecl]
interfaceToDeclaration vars = [ VarDecl [VarId (fst v) False False] (snd v) Nothing Nothing | v <- vars]

-- | List of TCL commands
type ScadeTick = [String]
type ScadeTrace = [ScadeTick]

data Report = Report {
  verified :: Bool -- ^ Could expected contract be fulfilled?
  , node :: String -- ^ The node in test
  , errorTrace :: ScadeTrace -- ^ In case /verified == True/ contains a list of TCL commands to reproduce the error.
} deriving Show

-- | Runs the Scade design verifier and reads back its report.
verifyScadeNodes :: Options -> FilePath -> String -> String -> FilePath -> FilePath -> FilePath -> IO (Maybe Report)
verifyScadeNodes opts scadeRoot gtlName name opFile testNodeFile proofNodeFile =
  let dv = scadeRoot </> "SCADE Suite" </> "bin" </> "dv.exe"
      reportFile = (outputPath opts) </> (gtlName ++ "-" ++ name ++ "_proof_report") <.> "xml"
      verifOpts = ["-node", name ++ "_proof", opFile, testNodeFile, proofNodeFile, "-po", "test_result", "-xml", reportFile]
  in do
    (_, _, _, p) <- Proc.createProcess $
                    Proc.CreateProcess {
                      cmdspec = Proc.RawCommand dv verifOpts
                      , cwd = Nothing, env = Nothing
                      , std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe
                      , close_fds = False
                    }
    exitCode <- Proc.waitForProcess p
    case exitCode of
      ExitFailure _ -> return Nothing
      ExitSuccess -> readReport reportFile

-- | Read the XML output of the design verifier.
-- The structure is something like:
--  <prover ...>
--    <property name="test_result" status="/s/" node="/n/" ...>
--      <tick ...>
--        <input name="/i/"><value type="/t/">v</value>
--  ...
-- Where s is "Falsifiable" or "Valid" (Report.verified == True iff s == "Valid"),
-- n is the name of the tested node (will be in Report.node).
-- For each tick there will be a ScadeTick in Report.errorTrace and for each
-- input there will be a set command in that tick. Each tick will be finalized by a cycle command.
readReport :: FilePath -> IO (Maybe Report)
readReport reportFile = do
  let defaultReport = Report False "" []
      reader =
        configSysVars [] >>>
        readDocument [withShowTree yes] reportFile >>>
        getChildren >>>
        makeReport
  (r, _) <- runXIOSState (initialState defaultReport) reader
  return $ Just $ reverseTrace $ xioUserState r
  where
    makeReport :: IOStateArrow Report XmlTree XmlTree -- (XIOState Report) -> XMLTree -> IO (Report, [(XmlTree, Report)]
    makeReport =
      isTag "prover" >>>
      getChildren >>>
      isTag "property" >>>
      getNodeName &&&>
      isVerified `orElse` generateTrace
    getNodeName :: IOStateArrow Report XmlTree String
    getNodeName =
      getAttrValue "node" >>> changeUserState (\name r -> r {node = name})
    isVerified :: IOStateArrow Report XmlTree XmlTree
    isVerified =
      hasAttrValue "status" isVerified' >>>
      changeUserState (\_ r -> r { verified = True })
      where
        isVerified' status
          | status == "Valid" = True
          | status == "Falsifiable" = False
          | otherwise = False
    generateTrace :: IOStateArrow Report XmlTree XmlTree
    generateTrace = deep readTick
      where
        readTick =
          isTag "tick" >>>
          startCycle >>>
          readCycleActions &&&> makeCycleCommand
          where
            startCycle = changeUserState (\_ r -> r {errorTrace = [] : (errorTrace r)})
            readCycleActions =
              getChildren >>>
              isTag "input" >>> makeSetCommand &&&>
              getChildren >>>
              isTag "value" >>> getChildren >>> valueSetCommand
            -- TCL command generation
            makeSetCommand =
              getAttrValue "name" >>>
              changeUserState (\n r -> r {errorTrace = (("SSM::Set " ++ (node r) ++ "/" ++ n) : (traceHead r)) : (traceTail r)})
            valueSetCommand =
              getText >>>
              changeUserState (\v r -> r {errorTrace = (((commandHead r) ++ " " ++ v) : (commandTail r)) : (traceTail r)})
            makeCycleCommand = changeUserState (\_ r -> r {errorTrace = ("SSM::Cycle" : (traceHead r)) : (traceTail r)})
            -- trace access
            traceHead = head . errorTrace
            traceTail = tail . errorTrace
            commandHead = head . traceHead
            commandTail = tail . traceHead
    -- After parsing the ticks and the commands in there are in reverse order -> correct that.
    reverseTrace :: Report -> Report
    reverseTrace r = r { errorTrace = reverse . (map reverse) . errorTrace $ r }

runXIOSState :: XIOState s -> IOStateArrow s XmlTree c -> IO (XIOState s, [c])
runXIOSState s0 f = runIOSLA (emptyRoot >>> f) s0 undefined
  where
    emptyRoot = root [] []

-- | Tests if we are at a node of type
-- </name/ ...>...
isTag name = isElem >>> hasName name

-- | Execute f and g on input, use output state of f for g and return
-- the result only of g.
-- Equivalent to f &&& g >>> arr snd.
(&&&>) :: IOStateArrow s a b -> IOStateArrow s a c -> IOStateArrow s a c
f &&&> g = f &&& g >>> arr snd
{-
-- For efficiency
IOSLA f &&&> IOSLA g = IOSLA $ \ s x -> do
                   (s', _) <- f s  x
                   (s'', y) <- g s' x
                   return (s'', y)
-}

--- | Generate the scenario file for the report.
generateScenario :: FilePath -> Report -> IO()
generateScenario scenarioFile report =
  writeFile scenarioFile $ (unlines . (map unlines) . errorTrace $ report)

scadeTranslateTypeC :: GTLType -> String
scadeTranslateTypeC GTLInt = "kcg_int"
scadeTranslateTypeC GTLBool = "kcg_bool"
scadeTranslateTypeC rep = error $ "Couldn't translate "++show rep++" to C-type"

scadeTranslateValueC :: GTLConstant -> String
scadeTranslateValueC d = case unfix d of
  GTLIntVal v -> show v
  GTLBoolVal v -> if v then "1" else "0"
  _ -> error $ "Couldn't translate "++show d++" to C-value"

scadeTypeToGTL :: ScadeTypeMapping -> ScadeTypeMapping -> Sc.TypeExpr -> Maybe GTLType
scadeTypeToGTL _ _ Sc.TypeInt = Just GTLInt
scadeTypeToGTL _ _ Sc.TypeBool = Just GTLBool
scadeTypeToGTL _ _ Sc.TypeReal = Just GTLFloat
scadeTypeToGTL _ _ Sc.TypeChar = Just GTLByte
scadeTypeToGTL g l (Sc.TypePath (Path path)) = do
  tp <- scadeLookupType g l path
  scadeTypeToGTL g Map.empty tp
scadeTypeToGTL g l (Sc.TypeEnum enums) = Just (GTLEnum enums)
scadeTypeToGTL g l (Sc.TypePower tp expr) = do
  rtp <- scadeTypeToGTL g l tp
  case expr of
    ConstIntExpr 1 -> return rtp
    ConstIntExpr n -> return (GTLArray n rtp)
scadeTypeToGTL _ _ _ = Nothing

data ScadeTypeInfo = ScadePackage ScadeTypeMapping
                   | ScadeType Sc.TypeExpr
                   deriving Show

type ScadeTypeMapping = Map String ScadeTypeInfo

scadeLookupType :: ScadeTypeMapping -> ScadeTypeMapping -> [String] -> Maybe Sc.TypeExpr
scadeLookupType global local name = case scadeLookupType' local name of
  Nothing -> scadeLookupType' global name
  Just res -> Just res
  where
    scadeLookupType' mp [] = Nothing
    scadeLookupType' mp (n:ns) = do
      res <- Map.lookup n mp
      case res of
        ScadeType expr -> case ns of
          [] -> Just expr
          _ -> Nothing
        ScadePackage nmp -> scadeLookupType' nmp ns

scadeMakeLocal :: [String] -> ScadeTypeMapping -> Maybe ScadeTypeMapping
scadeMakeLocal [_] mp = Just mp
scadeMakeLocal (x:xs) mp = do
  entr <- Map.lookup x mp
  case entr of
    ScadePackage nmp -> scadeMakeLocal xs nmp
    ScadeType _ -> Nothing

scadeTypes :: [Sc.Declaration] -> ScadeTypeMapping
scadeTypes [] = Map.empty
scadeTypes ((TypeBlock tps):xs) = foldl (\mp (TypeDecl _ name cont) -> case cont of
                                            Nothing -> mp
                                            Just expr -> Map.insert name (ScadeType expr) mp
                                        ) (scadeTypes xs) tps
scadeTypes ((PackageDecl _ name decls):xs) = Map.insert name (ScadePackage (scadeTypes decls)) (scadeTypes xs)
scadeTypes (_:xs) = scadeTypes xs

scadeTypeMap :: ScadeTypeMapping -> ScadeTypeMapping -> [(String,Sc.TypeExpr)] -> Either String (Map String GTLType)
scadeTypeMap global local tps = do
  res <- mapM (\(name,expr) -> case scadeTypeToGTL global local expr of
                  Nothing -> Left $ "Couldn't convert SCADE type "++show expr++" to GTL"
                  Just tp -> Right (name,tp)) tps
  return $ Map.fromList res

scadeParseNodeName :: String -> [String]
scadeParseNodeName name = case break (=='.') name of
  (rname,[]) -> [rname]
  (name1,rest) -> name1:(scadeParseNodeName (tail rest))

-- | Extract type information from a SCADE model.
--   Returns two list of variable-type pairs, one for the input variables, one for the outputs.
scadeInterface :: [String] -- ^ The name of the Scade model to analyze
                  -> [Sc.Declaration] -- ^ The parsed source code
                  -> ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)])
scadeInterface (name@(n1:names)) ((Sc.PackageDecl _ pname decls):xs)
  | n1==pname = scadeInterface names decls
  | otherwise = scadeInterface name xs
scadeInterface [name] (op@(Sc.UserOpDecl {}):xs)
  | Sc.userOpName op == name = (varNames' (Sc.userOpParams op),varNames' (Sc.userOpReturns op))
  | otherwise = scadeInterface [name] xs
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
                -> Buchi (Set (TypedExpr String)) -- ^ The buchi automaton
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
startState :: Buchi (Set (TypedExpr String)) -> Sc.State
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
buchiToStates :: Buchi (Set (TypedExpr String)) -> [Sc.State]
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
stateToTransition :: Integer -> BuchiState st (Set (TypedExpr String)) f -> Sc.Transition
stateToTransition name st
  = Transition
    (relsToExpr $ Set.toList (vars st))
    Nothing
    (TargetFork Restart ("st"++show name))

exprToScade :: TypedExpr String -> Sc.Expr
exprToScade expr = case getValue expr of
  Var name lvl -> foldl (\e _ -> UnaryExpr UnPre e) (IdExpr $ Path [name]) [1..lvl]
  Value val -> valueToScade (getType expr) val
  BinIntExpr op l r -> Sc.BinaryExpr (case op of
                                         OpPlus -> BinPlus
                                         OpMinus -> BinMinus
                                         OpMult -> BinTimes
                                         OpDiv -> BinDiv
                                     ) (exprToScade (unfix l)) (exprToScade (unfix r))
  BinRelExpr rel l r -> BinaryExpr (case rel of
                                      BinLT -> BinLesser
                                      BinLTEq -> BinLessEq
                                      BinGT -> BinGreater
                                      BinGTEq -> BinGreaterEq
                                      BinEq -> BinEquals
                                      BinNEq -> BinDifferent
                                   ) (exprToScade (unfix l)) (exprToScade (unfix r))
  UnBoolExpr GTL.Not p -> Sc.UnaryExpr Sc.UnNot (exprToScade (unfix p))

valueToScade :: GTLType -> GTLValue (Fix (Typed (Term String))) -> Sc.Expr
valueToScade _ (GTLIntVal v) = Sc.ConstIntExpr v
valueToScade _ (GTLBoolVal v) = Sc.ConstBoolExpr v
valueToScade _ (GTLByteVal v) = Sc.ConstIntExpr (fromIntegral v)
valueToScade _ (GTLEnumVal v) = Sc.IdExpr $ Path [v]
valueToScade _ (GTLArrayVal xs) = Sc.ArrayExpr (fmap (exprToScade.unfix) xs)
valueToScade _ (GTLTupleVal xs) = Sc.ArrayExpr (fmap (exprToScade.unfix) xs)

relsToExpr :: [TypedExpr String] -> Sc.Expr
relsToExpr [] = Sc.ConstBoolExpr True
relsToExpr xs = foldl1 (Sc.BinaryExpr Sc.BinAnd) (fmap exprToScade xs)

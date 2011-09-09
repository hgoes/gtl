{-# LANGUAGE TypeFamilies,GADTs #-}
{-| SCADE is a synchronous specification language for software-components.
    It provides a code-generator and a verification tool. -}
module Language.GTL.Backend.Scade
       (Scade(..))
       where

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.GTL.Backend
import Language.GTL.Translation
import Language.GTL.Types
import Language.Scade.Syntax as Sc
import Language.Scade.Pretty
import Language.GTL.Expression as GTL
import Language.GTL.DFA
import Data.Map as Map hiding (map)
import Control.Monad.Identity
import Data.List as List (intercalate, null, mapAccumL)
import Data.Maybe (maybeToList, isJust)
import Data.Set as Set (member)

import System.FilePath
import System.Process as Proc
import System.Exit (ExitCode(..))

import Text.XML.HXT.Core hiding (when)
import Text.XML.HXT.Arrow.XmlState.RunIOStateArrow (initialState)
import Text.XML.HXT.Arrow.XmlState.TypeDefs (xioUserState)
import Text.XML.HXT.DOM.TypeDefs ()

import Misc.ProgramOptions

-- | The SCADE backend
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
  backendVerify Scade (ScadeData node decls tps opFile) cy expr locals opts gtlName
    = let nodePath = scadeParseNodeName node
          name = (intercalate "_" nodePath)
          (inp,outp) = scadeInterface nodePath decls
          buchi = gtl2ba (Just cy) expr
          dfa = fmap (renameDFAStates . minimizeDFA) $ determinizeBA buchi
          scade = fmap (dfaToScade name inp outp locals) dfa
          --scade = buchiToScade name inp outp ()
      in do
        let outputDir = (outputPath opts)
            testNodeFile = outputDir </> (gtlName ++ "-" ++ name) <.> "scade"
            proofNodeFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof") <.> "scade"
            scenarioFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof-counterex") <.> "sss"
        dump opts gtlName name buchi
        case scade of
          Nothing -> putStrLn "Could not transform Buchi automaton into deterministic automaton" >> return Nothing
          Just scade' -> do
            writeFile testNodeFile (show $ prettyScade [scade'])
            writeFile proofNodeFile (show $ prettyScade [generateProver name nodePath inp outp])
            if not (dryRun opts) then
              case scadeRoot opts of
                Just p -> do
                  reportFile' <- verifyScadeNodes opts p gtlName name opFile testNodeFile proofNodeFile
                  case reportFile' of
                    Nothing -> putStrLn "Error while running Scade verifier" >> return Nothing
                    Just reportFile -> do
                      report' <- readReport reportFile
                      case report' of
                        Nothing -> putStrLn "Error reading back Scade verifier report" >> return Nothing
                        Just report -> do
                          when (not (verified report))
                            (generateScenario scenarioFile report)
                          return $ Just $ verified report
                Nothing -> putStrLn "Could not run Scade prover: SCADE_ROOT not given" >> return Nothing
              else return Nothing

-- | Deals with dumping debug informations.
dump opts gtlName name buchi =
  if "dump-buchi" `Set.member` (debug opts) then
    writeFile ((outputPath opts) </> (gtlName ++ name ++ "-buchi" ++ ".txt")) (show buchi)
  else return ()

generateProver :: String -> [String] -> [(String,Sc.TypeExpr)] -> [(String,Sc.TypeExpr)] -> Sc.Declaration
generateProver name nodePath ins outs
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
                                  SimpleEquation (map (Named . fst) outs) (ApplyExpr (PrefixOp $ PrefixPath $ Path nodePath) (map (IdExpr . Path . (:[]) . fst) ins))
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
verifyScadeNodes :: Options -> FilePath -> String -> String -> FilePath -> FilePath -> FilePath -> IO (Maybe FilePath)
verifyScadeNodes opts scadeRoot gtlName name opFile testNodeFile proofNodeFile =
  let dv = scadeRoot </> "SCADE Suite" </> "bin" </> "dv.exe"
      reportFile = (outputPath opts) </> (gtlName ++ "-" ++ name ++ "_proof_report") <.> "xml"
      verifOpts = ["-node", name ++ "_proof", opFile, testNodeFile, proofNodeFile, "-po", "test_result", "-xml", reportFile]
      outputStream = if (verbosity opts) > 0 then Inherit else CreatePipe
  in do
    (_, _, _, p) <- Proc.createProcess $
                    Proc.CreateProcess {
                      cmdspec = Proc.RawCommand dv verifOpts
                      , cwd = Nothing, env = Nothing
                      , std_in = CreatePipe, std_out = outputStream, std_err = outputStream
                      , close_fds = False
                    }
    exitCode <- Proc.waitForProcess p
    case exitCode of
      ExitFailure _ -> return Nothing
      ExitSuccess -> return $ Just reportFile

-- | Read the XML output of the design verifier.
-- The structure is something like:
--  <prover ...>
--    <property name="test_result" status="/s/" node="/n/" ...>
--      <tick ...>
--        <input name="/i/">
--          <value type="/t/">v</value>
--        </input>
--        <input name="/i/">
--          <composite>
--            <value type="/t/">v1</value>
--            <value type="/t/">v2</value>
--          </composite>
--        </input>
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
              getChildren >>> valueSetCommand
            -- TCL command generation
            makeSetCommand =
              getAttrValue "name" >>>
              changeUserState (\n r -> r {errorTrace = (("SSM::set " ++ (node r) ++ "/" ++ n) : (traceHead r)) : (traceTail r)})
            valueSetCommand :: IOStateArrow Report XmlTree String
            valueSetCommand =
              (compositeValue `orElse` singleValue) >>> saveValue
            compositeValue =
              isTag "composite" >>>
              deep (
                singleValue
              ) >.
              (intercalate ",") >>> arr addParens
            singleValue =
              isTag "value" >>> getChildren >>> getText
            saveValue = changeUserState (\v r -> r {errorTrace = (((commandHead r) ++ " " ++ v) : (commandTail r)) : (traceTail r)})
            makeCycleCommand = changeUserState (\_ r -> r {errorTrace = ("SSM::cycle" : (traceHead r)) : (traceTail r)})
            -- trace access
            traceHead = head . errorTrace
            traceTail = tail . errorTrace
            commandHead = head . traceHead
            commandTail = tail . traceHead
            addParens s = "(" ++ s ++ ")"
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

-- | Convert a DFA to Scade.
dfaToScade :: String -- ^ Name of the resulting SCADE node
                -> [(String, TypeExpr)] -- ^ Input variables
                -> [(String, TypeExpr)] -- ^ Output variables
                -> Map String GTLType
                -> DFA [TypedExpr String] Integer -- ^ The DFA
                -> Sc.Declaration

dfaToScade name ins outs locals dfa
  = UserOpDecl
    { userOpKind = Sc.Node
    , userOpImported = False
    , userOpInterface = InterfaceStatus Nothing False
    , userOpName = name++"_testnode"
    , userOpSize = Nothing
    , userOpParams = [ VarDecl [VarId n False False] tp Nothing Nothing
                     | (n,tp) <- ins ++ outs ]
    , userOpReturns = [VarDecl { Sc.varNames = [VarId "test_result" False False]
                               , Sc.varType = TypeBool
                               , Sc.varDefault = Nothing
                               , Sc.varLast = Nothing
                               }]
    , userOpNumerics = []
    , userOpContent = DataDef { dataSignals = []
                              , dataLocals = declarationsToScade $ Map.toList locals
                              , dataEquations = [StateEquation
                                                 (StateMachine Nothing (dfaToStates dfa))
                                                 [] True
                                                ]
                              }
    }

-- | Translates a buchi automaton into a list of SCADE automaton states.
dfaToStates :: DFA [TypedExpr String] Integer -> [Sc.State]
dfaToStates dfa = failState :
                  [ Sc.State
                   { stateInitial = s == dfaInit dfa
                   , stateFinal = False
                   , stateName = "st" ++ (show s)
                   , stateData = DataDef { dataSignals = []
                                         , dataLocals = []
                                         , dataEquations = [SimpleEquation [Named "test_result"] (ConstBoolExpr True)]
                                         }
                   , stateUnless = [ stateToTransition cond trg
                                   | (cond, trg) <- Map.toList trans, not (List.null cond) ] ++
                                   -- put unconditional transition at the end if available
                                   (maybeToList $ fmap (stateToTransition []) $ Map.lookup [] trans) ++
                                   [failTransition]
                   , stateUntil = []
                   , stateSynchro = Nothing
                   }
                 | (s, trans) <- Map.toList (unTotal $ dfaTransitions dfa) ]

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

-- | Given a state this function creates a transition into the state.
stateToTransition :: [TypedExpr String] -> Integer -> Sc.Transition
stateToTransition cond trg =
  let (e, a) = relsToExpr cond
  in Transition
      e
      (fmap Sc.ActionDef a)
      (TargetFork Restart ("st"++show trg))

exprToScade :: TypedExpr String -> (Sc.Expr, Maybe Sc.DataDef)
exprToScade expr = case getValue expr of
  Var name lvl _ -> (foldl (\e _ -> UnaryExpr UnPre e) (IdExpr $ Path [name]) [1..lvl], Nothing)
  Value val -> (valueToScade (getType expr) val, Nothing)
  BinIntExpr op l r ->
    let (lExpr, lAssign) = exprToScade (unfix l)
        (rExpr, rAssign) = exprToScade (unfix r)
    in (Sc.BinaryExpr (case op of
                         OpPlus -> BinPlus
                         OpMinus -> BinMinus
                         OpMult -> BinTimes
                         OpDiv -> BinDiv
                     ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  BinBoolExpr op l r ->
    let (lExpr, lAssign) = exprToScade (unfix l)
        (rExpr, rAssign) = exprToScade (unfix r)
    in (Sc.BinaryExpr (case op of
                        GTL.And -> Sc.BinAnd
                        GTL.Or -> Sc.BinOr
                      ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  BinRelExpr BinEq l r -> mkEqExprBinEquals (unfix l) (unfix r)
  BinRelExpr rel l r ->
    let (lExpr, lAssign) = exprToScade (unfix l)
        (rExpr, rAssign) = exprToScade (unfix r)
    in (BinaryExpr (case rel of
                      BinLT -> BinLesser
                      BinLTEq -> BinLessEq
                      BinGT -> BinGreater
                      BinGTEq -> BinGreaterEq
                      BinNEq -> BinDifferent
                   ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  UnBoolExpr GTL.Not p -> first (Sc.UnaryExpr Sc.UnNot) (exprToScade (unfix p))
  GTL.IndexExpr r i -> first (flip Sc.IndexExpr $ (Sc.ConstIntExpr i)) (exprToScade $ unfix r)

-- | If on the lhs of an equality expression a state output variable is found
-- this expression is transformed into an assignment on the transition.
mkEqExprBinEquals :: TypedExpr String -> TypedExpr String -> (Sc.Expr, Maybe Sc.DataDef)
mkEqExprBinEquals l r = case getValue l of
  (Var name lvl StateOut) -> (Sc.ConstBoolExpr True, Just $ Sc.DataDef [] [] [SimpleEquation [Named name] (exprToScadeNoAssigns r)])
  _ ->
    let (lExpr, lAssign) = exprToScade l
        (rExpr, rAssign) = exprToScade r
    in (BinaryExpr BinEquals lExpr rExpr
        , mergeAssigns lAssign rAssign)
-- | Merge two data definitions for one transition.
mergeAssigns :: Maybe Sc.DataDef -> Maybe Sc.DataDef -> Maybe Sc.DataDef
mergeAssigns = maybeComb (\d1 d2 -> DataDef (dataSignals d1 ++ dataSignals d2) (dataLocals d1 ++ dataLocals d2) (dataEquations d1 ++ dataEquations d2))
  where
    maybeComb f (Just x) (Just y) = Just $ f x y
    maybeComb _ Nothing y = y
    maybeComb _ x Nothing = x

exprToScadeNoAssigns e =
  let (e', a) = exprToScade e
  in if isJust a then error "assignment not allowed here" else e'

valueToScade :: GTLType -> GTLValue (Fix (Typed (Term String))) -> Sc.Expr
valueToScade _ (GTLIntVal v) = Sc.ConstIntExpr v
valueToScade _ (GTLBoolVal v) = Sc.ConstBoolExpr v
valueToScade _ (GTLByteVal v) = Sc.ConstIntExpr (fromIntegral v)
valueToScade _ (GTLEnumVal v) = Sc.IdExpr $ Path [v]
valueToScade _ (GTLArrayVal xs) = Sc.ArrayExpr (fmap (exprToScadeNoAssigns.unfix) xs) -- no assignments should be generated inside index expression
valueToScade _ (GTLTupleVal xs) = Sc.ArrayExpr (fmap (exprToScadeNoAssigns.unfix) xs) -- or tuple expressions

declarationsToScade :: [(String, GTLType)] -> [Sc.VarDecl]
declarationsToScade = concat . map declarationsToScade'
  where
    declarationsToScade' (n, GTLTuple ts) = makeTupleDecls n [] ts
    declarationsToScade' (n, t) = [Sc.VarDecl [Sc.VarId n False False] (gtlTypeToScade t) Nothing Nothing]

    -- Tuples are declared as follows:
    -- for every entry x : (a0, a1, ..., an) there is a variable x_i : ai declared.
    -- If tuples are nested, this scheme is extended for every layer:
    -- x : ((a0, a1), a2) becomes x_0_0 : a0; x_0_1 : a1; x_1 : a2;
    makeTupleDecls n indcs ts  = concat $ snd $ mapAccumL (makeTupleDecl n indcs) 0 ts
      where
        makeTupleDecl :: String -> [Int] -> Int -> GTLType -> (Int, [Sc.VarDecl])
        makeTupleDecl n indcs indx (GTLTuple ts) = (indx + 1, makeTupleDecls n (indx : indcs) ts)
        makeTupleDecl n indcs indx t = (indx + 1, [Sc.VarDecl [Sc.VarId (n ++ (expandName indcs) ++ "_" ++ show indx) False False] (gtlTypeToScade t) Nothing Nothing])
        expandName = foldl (\n i -> n ++ "_" ++ show i ) ""

gtlTypeToScade :: GTLType -> Sc.TypeExpr
gtlTypeToScade GTLInt = Sc.TypeInt
-- gtlTypeToScade GTLByte = ?
gtlTypeToScade GTLBool = Sc.TypeBool
gtlTypeToScade GTLFloat = Sc.TypeReal
-- gtlTypeToScade (GTLEnum decls) = Sc.TypeEnum decls -- We can't use this one here as we may want to refer to a already declared enum. That information is lost.
-- So we're missing something like GTLTypeVar String just like Sc.TypePath.
gtlTypeToScade (GTLArray size t) = Sc.TypePower (gtlTypeToScade t) (Sc.ConstIntExpr size)
--gtlTypeToScade (GTLTuple ts) = map gtlTypeToScade ts

apPairs f g = \(x1,y1) (x2,y2) -> (f x1 x2, g y1 y2)

relsToExpr :: [TypedExpr String] -> (Sc.Expr, Maybe Sc.DataDef)
relsToExpr [] = (Sc.ConstBoolExpr True, Nothing)
relsToExpr xs = foldl1 (apPairs (Sc.BinaryExpr Sc.BinAnd) mergeAssigns) (fmap exprToScade xs)

{-# LANGUAGE TypeFamilies,GADTs,FlexibleContexts #-}
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
import Data.Map as Map hiding (map, filter, foldl)
import Data.List as List (intercalate, mapAccumL, intersperse, findIndex)
import Data.Maybe (isJust)
import Data.Set as Set (member)
import qualified Data.Generics.Aliases as Syb (orElse)

import Control.Monad.Error.Class (MonadError(..))

import System.FilePath
import System.Process as Proc
import System.Exit (ExitCode(..))
import System.IO (hGetLine,hIsEOF)

import Text.XML.HXT.Core hiding (when)
import Text.XML.HXT.DOM.TypeDefs ()

import Misc.ProgramOptions

-- | The SCADE backend
data Scade = Scade deriving (Show)

x2s :: Options -> FilePath -> IO String
x2s opts fp = case (scadeRoot opts) of
  Nothing -> return ""
  Just p -> readProcess (p </> "SCADE Suite" </> "bin" </> "x2s613.exe") [fp] ""

instance GTLBackend Scade where
  data GTLBackendModel Scade = ScadeData { scadeOperatorName :: [String]
                                         , scadeFileContent :: [Sc.Declaration]
                                         , scadeTypeMapping :: ScadeTypeMapping
                                         , scadeFileName :: FilePath
                                         }
  backendName Scade = "scade"
  initBackend Scade opts [file,name] = do
    str <- case takeExtension file of
      ".scade" -> readFile file
      ".xscade" -> x2s opts file
    let decls = scade $ alexScanTokens str
    return $ ScadeData (splitScadeName name) decls (scadeTypes decls) file
  backendGetAliases Scade (ScadeData name decls types opFile)
    = Map.mapMaybe (\t -> case t of
                       ScadeType tp -> scadeTypeToGTL types Map.empty tp
                       _ -> Nothing) types
  typeCheckInterface Scade (ScadeData name decls types opFile) (ins,outs) = do
    let (sc_ins,sc_outs,_) = scadeInterface name decls
        Just local = scadeMakeLocal name types
    mp_ins <- scadeTypeMap types local sc_ins
    mp_outs <- scadeTypeMap types local sc_outs
    rins <- mergeTypes ins mp_ins
    routs <- mergeTypes outs mp_outs
    return (rins,routs)

  cInterface Scade (ScadeData name decls types opFile)
    = let (inp,outp,kind) = scadeInterface name decls
          rname = concat $ intersperse "_" name
          splitLast [x] = ([],x)
          splitLast (x:xs) = let (xs',y) = splitLast xs
                             in (x:xs',y)
          resetName xs = let (rest,x) = splitLast xs
                         in x:"reset":rest
      in CInterface { cIFaceIncludes = [rname++".h"]
                    , cIFaceStateType = case kind of
                         Node -> [("outC_"++rname,"",True)]
                         Function -> [ scadeTranslateTypeC gtp
                                     | (vname,tp) <- outp,
                                       let Just gtp = scadeTypeToGTL types Map.empty tp ]
                    , cIFaceInputType = [ scadeTranslateTypeC gtp
                                        | (vname,tp) <- inp,
                                          let Just gtp = scadeTypeToGTL types Map.empty tp ]
                    , cIFaceStateInit = \st -> case kind of
                         Node -> case st of
                           [st'] -> (concat $ intersperse "_" $ resetName name) ++ "(&("++st'++"))"
                         Function -> ""
                    , cIFaceIterate = \st inp -> case kind of
                         Node -> case st of
                           [st'] -> rname++"("++(concat $ intersperse "," (inp++[st']))++")"
                         Function -> rname++"("++(concat $ intersperse "," (inp++st))++")"
                    , cIFaceGetInputVar = \vars var idx -> case List.findIndex (\(n,_) -> n==var) inp of
                         Nothing -> Nothing -- error $ show name++" can't find "++show var++" in "++show inp
                         Just i -> Just $ (vars!!i)++(case idx of
                                                         [] -> ""
                                                         _ -> concat $ fmap (\x -> "["++show x++"]") idx)
                    , cIFaceGetOutputVar = \st var idx -> case kind of
                         Node -> case st of
                           [st'] -> Just $ st'++"."++var++(case idx of
                                                              [] -> ""
                                                              _ -> concat $ fmap (\x -> "["++show x++"]") idx)
                         Function -> case List.findIndex (\(n,_) -> n==var) outp of
                           Nothing -> Nothing --error $ show name++" can't find "++show var++" in "++show outp
                           Just i -> Just $ (st!!i)++(case idx of
                                                         [] -> ""
                                                         _ -> concat $ fmap (\x -> "["++show x++"]") idx)
                    , cIFaceTranslateType = scadeTranslateTypeC
                    , cIFaceTranslateValue = scadeTranslateValueC
                    }
  backendVerify Scade (ScadeData node decls types opFile) cy exprs locals init constVars opts gtlName
    = let name = (intercalate "_" node)
          rname = intercalate "::" node
          (inp,outp,kind) = scadeInterface node decls
          scade = do
            dfas <- sequence $ fmap (\expr -> determinizeBA (gtl2ba (Just cy) expr)) exprs
            return $ dfasToScade types name inp outp locals init $ fmap renameDFAStates dfas
      in do
        let outputDir = (outputPath opts)
            testNodeFile = outputDir </> (gtlName ++ "-" ++ name) <.> "scade"
            proofNodeFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof") <.> "scade"
            --scenarioFile = outputDir </> (gtlName ++ "-" ++ name ++ "-proof-counterex") <.> "sss"
        --dump opts gtlName name buchi
        case scade of
          Nothing -> putStrLn "Could not transform Buchi automaton into deterministic automaton" >> return Nothing
          Just scade' -> do
            writeFile testNodeFile (show $ prettyScade [scade'])
            writeFile proofNodeFile (show $ prettyScade [generateProver types name [name] node inp outp constVars])
            if not (dryRun opts) then
              do
                reportFile' <- verifyScadeNodes opts gtlName name opFile testNodeFile proofNodeFile
                case reportFile' of
                  Nothing -> putStrLn "Error while running Scade verifier" >> return Nothing
                  Just reportFile -> do
                    report <- readReport reportFile
                    mapM (\prop -> if propStatus prop
                                   then return ()
                                   else (writeFile (outputDir </> (gtlName++"-"++name++"-"++(propName prop)++"-counterex") <.> "sss")
                                         (propertyToReport (Just rname) prop))
                         ) (properties report)
                    return $ Just $ all propStatus (properties report)
              else return Nothing

splitScadeName :: String -> [String]
splitScadeName xs = let (cur,all) = splitScadeName' xs
                    in case cur of
                      [] -> all
                      _ -> (cur:all)
  where
    splitScadeName' (':':':':xs) = let (cur,all) = splitScadeName' xs in ("",cur:all)
    splitScadeName' (x:xs) = let (cur,all) = splitScadeName' xs in (x:cur,all)
    splitScadeName' [] = ("",[])

-- | Deals with dumping debug informations.
dump opts gtlName name buchi =
  if "dump-buchi" `Set.member` (debug opts) then
    writeFile ((outputPath opts) </> (gtlName ++ name ++ "-buchi" ++ ".txt")) (show buchi)
  else return ()

generateProver :: ScadeTypeMapping
                -> String
                -> [String] -> [String] -> [(String,Sc.TypeExpr)] -> [(String,Sc.TypeExpr)]
                -> Map String (GTLType, GTLConstant) -- ^ Constant variables
                -> Sc.Declaration
generateProver types name names nodePath ins outs constVars =
  let nonConstInp = filterNonConst constVars ins
  in UserOpDecl
    { userOpKind = Sc.Node
    , userOpImported = False
    , userOpInterface = InterfaceStatus Nothing False
    , userOpName = name ++ "_proof"
    , userOpSize = Nothing
    , userOpParams = interfaceToDeclaration nonConstInp
    , userOpReturns = [VarDecl { Sc.varNames = [VarId "test_result" False False]
                               , Sc.varType = TypeBool
                               , Sc.varDefault = Nothing
                               , Sc.varLast = Nothing
                               }]
    , userOpNumerics = []
    , userOpContent = DataDef { dataSignals = []
                              , dataLocals = interfaceToDeclaration outs ++ (declareConstVars types constVars)
                              , dataEquations =
                                (constAssign constVars) ++
                                [SimpleEquation (map (Named . fst) outs) (ApplyExpr (PrefixOp $ PrefixPath $ Path nodePath) (map (IdExpr . Path . (:[]) . fst) ins))
                                ,SimpleEquation [(Named "test_result")]
                                 (case names of
                                     [] -> ConstBoolExpr True
                                     _ -> foldl1 (BinaryExpr BinAnd) $
                                          fmap (\name -> ApplyExpr (PrefixOp $ PrefixPath $ Path [name ++ "_testnode"]) (map (IdExpr . Path . (:[]) . fst) (ins ++ outs))) names)
                                ]
                              }
    }

interfaceToDeclaration :: [(String,Sc.TypeExpr)] -> [VarDecl]
interfaceToDeclaration vars = [ VarDecl [VarId (fst v) False False] (snd v) Nothing Nothing | v <- vars]

filterNonConst :: Ord a => Map a b -> [(a,c)] -> [(a,c)]
filterNonConst constVars = filter (not . (flip Map.member $ constVars) . fst)

data Prover = Prover
              { proverResult :: Bool
              , strategy :: String 
              , properties :: [Property]
              } deriving Show

data Property = Property
                { propName :: String
                , propStatus :: Bool
                , propNode :: String
                , propTrace :: [ScadeTick]
                } deriving Show

data ScadeTick = ScadeTick
                 { tickCycle :: Int
                 , tickContent :: [ScadeTickAssignment]
                 } deriving Show

data ScadeTickAssignment = InputAssignment String ScadeTickValue
                         | OutputAssignment String ScadeTickValue
                         deriving Show

data ScadeTickValue = SingleData String String
                    | CompositeData [ScadeTickValue]
                    deriving Show

renderTickValue :: ScadeTickValue -> String
renderTickValue (SingleData _ v) = v
renderTickValue (CompositeData vs) = "("++intercalate "," (fmap renderTickValue vs)++")"

propertyToReport :: Maybe String -> Property -> String
propertyToReport node prop
  = unlines $ concat
    [ [ "SSM::set "++rnode++"/"++name++" "++renderTickValue val
      | InputAssignment name val <- tickContent tick ]
      ++ ["SSM::cycle"]
    | tick <- propTrace prop ]
  where
    rnode = case node of
      Nothing -> propNode prop
      Just n -> n

instance XmlPickler Prover where
  xpickle = xpElem "prover" $
            xpWrap (\(res,strat,props) -> Prover res strat props,
                    \prov -> (proverResult prov,strategy prov,properties prov)) $
            xpTriple (xpWrap (\txt -> case txt of
                                 "Ok" -> True
                                 _ -> False,
                              \res -> if res then "Ok" else "Failed") $ xpTextAttr "result")
            (xpTextAttr "strategy")
            (xpList xpickle)

instance XmlPickler Property where
  xpickle = xpElem "property" $
            xpWrap (\(name,st,node,len,cont) -> Property name st node cont,
                    \p -> (propName p,propStatus p,propNode p,Just $ length $ propTrace p,propTrace p)) $
            xp5Tuple (xpTextAttr "name") 
            (xpWrap (\txt -> case txt of
                        "Falsifiable" -> False
                        "Valid" -> True
                        _ -> False,
                     \p -> if p then "Valid"
                           else "Falsifiable") $ xpTextAttr "status")
            (xpTextAttr "node")
            (xpAttrImplied "length" $ xpInt)
            (xpList xpickle)

instance XmlPickler ScadeTick where
  xpickle = xpElem "tick" $
            xpWrap (\(cyc,inps) -> ScadeTick cyc inps,
                    \tick -> (tickCycle tick,tickContent tick)) $
            xpPair (xpAttr "cycle" xpInt)
            (xpList xpickle)

instance XmlPickler ScadeTickAssignment where
  xpickle = xpAlt (\x -> case x of
                      InputAssignment _ _ -> 0
                      OutputAssignment _ _ -> 1)
            [xpElem "input" $
             xpWrap (\(name,val) -> InputAssignment name val,
                     \(InputAssignment name val) -> (name,val)) $
             xpPair (xpTextAttr "name") xpickle
            ,xpElem "output" $
             xpWrap (\(name,val) -> OutputAssignment name val,
                     \(OutputAssignment name val) -> (name,val)) $
             xpPair (xpTextAttr "name") xpickle
            ]

instance XmlPickler ScadeTickValue where
  xpickle = xpAlt (\x -> case x of
                      SingleData _ _ -> 0
                      CompositeData _ -> 1)
            [xpElem "value" $
             xpWrap (\(tp,val) -> SingleData tp val,
                     \(SingleData tp val) -> (tp,val)) $ 
             xpPair (xpTextAttr "type") xpText
            ,xpElem "composite" $
             xpWrap (CompositeData,\(CompositeData x) -> x) $ 
             xpList xpickle
            ]

-- | Runs the Scade design verifier and reads back its report.
verifyScadeNodes :: Options -> String -> String -> FilePath -> FilePath -> FilePath -> IO (Maybe FilePath)
verifyScadeNodes opts gtlName name opFile testNodeFile proofNodeFile =
  let reportFile = (outputPath opts) </> (gtlName ++ "-" ++ name ++ "_proof_report") <.> "xml"
      verifOpts = ["-node", name ++ "_proof"
                  ,opFile
                  ,testNodeFile
                  ,proofNodeFile
                  ,"-po","test_result"
                  ,"-xml",reportFile]++(case bmcBound opts of
                                           Nothing -> []
                                           Just l -> ["-strategy","debug"
                                                     ,"-stop-depth",show l])
      outputStream = if (verbosity opts) > 0 then Inherit else CreatePipe
      readAll h = do
        r <- hIsEOF h
        if r
          then return ()
          else hGetLine h >> readAll h
  in case scadeRoot opts of
    Nothing -> putStrLn "No SCADE_ROOT environment variable set" >> return Nothing
    Just root -> do
      let dv = root </> "SCADE Suite" </> "bin" </> "dv.exe"
      (_, hout, _, p) <- Proc.createProcess $
                         Proc.CreateProcess {
                           cmdspec = Proc.RawCommand dv verifOpts
                           , cwd = Nothing, env = Nothing
                           , std_in = CreatePipe, std_out = outputStream, std_err = outputStream
                           , close_fds = False
                           , create_group = False
                           }
      if (verbosity opts) > 0 then return () else (case hout of
                                                      Nothing -> return ()
                                                      Just hout' -> do 
                                                        str <- readAll hout'
                                                        return ())
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
readReport :: FilePath -> IO Prover
readReport reportFile = do
  res <- runX (xunpickleDocument xpickle [withValidate no,withRemoveWS yes,withPreserveComment no] reportFile)
  case res of
    [p] -> return p
    _ -> error "Couldn't parse report"

{-
--- | Generate the scenario file for the report.
generateScenario :: FilePath -> Report -> IO ()
generateScenario scenarioFile report = 
  writeFile scenarioFile $ (unlines . (map unlines) . errorTrace $ report) -}

scadeTranslateTypeC :: GTLType -> (String,String,Bool)
scadeTranslateTypeC (Fix GTLInt) = ("kcg_int","",False)
scadeTranslateTypeC (Fix GTLBool) = ("kcg_bool","",False)
scadeTranslateTypeC (Fix (GTLNamed n tp)) = let (_,_,ref) = scadeTranslateTypeC tp
                                            in (n,"",ref)
scadeTranslateTypeC (Fix (GTLArray i tp)) = let (p,q,ref) = scadeTranslateTypeC tp
                                            in (p,q++"["++show i++"]",True)
scadeTranslateTypeC rep = error $ "Couldn't translate "++show rep++" to C-type"

scadeTranslateValueC :: GTLConstant -> CExpr
scadeTranslateValueC d = case unfix d of
  GTLIntVal v -> CValue $ show v
  GTLBoolVal v -> CValue $ if v then "1" else "0"
  GTLEnumVal v -> CValue v
  GTLArrayVal vs -> CArray (fmap scadeTranslateValueC vs)
  _ -> error $ "Couldn't translate "++show d++" to C-value"

scadeTypeToGTL :: ScadeTypeMapping -> ScadeTypeMapping -> Sc.TypeExpr -> Maybe GTLType
scadeTypeToGTL _ _ Sc.TypeInt = Just gtlInt
scadeTypeToGTL _ _ Sc.TypeBool = Just gtlBool
scadeTypeToGTL _ _ Sc.TypeReal = Just gtlFloat
scadeTypeToGTL _ _ Sc.TypeChar = Just gtlByte
scadeTypeToGTL g l (Sc.TypePath (Path path)) = do
  tp <- scadeLookupType g l path
  rtp <- scadeTypeToGTL g Map.empty tp
  return $ Fix $ GTLNamed (last path) rtp
scadeTypeToGTL g l (Sc.TypeEnum enums) = Just (gtlEnum enums)
scadeTypeToGTL g l (Sc.TypePower tp expr) = do
  rtp <- scadeTypeToGTL g l tp
  case expr of
    ConstIntExpr 1 -> return rtp
    ConstIntExpr n -> return (gtlArray n rtp)
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

-- | Types are resolved in two stages: first find all type declaration and
--    then move types from "opened" packages into the global scope.
scadeTypes :: [Sc.Declaration] -> ScadeTypeMapping
scadeTypes decls = (\types -> resolvePackageOpen types types decls) $ (readScadeTypes decls)
  where
    readScadeTypes [] = Map.empty
    readScadeTypes ((TypeBlock tps):xs) = foldl (\mp (TypeDecl _ name cont) -> case cont of
                                                Nothing -> mp
                                                Just expr -> Map.insert name (ScadeType expr) mp
                                            ) (readScadeTypes xs) tps
    readScadeTypes ((PackageDecl _ name decls):xs) = Map.insert name (ScadePackage (readScadeTypes decls)) (readScadeTypes xs)
    readScadeTypes (_:xs) = scadeTypes xs

    resolvePackageOpen global local ((PackageDecl _ name decls) : xs) =
      Map.adjust (\(ScadePackage pTypes) -> ScadePackage $ resolvePackageOpen global pTypes decls) name local
    resolvePackageOpen global local ((OpenDecl (Path path)) : xs) = local `Map.union` (packageTypes global path)
    resolvePackageOpen global local _ = local

    packageTypes :: ScadeTypeMapping -> [String] -> ScadeTypeMapping
    packageTypes _ [] = Map.empty
    packageTypes types [p] = case Map.lookup p types of
      Just (ScadePackage pTypes) -> pTypes
      _ -> Map.empty
    packageTypes types (p:ps) = packageTypes types ps

scadeTypeMap :: MonadError String m => ScadeTypeMapping -> ScadeTypeMapping -> [(String,Sc.TypeExpr)] -> m (Map String GTLType)
scadeTypeMap global local tps = do
  res <- mapM (\(name,expr) -> case scadeTypeToGTL global local expr of
                  Nothing -> throwError $ "Couldn't convert SCADE type "++show expr++" to GTL"
                  Just tp -> return (name,tp)) tps
  return $ Map.fromList res

-- | Extract type information from a SCADE model.
--   Returns two list of variable-type pairs, one for the input variables, one for the outputs.
scadeInterface :: [String] -- ^ The name of the Scade model to analyze
                  -> [Sc.Declaration] -- ^ The parsed source code
                  -> ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)],UserOpKind)
scadeInterface (name@(n1:names)) ((Sc.PackageDecl _ pname decls):xs)
  | n1==pname = scadeInterface names decls
  | otherwise = scadeInterface name xs
scadeInterface [name] (op@(Sc.UserOpDecl {}):xs)
  | Sc.userOpName op == name = (varNames' (Sc.userOpParams op),varNames' (Sc.userOpReturns op),Sc.userOpKind op)
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
dfasToScade :: ScadeTypeMapping
                -> String -- ^ Name of the resulting SCADE node
                -> [(String, TypeExpr)] -- ^ Input variables
                -> [(String, TypeExpr)] -- ^ Output variables
                -> Map String GTLType -- ^ Local variables of the mode
                -> Map String (Maybe GTLConstant)
                -> [DFA [TypedExpr String] Integer] -- ^ The DFAs
                -> Sc.Declaration
dfasToScade types name ins outs locals defs dfas
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
                              , dataLocals = [VarDecl { varNames = [VarId ("test_result"++show n) False False]
                                                      , varType = TypeBool
                                                      , varDefault = Nothing
                                                      , varLast = Nothing }
                                             | (_,n) <- zip dfas [0..] ] ++
                                             declarationsToScade types (Map.toList locals) defs
                              , dataEquations = SimpleEquation [Named "test_result"] (foldl1 (BinaryExpr BinAnd) [ IdExpr (Path ["test_result"++show n]) | (_,n) <- zip dfas [0..] ]) :
                                                [StateEquation
                                                 (StateMachine Nothing (dfaToStates locals ("test_result"++show n) dfa))
                                                 [] True
                                                | (dfa,n) <- zip dfas [0..]
                                                ]
                              }
    }

-- | Translates a buchi automaton into a list of SCADE automaton states.
dfaToStates :: Map String GTLType -> String -> DFA [TypedExpr String] Integer -> [Sc.State]
dfaToStates locals resultvar dfa
  = failState resultvar :
    [ Sc.State { stateInitial = s == dfaInit dfa
               , stateFinal = False
               , stateName = "st" ++ (show s)
               , stateData = DataDef { dataSignals = []
                                     , dataLocals = []
                                     , dataEquations = [SimpleEquation [Named resultvar] (ConstBoolExpr True)]
                                     }
               , stateUnless = [ stateToTransition locals cond trg
                               | (cond, trg) <- trans ] ++
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
failState :: String -> Sc.State
failState resultvar = Sc.State
  { stateInitial = False
  , stateFinal = False
  , stateName = "fail"
  , stateData = DataDef { dataSignals = []
                        , dataLocals = []
                        , dataEquations = [SimpleEquation [Named resultvar] (ConstBoolExpr False)]
                        }
  , stateUnless = []
  , stateUntil = []
  , stateSynchro = Nothing
  }

-- | Given a state this function creates a transition into the state.
stateToTransition :: Map String GTLType ->  [TypedExpr String] -> Integer -> Sc.Transition
stateToTransition locals cond trg =
  let (e, a) = relsToExpr locals [cond]
  in Transition
      e
      (fmap Sc.ActionDef a)
      (TargetFork Restart ("st"++show trg))

-- | There is a special case for state output constraints using
-- equality if it involves a local variable on the lhs.
-- This corresponds to an assignment which has to be executed.
-- TODO: is this the correct behaviour and the only case.
exprToScade :: Map String GTLType -> TypedExpr String -> (Sc.Expr, Maybe Sc.DataDef)
exprToScade locals (Fix expr) = case getValue expr of
  Var name lvl u -> (foldl (\e _ -> UnaryExpr UnPre e) (case u of
                                                           --StateIn -> LastExpr name -- \x -> BinaryExpr BinAfter (ConstIntExpr 0) (UnaryExpr UnPre x)
                                                           _ -> IdExpr (Path [name])
                                                       ) [1..lvl], Nothing)
  Value val -> (valueToScade locals val, Nothing)
  BinIntExpr op l r ->
    let (lExpr, lAssign) = exprToScade locals l
        (rExpr, rAssign) = exprToScade locals r
    in (Sc.BinaryExpr (case op of
                         OpPlus -> BinPlus
                         OpMinus -> BinMinus
                         OpMult -> BinTimes
                         OpDiv -> BinDiv
                     ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  BinBoolExpr op l r ->
    let (lExpr, lAssign) = exprToScade locals l
        (rExpr, rAssign) = exprToScade locals r
    in (Sc.BinaryExpr (case op of
                        GTL.And -> Sc.BinAnd
                        GTL.Or -> Sc.BinOr
                      ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  BinRelExpr BinEq l r -> mkEqExprBinEquals locals l r
  BinRelExpr rel l r ->
    let (lExpr, lAssign) = exprToScade locals l
        (rExpr, rAssign) = exprToScade locals r
    in (BinaryExpr (case rel of
                      BinLT -> BinLesser
                      BinLTEq -> BinLessEq
                      BinGT -> BinGreater
                      BinGTEq -> BinGreaterEq
                      BinNEq -> BinDifferent
                   ) lExpr rExpr
        , mergeAssigns lAssign rAssign)
  UnBoolExpr GTL.Not p -> first (Sc.UnaryExpr Sc.UnNot) (exprToScade locals p)
  GTL.IndexExpr r i -> first (flip Sc.IndexExpr $ (Sc.ConstIntExpr i)) (exprToScade locals r)

-- | If on the lhs of an equality expression a state output variable is fund
-- this expression is transformed into an assignment on the transition.
mkEqExprBinEquals :: Map String GTLType -> TypedExpr String -> TypedExpr String -> (Sc.Expr, Maybe Sc.DataDef)
mkEqExprBinEquals locals l r =
  case getValue (unfix l) of
    (Var name lvl StateOut) ->
      if name `Map.member` locals then
        (Sc.ConstBoolExpr True, Just $ Sc.DataDef [] [] [SimpleEquation [Named name] (exprToScadeNoAssigns locals r)])
      else mkNonAssign
    _ -> mkNonAssign
  where
    mkNonAssign =
      let (lExpr, lAssign) = exprToScade locals l
          (rExpr, rAssign) = exprToScade locals r
      in (BinaryExpr BinEquals lExpr rExpr
        , mergeAssigns lAssign rAssign)
-- | Merge two data definitions for one transition.
mergeAssigns :: Maybe Sc.DataDef -> Maybe Sc.DataDef -> Maybe Sc.DataDef
mergeAssigns = maybeComb (\d1 d2 -> DataDef (dataSignals d1 ++ dataSignals d2) (dataLocals d1 ++ dataLocals d2) (dataEquations d1 ++ dataEquations d2))
  where
    maybeComb f (Just x) (Just y) = Just $ f x y
    maybeComb _ Nothing y = y
    maybeComb _ x Nothing = x

exprToScadeNoAssigns locals e =
  let (e', a) = exprToScade locals e
  in if isJust a then error "assignment not allowed here" else e'

valueToScade :: Map String GTLType -> GTLValue (Fix (Typed (Term String))) -> Sc.Expr
valueToScade locals (GTLIntVal v) = Sc.ConstIntExpr v
valueToScade locals (GTLBoolVal v) = Sc.ConstBoolExpr v
valueToScade locals (GTLByteVal v) = Sc.ConstIntExpr (fromIntegral v)
valueToScade locals (GTLEnumVal v) = Sc.IdExpr $ Path [v]
valueToScade locals (GTLArrayVal xs) = Sc.ArrayExpr (fmap (exprToScadeNoAssigns locals) xs) -- no assignments should be generated inside index expression
valueToScade locals (GTLTupleVal xs) = Sc.ArrayExpr (fmap (exprToScadeNoAssigns locals) xs) -- or tuple expressions

-- Generate plain values, no expressions allowed, only constants
constantToScade :: GTLConstant -> Sc.Expr
constantToScade (Fix (GTLIntVal v)) = Sc.ConstIntExpr v
constantToScade (Fix (GTLBoolVal v)) = Sc.ConstBoolExpr v
constantToScade (Fix (GTLByteVal v)) = Sc.ConstIntExpr (fromIntegral v)
constantToScade (Fix (GTLEnumVal v)) = Sc.IdExpr $ Path [v]
constantToScade (Fix (GTLArrayVal xs)) = Sc.ArrayExpr (fmap constantToScade xs)
constantToScade (Fix (GTLTupleVal xs)) = Sc.ArrayExpr (fmap constantToScade xs)

declarationsToScade :: ScadeTypeMapping -> [(String, GTLType)] -> Map String (Maybe GTLConstant) -> [Sc.VarDecl]
declarationsToScade types decls defs = concat $ map declarationsToScade' decls
  where
    declarationsToScade' (n, Fix (GTLTuple ts)) = makeTupleDecls n [] ts
    declarationsToScade' (n, t) = [Sc.VarDecl [Sc.VarId n False False] (gtlTypeToScade types t) Nothing (Just $ case Map.lookup n defs of
                                                                                                            Nothing -> constantToScade $ defaultValue t
                                                                                                            Just (Just c) -> constantToScade c
                                                                                                        )]

    -- Tuples are declared as follows:
    -- for every entry x : (a0, a1, ..., an) there is a variable x_i : ai declared.
    -- If tuples are nested, this scheme is extended for every layer:
    -- x : ((a0, a1), a2) becomes x_0_0 : a0; x_0_1 : a1; x_1 : a2;
    makeTupleDecls n indcs ts  = concat $ snd $ mapAccumL (makeTupleDecl n indcs) 0 ts
      where
        makeTupleDecl :: String -> [Int] -> Int -> GTLType -> (Int, [Sc.VarDecl])
        makeTupleDecl n indcs indx (Fix (GTLTuple ts)) = (indx + 1, makeTupleDecls n (indx : indcs) ts)
        makeTupleDecl n indcs indx t = (indx + 1, [Sc.VarDecl [Sc.VarId (n ++ (expandName indcs) ++ "_" ++ show indx) False False] (gtlTypeToScade types t) Nothing Nothing])
        expandName = foldl (\n i -> n ++ "_" ++ show i ) ""

declareConstVars :: ScadeTypeMapping -> Map String (GTLType, GTLConstant) -> [Sc.VarDecl]
declareConstVars types = foldrWithKey (\n (t,v) l -> (VarDecl [VarId n False False] (gtlTypeToScade types t) Nothing Nothing) : l) []

constAssign :: Map String (GTLType, GTLConstant) -> [Sc.Equation]
constAssign = foldrWithKey (\n (t,v) l -> (SimpleEquation [Named n ] (constantToScade v) ) : l) []

enumAlias :: ScadeTypeMapping -> [String] -> Maybe String
enumAlias types enum = Map.foldrWithKey (\n' t n -> n `Syb.orElse` (matchesEnum enum n' t)) Nothing types
  where
    matchesEnum enum name (ScadeType (TypeEnum enum')) = if enum == enum' then Just name else Nothing
    matchesEnum _ _ _ = Nothing

gtlTypeToScade :: ScadeTypeMapping -> GTLType -> Sc.TypeExpr
gtlTypeToScade _ (Fix GTLInt) = Sc.TypeInt
-- gtlTypeToScade GTLByte = ?
gtlTypeToScade _ (Fix GTLBool) = Sc.TypeBool
gtlTypeToScade _ (Fix GTLFloat) = Sc.TypeReal
gtlTypeToScade types (Fix (GTLEnum decls)) =
  let malias = enumAlias types decls
  in case malias of
    Just alias -> Sc.TypePath (Path [alias])
    Nothing -> Sc.TypeEnum decls
gtlTypeToScade types (Fix (GTLArray size t)) = Sc.TypePower (gtlTypeToScade types t) (Sc.ConstIntExpr size)
--gtlTypeToScade (GTLTuple ts) = map gtlTypeToScade ts
gtlTypeToScade _ (Fix (GTLNamed n _)) = Sc.TypePath (Path [n])
gtlTypeToScade _ t = error $ "Cannot generate type " ++ show t

apPairs f g = \(x1,y1) (x2,y2) -> (f x1 x2, g y1 y2)

relsToExpr :: Map String GTLType -> [[TypedExpr String]] -> (Sc.Expr, Maybe Sc.DataDef)
relsToExpr _ [] = (Sc.ConstBoolExpr False, Nothing)
relsToExpr locals xs = foldl1 (apPairs (Sc.BinaryExpr Sc.BinOr) mergeAssigns)
                       (fmap (\x -> case x of
                                 [] -> (Sc.ConstBoolExpr True, Nothing)
                                 _ -> foldl1 (apPairs (Sc.BinaryExpr Sc.BinAnd) mergeAssigns) (fmap (exprToScade locals) x)
                             ) xs)

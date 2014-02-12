{-# LANGUAGE RankNTypes,DeriveDataTypeable,ExistentialQuantification,TypeFamilies,CPP,FlexibleContexts,FlexibleInstances #-}
module Language.GTL.Target.SMT where

import Data.Typeable
import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.Types
import Language.GTL.Buchi
import Language.GTL.Translation
import Language.GTL.ErrorRefiner
import Language.SMTLib2 as SMT
import Language.SMTLib2.Solver
import Language.SMTLib2.Pipe
import Language.SMTLib2.Internals.Operators
import Language.SMTLib2.Internals as SMT
import Data.Map as Map hiding ((!))
import Data.Set as Set
import qualified Data.Text as T
import Data.AttoLisp as L
import Control.Monad.Trans
import Data.Traversable
import Data.Foldable
import Prelude hiding (mapM,sequence,foldl1,concat,mapM_,minimum)
import Data.List (genericIndex,intersperse)
import Data.Word
import Control.Concurrent
import Misc.ProgramOptions
import qualified Data.List as List
import Data.Time
import System.IO (hFlush,stdout)
import Data.Unit
import Data.Maybe (catMaybes)
import System.FilePath

#ifdef SMTExts
type GTLSMTPc = Integer
type GTLSMTInt = Integer
#else
type GTLSMTPc = BV64
type GTLSMTInt = BV64
#endif

(!) :: (Ord k,Show k) => Map k v -> k -> v
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Can't find key "++show k++" in "++show (Map.keys mp)
             Just v -> v

#ifdef SMT_EXTS
-- | Used to represent Enum values.
data EnumVal = EnumVal String deriving (Typeable,Eq)

instance ToGTL EnumVal where
  toGTL (EnumVal name) = GTLEnumVal name
  --gtlTypeOf (EnumVal enums _ _) = Fix $ GTLEnum enums

varEnum :: [String] -> SMT (SMTExpr EnumVal)
varEnum = varAnn

constantEnum :: String -> [String] -> SMTExpr EnumVal
constantEnum = constantAnn

annEnum :: [String] -> SMTAnnotation EnumVal
annEnum = id

enumGet :: [String] -> EnumVal -> String
enumGet _ (EnumVal v) = v

instance SMTType EnumVal where
  type SMTAnnotation EnumVal = [String]
  getSort _ vals = Fix $ NamedSort ("Enum"++concat [ "_"++val | val <- vals ]) []
  asDataType _ vals = Just ("Enum"++concat [ "_"++val | val <- vals ],
                            TypeCollection { argCount = 0
                                           , dataTypes = [enumDt] })
    where
      enumDt = DataType { dataTypeName = "Enum"++concat [ "_"++val | val <- vals ]
                        , dataTypeConstructors = [ Constr { conName = val
                                                          , conFields = []
                                                          , construct = \[] [] f -> f [] (EnumVal val) vals
                                                          , conTest = \[] val -> case cast val of
                                                            Just (EnumVal val') -> val==val'
                                                          }
                                                 | val <- vals ]
                        , dataTypeGetUndefined = \[] f -> f (undefined::EnumVal) vals }
  asValueType x ann f = Just $ f x ann
  annotationFromSort _ (Fix (NamedSort enumName []))
    = case splitEnumName enumName of
      "Enum":vals -> vals
    where
      splitEnumName name = let (l,s') = break (=='_') name
                           in l:case s' of
                                  [] -> []
                                  _:s'' -> splitEnumName s''
instance SMTValue EnumVal where
  mangle (EnumVal v) _ = L.Symbol $ T.pack v
  unmangle (L.Symbol v) vals = return $ Just $ EnumVal (T.unpack v)
  unmangle _ _ = return Nothing
#else
type EnumVal = BitVector BVUntyped

varEnum :: [String] -> SMT (SMTExpr EnumVal)
varEnum vals = varAnn (annEnum vals)

constantEnum :: String -> [String] -> SMTExpr EnumVal
constantEnum val vals = let Just idx = List.elemIndex val vals
                        in constantAnn (BitVector (fromIntegral idx)) (annEnum vals)

annEnum :: [String] -> SMTAnnotation EnumVal
annEnum vals = let bits = ceiling $ logBase 2 $ fromIntegral (List.length vals)
               in bits

enumGet :: [String] -> EnumVal -> String
enumGet vs (BitVector v) = List.genericIndex vs v
#endif

data GTLSMTExpr = GSMTInt { asSMTInt :: SMTExpr GTLSMTInt }
                | GSMTByte { asSMTByte :: SMTExpr BV8 }
                | GSMTBool { asSMTBool :: SMTExpr Bool }
                | GSMTEnum { asSMTEnum :: SMTExpr EnumVal
                           , enumValues :: [String] }
                | GSMTArray { asSMTArray :: [GTLSMTExpr] }
                | GSMTTuple { asSMTTuple :: [GTLSMTExpr] }
                deriving (Eq,Typeable,Show)

instance Args GTLSMTExpr where
  type ArgAnnotation GTLSMTExpr = GTLType
  foldExprs f s e (Fix GTLInt) = do
    (s',e') <- f s (asSMTInt e) ()
    return (s',GSMTInt e')
  foldExprs f s e (Fix GTLByte) = do
    (s',e') <- f s (asSMTByte e) ()
    return (s',GSMTByte e')
  foldExprs f s e (Fix GTLBool) = do
    (s',e') <- f s (asSMTBool e) ()
    return (s',GSMTBool e')
  foldExprs f s e (Fix (GTLEnum vs)) = do
    (s',e') <- f s (asSMTEnum e) (annEnum vs)
    return (s',GSMTEnum e' vs)
  foldExprs f s e (Fix (GTLArray len tp)) = do
    (s',arr) <- lenMapAccumL len (\cs el -> foldExprs f cs el tp) s (asSMTArray e)
    return (s',GSMTArray arr)
  foldExprs f s e (Fix (GTLTuple tps)) = do
    (s',els) <- mapAccumLM (\st (tp,el) -> foldExprs f st el tp) s (unsafeZip tps (asSMTTuple e))
    return (s',GSMTTuple els)
  foldExprs f s e (Fix (GTLNamed name tp)) = foldExprs f s e tp
  foldsExprs f s args (Fix GTLInt) = do
    (ns,nargs,zarg) <- f s (fmap (\(x,b) -> (asSMTInt x,b)) args) ()
    return (ns,fmap GSMTInt nargs,GSMTInt zarg)
  foldsExprs f s args (Fix GTLByte) = do
    (ns,nargs,zarg) <- f s (fmap (\(x,b) -> (asSMTByte x,b)) args) ()
    return (ns,fmap GSMTByte nargs,GSMTByte zarg)
  foldsExprs f s args (Fix GTLBool) = do
    (ns,nargs,zarg) <- f s (fmap (\(x,b) -> (asSMTBool x,b)) args) ()
    return (ns,fmap GSMTBool nargs,GSMTBool zarg)
  foldsExprs f s args (Fix (GTLEnum vals)) = do
    (ns,nargs,zarg) <- f s (fmap (\(x,b) -> (asSMTEnum x,b)) args) (annEnum vals)
    return (ns,fmap (\x -> GSMTEnum x vals) nargs,GSMTEnum zarg vals)
  foldsExprs f s args (Fix (GTLArray len tp)) = do
    (ns,nargs,zarg) <- foldsExprs f s (fmap (\(x,b) -> (asSMTArray x,b)) args)
                       (List.genericReplicate len tp)
    return (ns,fmap GSMTArray nargs,GSMTArray zarg)
  foldsExprs f s args (Fix (GTLTuple tps)) = do
    (ns,nargs,zarg) <- foldsExprs f s (fmap (\(x,b) -> (asSMTTuple x,b)) args) tps
    return (ns,fmap GSMTTuple nargs,GSMTTuple zarg)
  extractArgAnnotation (GSMTInt _) = Fix GTLInt
  extractArgAnnotation (GSMTByte _) = Fix GTLByte
  extractArgAnnotation (GSMTBool _) = Fix GTLBool
  extractArgAnnotation (GSMTEnum _ vs) = Fix (GTLEnum vs)
  extractArgAnnotation (GSMTArray arr) = Fix (GTLArray (List.genericLength arr) (extractArgAnnotation $ head arr))
  extractArgAnnotation (GSMTTuple els) = Fix (GTLTuple (fmap extractArgAnnotation els))

mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM _ st [] = return (st,[])
mapAccumLM f st (x:xs) = do
  (st1,y) <- f st x
  (st2,ys) <- mapAccumLM f st1 xs
  return (st2,y:ys)

lenMapAccumL :: Monad m => Integer -> (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
lenMapAccumL 0 f s _ = return (s,[])
lenMapAccumL n f s ~(x:xs) = do
  (s',y) <- f s x
  (s'',ys) <- lenMapAccumL (n-1) f s' xs
  return (s'',y:ys)

unsafeZip :: [a] -> [b] -> [(a,b)]
unsafeZip [] _ = []
unsafeZip (x:xs) ~(y:ys) = (x,y):unsafeZip xs ys

-- | Saves the variables of one instance (including the state variable of the state machine)
data InstanceState = InstanceState
                     { instanceInputVars :: Map String GTLSMTExpr
                     , instanceOutputVars :: Map String GTLSMTExpr
                     , instanceLocalVars :: Map String GTLSMTExpr
                     , instanceAutomata :: [SMTExpr GTLSMTPc]
                     } deriving (Eq,Typeable,Show)

data InstanceInfo = InstanceInfo
                    { iiModel :: GTLModel String
                    , iiAutomataMapping :: [(GTLContract String,Maybe (String,Map GTLSMTPc String,Map String GTLSMTPc))]
                    } deriving (Eq,Typeable,Show)

getInstanceInfo :: GTLModel String -> [GTLContract String] -> InstanceInfo
getInstanceInfo mdl extra = InstanceInfo { iiModel = mdl
                                         , iiAutomataMapping = [ (f,case GTL.getValue $ unfix $ gtlContractFormula f of
                                                                     Automaton name ba -> let rname = case name of
                                                                                                Nothing -> "automaton"++show n
                                                                                                Just name' -> name'
                                                                                              stlst = [ (i,stname)
                                                                                                      | (i,(stname,_)) <- zip [0..] (Map.toAscList $ baTransitions ba) ]
                                                                                              stmp = Map.fromAscList stlst
                                                                                              r_stmp = Map.fromList (fmap (\(x,y) -> (y,x)) stlst)
                                                                                          in Just (rname,stmp,r_stmp)
                                                                     _ -> Nothing)
                                                               | (f,n) <- zip (gtlModelContract mdl ++ extra) [0..] ]
                                         }

annInstanceInfo :: InstanceInfo -> ArgAnnotation InstanceState
annInstanceInfo is = (gtlModelInput $ iiModel is,
                      gtlModelOutput $ iiModel is,
                      gtlModelLocals $ iiModel is,
                      List.genericLength (iiAutomataMapping is))

getVar :: String -> VarUsage -> InstanceState -> GTLSMTExpr
getVar name u is = let mp = case u of
                              Input -> instanceInputVars is
                              Output -> instanceOutputVars is
                              _ -> instanceLocalVars is
                   in case Map.lookup name mp of
                        Nothing -> error $ "Variable "++show name++" ("++show u++") not found in "++show (Map.keys mp)
                        Just v -> v

instance Args InstanceState where
  type ArgAnnotation InstanceState = (Map String GTLType,Map String GTLType,Map String GTLType,Integer)
  {-foldExprs f s is (inp_tps,outp_tps,loc_tps,ncontr) = do
    (s1,inp) <- foldExprs f s (instanceInputVars is) inp_tps
    (s2,outp) <- foldExprs f s1 (instanceOutputVars is) outp_tps
    (s3,loc) <- foldExprs f s2 (instanceLocalVars is) loc_tps
    (s4,pc') <- mapAccumLM (\cs i -> foldExprs f cs (List.genericIndex (instanceAutomata is) i) ()
                           ) s3 [0..(ncontr-1)]
    return (s4,InstanceState { instanceInputVars = inp
                             , instanceOutputVars = outp
                             , instanceLocalVars = loc 
                             , instanceAutomata = pc' })-}
  foldsExprs f s is (inp_tps,outp_tps,loc_tps,ncontr) = do
    (s1,inp,zinp) <- foldsExprs f s
                     (fmap (\(x,b) -> (instanceInputVars x,b)) is) inp_tps
    (s2,outp,zoutp) <- foldsExprs f s1
                       (fmap (\(x,b) -> (instanceOutputVars x,b)) is) outp_tps
    (s3,loc,zloc) <- foldsExprs f s2
                     (fmap (\(x,b) -> (instanceLocalVars x,b)) is) loc_tps
    (s4,pc,zpc) <- foldsExprs f s3
                   (fmap (\(x,b) -> (instanceAutomata x,b)) is)
                   (List.genericReplicate ncontr ())
    return (s4,[ InstanceState inp' outp' loc' pc'
               | (inp',outp',loc',pc') <- List.zip4 inp outp loc pc ],
            InstanceState zinp zoutp zloc zpc)
  extractArgAnnotation is = (fmap extractArgAnnotation (instanceInputVars is),
                             fmap extractArgAnnotation (instanceOutputVars is),
                             fmap extractArgAnnotation (instanceLocalVars is),
                             List.genericLength (instanceAutomata is))

-- | Saves the variables of all components in the GALS system
data GlobalState = GlobalState
                   { instanceStates :: Map String InstanceState
                   } deriving (Eq,Typeable,Show)

data GlobalInfo = GlobalInfo
                  { instanceInfos :: Map String InstanceInfo
                  , globalSpec :: GTLSpec String
                  } deriving (Eq,Typeable,Show)

getGlobalInfo :: GTLSpec String -> GlobalInfo
getGlobalInfo spec = GlobalInfo 
                     (fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                     in getInstanceInfo mdl (gtlInstanceContract inst)
                           ) (gtlSpecInstances spec))
                     spec

annGlobalInfo :: GlobalInfo -> ArgAnnotation GlobalState
annGlobalInfo gi = fmap annInstanceInfo (instanceInfos gi)

instance Args GlobalState where
  type ArgAnnotation GlobalState = Map String (Map String GTLType,Map String GTLType,Map String GTLType,Integer)
  foldExprs f s gs info = do
    (s',gs') <- foldExprs f s (instanceStates gs) info
    return (s',GlobalState { instanceStates = gs' })
  extractArgAnnotation gs = fmap extractArgAnnotation (instanceStates gs)

indexGTLSMT :: GTLSMTExpr -> [Integer] -> GTLSMTExpr
indexGTLSMT x [] = x
indexGTLSMT (GSMTArray arr) (i:is) = indexGTLSMT (arr `genericIndex` i) is
indexGTLSMT (GSMTTuple arr) (i:is) = indexGTLSMT (arr `genericIndex` i) is

eqGTLSMT :: GTLSMTExpr -> GTLSMTExpr -> SMTExpr Bool
eqGTLSMT (GSMTInt l) (GSMTInt r) = l .==. r
eqGTLSMT (GSMTByte l) (GSMTByte r) = l .==. r
eqGTLSMT (GSMTBool l) (GSMTBool r) = l .==. r
eqGTLSMT (GSMTEnum l _) (GSMTEnum r _) = l .==. r
eqGTLSMT (GSMTArray l) (GSMTArray r) = app and' $ List.zipWith eqGTLSMT l r
eqGTLSMT (GSMTTuple l) (GSMTTuple r) = app and' $ List.zipWith eqGTLSMT l r

eqInst :: InstanceState -> InstanceState -> SMTExpr Bool
eqInst l r = app and' $
             (Map.elems $ Map.intersectionWith eqGTLSMT (instanceInputVars l) (instanceInputVars r)) ++
             (Map.elems $ Map.intersectionWith eqGTLSMT (instanceOutputVars l) (instanceOutputVars r)) ++
             (Map.elems $ Map.intersectionWith eqGTLSMT (instanceLocalVars l) (instanceLocalVars r)) ++
             (zipWith (.==.) (instanceAutomata l) (instanceAutomata r))

eqSt :: GlobalState -> GlobalState -> SMTExpr Bool
eqSt l r = app and' $
           Map.elems $
           Map.intersectionWith eqInst (instanceStates l) (instanceStates r)

connectionFun :: GTLSpec String -> (GlobalState,GlobalState) -> SMTExpr Bool
connectionFun spec (stf,stt)
  = app and' [ eqGTLSMT (indexGTLSMT ((instanceOutputVars $ (instanceStates stf)!f)!fv) fi)
               (indexGTLSMT ((instanceInputVars $ (instanceStates stt)!t)!tv) ti)
             | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- gtlSpecConnections spec
             ]

defaultsFun :: GTLSpec String -> GlobalState -> SMTExpr Bool
defaultsFun spec st
  = app and' [ eqGTLSMT ((instanceInputVars $ (instanceStates st)!iname)!vname) (translateConstant tp c)
             | (iname,inst) <- Map.toList (gtlSpecInstances spec)
             , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
             , (vname,(tp,c)) <- Map.toList $ gtlModelConstantInputs mdl
             ]
  where
    translateConstant tp c = translateExpr (\_ _ _ -> error "Language.GTL.Target.SMT.defaultsFun: This should not happen.")
                             (typedConstantToExpr tp c)

translateBVRel :: IsBitVector a => Relation -> SMTExpr (BitVector a) -> SMTExpr (BitVector a) -> SMTExpr Bool
translateBVRel BinLT = bvslt
translateBVRel BinLTEq = bvsle
translateBVRel BinGT = bvsgt
translateBVRel BinGTEq = bvsge
translateBVRel BinEq = (.==.)
translateBVRel BinNEq = \l r -> not' (l .==. r)

translateIntRel :: Relation -> SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool
translateIntRel BinLT = (.<.)
translateIntRel BinLTEq = (.<=.)
translateIntRel BinGT = (.>.)
translateIntRel BinGTEq = (.>=.)
translateIntRel BinEq = (.==.)
translateIntRel BinNEq = \l r -> not' (l .==. r)

-- | Translate a GTL expression into a SMT expression
translateExpr :: (v -> VarUsage -> Integer -> GTLSMTExpr) -> TypedExpr v -> GTLSMTExpr
translateExpr f (Fix expr)
  = case GTL.getValue expr of
    GTL.Var n i u -> f n u i
    GTL.Value val -> case val of
      GTLIntVal i ->  GSMTInt $ SMT.constant (fromIntegral i)
      GTLByteVal w -> GSMTByte $ SMT.constant (fromIntegral w)
      GTLBoolVal b -> GSMTBool $ SMT.constant b
      GTLEnumVal v -> let Fix (GTLEnum vals) = GTL.getType expr
                      in GSMTEnum (constantEnum v vals) vals
      GTLArrayVal vs -> GSMTArray $ fmap (translateExpr f) vs
      GTLTupleVal vs -> GSMTTuple $ fmap (translateExpr f) vs
    GTL.BinRelExpr BinEq l r -> GSMTBool $ eqGTLSMT (translateExpr f l) (translateExpr f r)
    GTL.BinRelExpr BinNEq l r -> GSMTBool $ not' $ eqGTLSMT (translateExpr f l) (translateExpr f r)
    GTL.BinRelExpr rel l r -> let ll = translateExpr f l
                                  rr = translateExpr f r
#ifdef SMTExts
                                  mkRel rel (GSMTInt l) (GSMTInt r) = translateIntRel rel l r
#else
                                  mkRel rel (GSMTInt l) (GSMTInt r) = translateBVRel rel l r
#endif
                                  mkRel rel (GSMTByte l) (GSMTByte r) = translateBVRel rel l r
                                  mkRel BinEq l r = eqGTLSMT l r
                                  mkRel BinNEq l r = not' $ eqGTLSMT l r
                              in GSMTBool $ mkRel rel ll rr
    GTL.BinIntExpr op l r -> let ll = translateExpr f l
                                 rr = translateExpr f r
                                 mkIntOp OpPlus (GSMTInt l) (GSMTInt r) = GSMTInt (l + r)
                                 mkIntOp OpPlus (GSMTByte l) (GSMTByte r) = GSMTByte (l + r)
                                 mkIntOp OpMinus (GSMTInt l) (GSMTInt r) = GSMTInt (l - r)
                                 mkIntOp OpMinus (GSMTByte l) (GSMTByte r) = GSMTByte (l - r)
                                 mkIntOp OpMult (GSMTInt l) (GSMTInt r) = GSMTInt (l * r)
                                 mkIntOp OpMult (GSMTByte l) (GSMTByte r) = GSMTByte (l * r)
                             in mkIntOp op ll rr
    GTL.IndexExpr expr' idx -> indexGTLSMT (translateExpr f expr') [idx]
    GTL.BinBoolExpr op l r -> let GSMTBool ll = translateExpr f l
                                  GSMTBool rr = translateExpr f r
                              in GSMTBool $ case op of
                                              GTL.And -> ll .&&. rr
                                              GTL.Or -> ll .&&. rr
                                              GTL.Implies -> ll .=>. rr
    GTL.UnBoolExpr GTL.Not arg -> let GSMTBool arg' = translateExpr f arg
                                  in GSMTBool $ not' arg'
    _ -> error $ "Implement translateExpr for " ++ showTermWith (\_ _ -> showString "_") (\_ _ -> showString "_") 0 (GTL.getValue expr) ""

-- | Perform a calculation step in a single component
instanceFuns :: Set [String] -> InstanceInfo -> (InstanceState -> SMTExpr Bool,InstanceState -> InstanceState -> SMTExpr Bool)
instanceFuns enums info
  = (init,step)
    where
      bas = fmap (\(f,ann) -> case GTL.getValue $ unfix $ gtlContractFormula f of
                     Automaton _ ba -> case ann of
                       Nothing -> Left (ba,snd $ mapAccumL (\n _ -> (n+1,n)) 0 (baTransitions ba))
                       Just (_,_,rmp) -> Left (ba,rmp)
                     _ -> Right $ gtl2ba (Just (gtlModelCycleTime $ iiModel info)) (gtlContractFormula f)
                 ) (iiAutomataMapping info)
      init inst = app and' $
                  [ either (\(aut,st_mp) -> let inits' = fmap (st_mp!) (Set.toList $ baInits aut)
                                            in app or' [ c .==. SMT.constant p
                                                       | p <- inits' ]
                           )
                    (\rba -> app or' [ c .==. SMT.constant (fromIntegral p)
                                     | p <- Set.toList $ baInits rba
                                     ]
                    ) ba
                  | (ba,c) <- zip bas (instanceAutomata inst) ] ++
                  [ eqGTLSMT
                    (case Map.lookup var (instanceInputVars inst) of
                        Just var' -> var'
                        Nothing -> case Map.lookup var (instanceOutputVars inst) of
                          Just var' -> var'
                          Nothing -> (instanceLocalVars inst)!var)
                    (translateExpr (\v u _ -> getVar v u inst) (constantToExpr enums def))
                  | (var,Just def) <- Map.toList $ gtlModelDefaults $ iiModel info ]
      step stf stt = app and'
                     [ either (\(aut,st_mp)
                               -> app and' [ (c1 .==. SMT.constant (st_mp!st)) .=>.
                                             app or' [ app and' ((c2 .==. SMT.constant (st_mp!trg)):
                                                                 [let GSMTBool v = translateExpr (\v u i -> case u of
                                                                                                     Input -> (instanceInputVars stf)!v
                                                                                                     StateIn -> (instanceLocalVars stf)!v
                                                                                                     Output -> (instanceOutputVars stt)!v
                                                                                                     StateOut -> (instanceLocalVars stt)!v) c
                                                                  in v
                                                                 | c <- cond ])
                                                     | (cond,trg) <- trans
                                                     ]
                                           | (st,trans) <- Map.toList (baTransitions aut)
                                           ])
                       (\rba -> app and' [ (c1 .==. SMT.constant (fromIntegral st)) .=>. 
                                           app or' [ app and' ((c2 .==. SMT.constant (fromIntegral trg)):
                                                               [let GSMTBool v = translateExpr (\v u i -> case u of
                                                                                                   Input -> (instanceInputVars stf)!v
                                                                                                   StateIn -> (instanceLocalVars stf)!v
                                                                                                   Output -> (instanceOutputVars stt)!v
                                                                                                   StateOut -> (instanceLocalVars stt)!v) c
                                                                in v
                                                               | c <- cond ])
                                                   | (cond,trg) <- trans ]
                                         | (st,trans) <- Map.toList (baTransitions rba)
                                         ]
                       ) ba
                     | (ba,c1,c2) <- zip3 bas (instanceAutomata stf) (instanceAutomata stt)
                     ]

-- | Asserts that two instance states are equal in their output and state variables.
eqInstOutp :: InstanceState -> InstanceState -> SMTExpr Bool
eqInstOutp st1 st2 
  = app and' ((app and' $ zipWith (.==.) (instanceAutomata st1) (instanceAutomata st2)):
              ((Map.elems $ Map.intersectionWith eqGTLSMT (instanceOutputVars st1) (instanceOutputVars st2))++
               (Map.elems $ Map.intersectionWith eqGTLSMT (instanceLocalVars st1) (instanceLocalVars st2))))

-- | A scheduling dictates which instance may perform a calculation step at which point in time.
class (Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ Map String Integer) => Scheduling s where
  type SchedulingData s
  firstSchedule :: s -> SchedulingData s -> SMTExpr Bool
  canSchedule :: s -> String -> SchedulingData s -> SMTExpr Bool
  schedule :: s -> String -> SchedulingData s -> SchedulingData s -> SMTExpr Bool
  eqScheduling :: s -> SchedulingData s -> SchedulingData s -> SMTExpr Bool
  schedulingFairnessCount :: s -> Map String Integer -> Integer
  schedulingFairness :: s -> SchedulingData s -> [SMTExpr Bool]
  showSchedulingInformation :: s -> SchedulingData s -> SMT String

data SimpleScheduling = SimpleScheduling

data SimpleSchedulingData = SimpleSchedulingData deriving (Typeable,Eq,Show)

instance Args SimpleSchedulingData where
  type ArgAnnotation SimpleSchedulingData = Map String Integer
  foldExprs _ s _ _ = return (s,SimpleSchedulingData)

instance Scheduling SimpleScheduling where
  type SchedulingData SimpleScheduling = SimpleSchedulingData
  firstSchedule _ _ = SMT.constant True
  canSchedule _ _ _ = SMT.constant True
  schedule _ _ _ _ = SMT.constant True
  eqScheduling _ _ _ = SMT.constant True
  schedulingFairnessCount _ _ = 0
  schedulingFairness _ _ = []
  showSchedulingInformation _ _ = return "none"

data SyncScheduling = SyncScheduling

newtype SyncSchedulingData = SyncSchedulingData (Map String (SMTExpr Bool)) deriving (Typeable,Eq,Show)

instance Args SyncSchedulingData where
  type ArgAnnotation SyncSchedulingData = Map String Integer
  foldExprs f s ~(SyncSchedulingData mp) procs = do
    (s',mp') <- mapAccumLM (\cs (name,_) -> do
                               (cs',nv) <- f cs (mp!name) ()
                               return (cs',(name,nv))) s (Map.toAscList procs)
    return (s',SyncSchedulingData (Map.fromAscList mp'))

instance Scheduling SyncScheduling where
  type SchedulingData SyncScheduling = SyncSchedulingData
  firstSchedule _ (SyncSchedulingData mp) = app and' [ not' x | x <- Map.elems mp ]
  canSchedule _ name (SyncSchedulingData mp) = app or' [ not' (mp!name)
                                                       , app and' $ Map.elems mp ]
  schedule _ name (SyncSchedulingData m1) (SyncSchedulingData m2) 
    = app and' [m2!name
               ,ite (m1!name) 
                (app and' [ not' x | (name',x) <- Map.toList m2, name/=name' ])
                (app and' [ x .==. (m1!name') | (name',x) <- Map.toList m2, name/=name' ])
               ]
  eqScheduling _ (SyncSchedulingData p1) (SyncSchedulingData p2)
    = app and' $ Map.elems $ Map.intersectionWith (.==.) p1 p2
  schedulingFairnessCount _ _ = 0
  schedulingFairness _ _ = []
  showSchedulingInformation _ (SyncSchedulingData mp) = do
    mp' <- mapM (\(name,x) -> do
                    vx <- SMT.getValue x
                    return $ name ++ ":" ++ (if vx then "1" else "0")
                ) (Map.toList mp)
    return $ show mp'

data FairScheduling = FairScheduling

data FairSchedulingData = FairSchedulingData (SMTExpr (BitVector BVUntyped)) Integer
                          (Map String (BitVector BVUntyped)) deriving (Typeable,Eq,Show)

instance Args FairSchedulingData where
  type ArgAnnotation FairSchedulingData = Map String Integer
  foldExprs f s ~(FairSchedulingData bv w v) procs = do
    let w' = ceiling $ logBase 2 $ fromIntegral $ Map.size procs
        (_,v') = mapAccumL (\n _ -> (n+1,BitVector n)) 0 procs
    (s',bv') <- f s bv w'
    return (s',FairSchedulingData bv' w' v')

instance Scheduling FairScheduling where
  type SchedulingData FairScheduling = FairSchedulingData
  firstSchedule _ _ = SMT.constant True
  canSchedule _ _ _ = SMT.constant True
  schedule _ name (FairSchedulingData i w mp) _ = i .==. SMT.constantAnn (mp!name) w
  eqScheduling _ (FairSchedulingData i _ _) (FairSchedulingData j _ _) = i .==. j
  schedulingFairnessCount _ procs = fromIntegral (Map.size procs)
  schedulingFairness _ (FairSchedulingData i w mp) = [ i .==. SMT.constantAnn v w | (name,v) <- Map.toList mp ]
  showSchedulingInformation _ (FairSchedulingData i w mp) = do
    v <- SMT.getValue i
    case [ name | (name,j) <- Map.toList mp, j==v ] of
      [n] -> return n

data TimedScheduling = TimedScheduling

data TimedSchedulingData = TimedSchedulingData (Map String (SMTExpr GTLSMTInt)) (SMTExpr GTLSMTInt) (Map String Integer) deriving (Typeable,Eq,Show)

instance Args TimedSchedulingData where
  type ArgAnnotation TimedSchedulingData = Map String Integer
  foldExprs f s ~(TimedSchedulingData mp v _) procs = do
    (s1,mp') <- mapAccumLM (\s (name,_) -> do
                               (s',x) <- f s (mp!name) ()
                               return (s',(name,x))
                           ) s (Map.toAscList procs)
    (s2,v') <- f s1 v ()
    return (s2,TimedSchedulingData (Map.fromAscList mp') v' procs)

minimumSMTBy :: SMTType t => (SMTExpr t -> SMTExpr t -> SMTExpr Bool) -> [SMTExpr t] -> SMTExpr t -> SMTExpr Bool
minimumSMTBy _ [x] r = r .==. x
minimumSMTBy f xs r = app and' $ (app or' [ r .==. x | x <- xs ]):
                      [ f r x | x <- xs ]

#ifdef SMTExts
minimumSMT :: SMTOrd t => [SMTExpr t] -> SMTExpr t -> SMTExpr Bool
minimumSMT = minimumSMTBy (.<=.)
#else
minimumSMT :: IsBitVector t => [SMTExpr (BitVector t)] -> SMTExpr (BitVector t) -> SMTExpr Bool
minimumSMT = minimumSMTBy bvsle
#endif

instance Scheduling TimedScheduling where
  type SchedulingData TimedScheduling = TimedSchedulingData
  firstSchedule _ (TimedSchedulingData mp _ _) = app and' [ v .==. SMT.constant 0 | v <- Map.elems mp ]
  canSchedule _ name (TimedSchedulingData mp _ _) = (mp!name) .==. SMT.constant 0
  schedule _ name (TimedSchedulingData mp1 min p) (TimedSchedulingData mp2 _ _)
    = let mp1' = Map.adjust (+ (SMT.constant $ fromIntegral (p!name))) name mp1
      in app and' $ (minimumSMT (Map.elems mp1') min):
         (Map.elems $ Map.intersectionWith (\o n -> n .==. o - min) mp1' mp2)
  showSchedulingInformation _ (TimedSchedulingData mp min procs) = do
    mp' <- mapM SMT.getValue mp
    return $ show $ Map.toList mp'
  eqScheduling _ (TimedSchedulingData mp1 _ _) (TimedSchedulingData mp2 _ _) = app and' $ Map.elems $ Map.intersectionWith (.==.) mp1 mp2
  schedulingFairnessCount _ _ = 0
  schedulingFairness _ _ = []
  
data TimedScheduling2 = TimedScheduling2

data TimedSchedulingData2 = TimedSchedulingData2 
                            (Map String (SMTExpr (BitVector BVUntyped)))
                            (Map String Integer)
                            (Map String Integer)
                          deriving (Eq,Typeable,Show)

{-
countScheduleStates :: Integral a => [a] -> a
countScheduleStates procs = allStates - noZeroStates
  where
    procs' = fmap (`div` com) procs
    com = foldl1 gcd procs
    
    allStates = product (fmap (+1) procs')
    noZeroStates = product procs'

encodeScheduleState :: Integral a => [a] -> [a] -> a
encodeScheduleState limits num = 
-}

combinations :: [[a]] -> [[a]]
combinations [] = [[]]
combinations (xs:xxs) = [ (x:ys) | x <- xs, ys <- combinations xxs ]

findAndRemoveIndex :: (a -> Bool) -> [a] -> ([a],Int)
findAndRemoveIndex f = find' 0
  where
    find' n (x:xs) = if f x
                     then (xs,n)
                     else (let (rest,i) = find' (n+1) xs
                           in (x:rest,i))

restoreAt :: a -> Int -> [a] -> [a]
restoreAt x 0 ys = x:ys
restoreAt x n (y:ys) = y:(restoreAt x (n-1) ys)

normate :: Integral b => [(a,b)] -> [(a,b)]
normate xs = fmap (\(n,x) -> (n,x-m)) xs
  where
    m = minimum (fmap snd xs)

instance Args TimedSchedulingData2 where
  type ArgAnnotation TimedSchedulingData2 = Map String Integer
  foldExprs f s ~(TimedSchedulingData2 cs _ _) procs = do
    let md = foldl1 gcd procs
        cys = fmap (`div` md) procs
        ann = fmap (ceiling . logBase 2 . fromIntegral . (+1)) cys
    (s',cs') <- foldExprs f s cs ann
    return (s',TimedSchedulingData2 cs' cys ann)
  
instance Scheduling TimedScheduling2 where
  type SchedulingData TimedScheduling2 = TimedSchedulingData2
  firstSchedule _ (TimedSchedulingData2 bvs _ w) = app and' [ bv .==. (SMT.constantAnn (BitVector 0) (w!name)) | (name,bv) <- Map.toList bvs ]
  canSchedule _ name (TimedSchedulingData2 bvs _ w) = bvs!name .==. (SMT.constantAnn (BitVector 0) (w!name))
  schedule _ name (TimedSchedulingData2 bvs1 cys w) (TimedSchedulingData2 bvs2 _ _)
    = app or' [ app and' $ 
                [ bvs1!name .==. SMT.constantAnn (BitVector v) (w!name) | (name,v) <- cur ] ++
                [ bvs2!name' .==. SMT.constantAnn (BitVector v) (w!name') | (name',v) <- normate $ (name,cys!name):(zip onames x) ]
              | x <- combinations ranges
              , let cur = zip onames x
              ]
    where
      ranges = fmap (\l -> [0..l]) limits
      (onames,limits) = unzip cys'
      (cys',name_idx) = findAndRemoveIndex (\(name',_) -> name == name') $ Map.toList cys
  showSchedulingInformation _ (TimedSchedulingData2 mp _ _) = do
    mp' <- mapM SMT.getValue mp
    return $ show $ Map.toList mp'
  eqScheduling _ (TimedSchedulingData2 mp1 _ _) (TimedSchedulingData2 mp2 _ _)
    = app and' $ Map.elems $ Map.intersectionWith (.==.) mp1 mp2
  schedulingFairnessCount _ _ = 0
  schedulingFairness _ _ = []

-- | Saves the variables needed for the encoding of LTL properties
data TemporalVars v = TemporalVars { formulaEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxFEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxGEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   } deriving (Typeable,Eq,Show)

getTemporalVars :: Ord v => TypedExpr v -> (Map (TypedExpr v) (),
                                            Map (TypedExpr v) (),
                                            Map (TypedExpr v) (),
                                            Map (TypedExpr v) ())
getTemporalVars = getTemp (Map.empty,Map.empty,Map.empty,Map.empty)
  where
    getTemp cur@(f,auxF,auxG,nots) expr
      | Map.member expr f = cur
      | otherwise = case GTL.getValue (unfix expr) of
        GTL.Var name h u -> (Map.insert expr () f,auxF,auxG,nots)
        GTL.BinRelExpr _ _ _ -> (Map.insert expr () f,auxF,auxG,nots)
        GTL.BinBoolExpr op lhs rhs
          -> let cur1 = getTemp cur lhs
                 (f1,auxF1,auxG1,nots1) = getTemp cur1 rhs
                 f2 = Map.insert expr () f1
             in case op of
               GTL.Until NoTime -> (f2,Map.insert rhs () auxF1,auxG1,nots1)
               GTL.UntilOp NoTime -> (f2,auxF1,Map.insert rhs () auxG1,nots1)
               _ -> (f2,auxF1,auxG1,nots1)
        GTL.UnBoolExpr op arg
          -> let (f1,auxF1,auxG1,nots1) = getTemp cur arg
             in case op of
               GTL.Not -> (f1,auxF1,auxF1,Map.insert expr () nots1)
               GTL.Always -> let f2 = Map.insert expr () f1
                                 auxG2 = Map.insert arg () auxG1
                             in (f2,auxF1,auxG2,nots1)
               GTL.Finally NoTime -> let f2 = Map.insert expr () f1
                                         auxF2 = Map.insert arg () auxF1
                                     in (f2,auxF2,auxG1,nots1)
               _ -> let f2 = Map.insert expr () f1
                    in (f2,auxF1,auxG1,nots1)
        _ -> cur

instance (Typeable v,Show v,Ord v) => Args (TemporalVars v) where
  type ArgAnnotation (TemporalVars v) = (Map (TypedExpr v) (),
                                         Map (TypedExpr v) (),
                                         Map (TypedExpr v) (),
                                         Map (TypedExpr v) ())
  foldsExprs f s tvs (mp_f,mp_auxF,mp_auxG,mp_nots) = do
    (s1,fs,zfs) <- foldsExprs f s (fmap (\(x,b) -> (formulaEnc x,b)) tvs) mp_f
    (s2,auxFs,zauxFs) <- foldsExprs f s1 (fmap (\(x,b) -> (auxFEnc x,b)) tvs) mp_auxF
    (s3,auxGs,zauxGs) <- foldsExprs f s2 (fmap (\(x,b) -> (auxGEnc x,b)) tvs) mp_auxG
    let fs' = fmap (\cf -> Map.union
                           cf
                           (Map.mapWithKey (\key _ -> case GTL.getValue (unfix key) of
                                               GTL.UnBoolExpr GTL.Not arg -> not' $ cf!arg
                                           ) mp_nots)
                   ) fs
    return (s3,[ TemporalVars { formulaEnc = f'
                              , auxFEnc = auxF
                              , auxGEnc = auxG } | (f',auxF,auxG) <- zip3 fs auxFs auxGs ],
            TemporalVars { formulaEnc = zfs
                         , auxFEnc = zauxFs
                         , auxGEnc = zauxGs })
  extractArgAnnotation tv = let (not_f,f) = Map.partitionWithKey (\key _ -> case GTL.getValue (unfix key) of
                                                                     GTL.UnBoolExpr GTL.Not _ -> True
                                                                     _ -> False
                                                                 ) (formulaEnc tv)
                            in (fmap (const ()) f,
                                fmap (const ()) (auxFEnc tv),
                                fmap (const ()) (auxGEnc tv),
                                fmap (const ()) not_f)

data BMCConfig a = BMCConfig { bmcConfigCur :: a
                             , bmcConfigNext :: a -> a
                             , bmcConfigCompleteness :: a -> Bool
                             , bmcConfigCheckSat :: a -> Bool
                             , bmcConfigTerminate :: a -> Bool
                             , bmcConfigDebug :: a -> Bool
                             , bmcConfigUseStacks :: a -> Bool
                             , bmcConfigInline :: Bool
                             }

stack' :: BMCConfig c -> SMT a -> SMT a
stack' cfg = if bmcConfigUseStacks cfg (bmcConfigCur cfg) then stack else id                           

-- | Create a mapping from enum types to Integers for all the enums in the spec.
enumMap :: GlobalInfo -> Map [String] Integer
enumMap spec = let enums = getEnums (Map.unions [ Map.unions [gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl]
                                                | (iname,inst) <- Map.toList (instanceInfos spec),
                                                  let mdl = iiModel inst
                                                ])
               in Map.fromList (Prelude.zip (Set.toList enums) [0..])

-- | Create dependencies between the temporal variables of a previous and the current state
dependencies :: (Show v,Ord v) => (v -> VarUsage -> Integer -> GTLSMTExpr) -> TypedExpr v -> TemporalVars v -> TemporalVars v -> [SMTExpr Bool]
dependencies f expr cur nxt = case GTL.getValue (unfix expr) of
  GTL.Var v h u -> let GSMTBool var = f v u h
                   in [self .==. var]
  GTL.UnBoolExpr GTL.Not (Fix (Typed _ (GTL.Var v h u))) -> let GSMTBool var = f v u h
                                                            in [self .==. not' var]
  GTL.Value (GTLBoolVal x) -> []
  GTL.BinBoolExpr op lhs rhs -> let ls = dependencies f lhs cur nxt
                                    l = (formulaEnc cur)!lhs
                                    rs = dependencies f rhs cur nxt
                                    r = (formulaEnc cur)!rhs
                                in case op of
                                     GTL.And -> (self .==. (l .&&. r)):ls++rs
                                     GTL.Or -> (self .==. (l .||. r)):ls++rs
                                     GTL.Implies -> (self .==. (l .=>. r)):ls++rs
                                     GTL.Until NoTime -> (self .==. (r .||. (l .&&. nself))):ls++rs
                                     GTL.UntilOp NoTime -> (self .==. (r .&&. (l .||. nself))):ls++rs
  GTL.UnBoolExpr op e -> let es = dependencies f e cur nxt
                             e' = (formulaEnc cur)!e
                         in case op of
                              GTL.Always -> (self .==. (e' .&&. nself)):es
                              GTL.Finally NoTime -> (self .==. (e' .||. nself)):es
                              GTL.Next NoTime -> let ne = (formulaEnc nxt)!e
                                                 in (self .==. ne):es
                              _ -> es
  GTL.BinRelExpr _ _ _ -> let GSMTBool v = translateExpr f expr
                          in [self .==. v]
  _ -> []
  where
    self = (formulaEnc cur)!expr
    nself = (formulaEnc nxt)!expr

getProcs :: GlobalInfo -> Map String Integer
getProcs spec = fmap (\inst -> gtlModelCycleTime $ iiModel inst)
                (instanceInfos spec)

createSMTFunctions :: Scheduling s => BMCConfig a -> s -> GlobalInfo
                      -> SMT ((GlobalState,SchedulingData s) -> SMTExpr Bool,
                              (GlobalState,GlobalState,SchedulingData s,SchedulingData s) -> SMTExpr Bool,
                              (GlobalState,GlobalState) -> SMTExpr Bool,
                              GlobalState -> SMTExpr Bool)
createSMTFunctions cfg sched info = do
  let enums = enumMap info
      kenums = Map.keysSet enums
      procs = getProcs info
  funs <- fmap Map.fromAscList $
          mapM (\(name,inst) -> do
                   let (init,step) = instanceFuns kenums inst
                   init_fun <- mkFun cfg ("init_"++name) ("init function of "++name) (annInstanceInfo inst) init
                   step_fun <- mkFun cfg ("step_"++name) ("step function of "++name) (annInstanceInfo inst,annInstanceInfo inst) (uncurry step)
                   return (name,(init_fun,step_fun))
               ) (Map.toAscList (instanceInfos info))
  g_init_fun <- mkFun cfg "init" "global init function" (annGlobalInfo info,procs)
                (\(gst,sched_st) -> app and' $ (firstSchedule sched sched_st):
                                    [ fst (funs!name) lst 
                                    | (name,lst) <- Map.toList (instanceStates gst) ])
  g_step_fun <- mkFun cfg "step" "global step function" (annGlobalInfo info,annGlobalInfo info,procs,procs)
                (\(g1,g2,s1,s2)
                 -> app or' [ app and' $ [canSchedule sched name s1
                                         ,schedule sched name s1 s2
                                         ,snd (funs!name) (lst1,(instanceStates g2)!name)] ++
                              [ eqInstOutp lst2 ((instanceStates g2)!name') 
                              | (name',lst2) <- Map.toList (instanceStates g1), name/=name' ]
                            | (name,lst1) <- Map.toList (instanceStates g1) ])
  conn_fun <- mkFun cfg "conn" "connection function" (annGlobalInfo info,annGlobalInfo info)
              (connectionFun $ globalSpec info)
  const_fun <- mkFun cfg "constInps" "constant input function" (annGlobalInfo info)
               (defaultsFun $ globalSpec info)
  return (g_init_fun,g_step_fun,conn_fun,const_fun)

mkFun :: (Args a,ArgAnnotation a ~ b,SMTType c) => BMCConfig d -> String -> String -> b -> (a -> SMTExpr c) -> SMT (a -> SMTExpr c)
mkFun cfg name descr ann f 
  = if bmcConfigInline cfg
    then (do
             comment $ descr
             fun <- defFunAnnNamed name ann f
             return (app fun))
    else return f

bmc :: Scheduling s => BMCConfig a -> s -> GlobalInfo -> SMT (Maybe [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)])
bmc cfg sched spec = do
  let formula = GTL.distributeNot (gtlSpecVerify $ globalSpec spec)
      enums = enumMap spec
      kenums = Map.keysSet enums
      procs = getProcs spec
      annTV = getTemporalVars formula
#ifndef SMTExts
  setLogic "QF_BV"
#endif
  --setOption $ PrintSuccess False
  setOption $ ProduceModels True
  (g_init_fun,g_step_fun,conn_fun,const_fun) <- createSMTFunctions cfg sched spec
  dep_fun <- mkFun cfg "deps" "dependency function" (annGlobalInfo spec,annTV,annTV)
             (\(st,cur,nxt) -> app and' $ dependencies (\(iname,var) _ h -> let inst = (instanceStates st)!iname
                                                                            in case Map.lookup var (instanceInputVars inst) of
                                                                              Just v -> v
                                                                              Nothing -> case Map.lookup var (instanceOutputVars inst) of
                                                                                Just v -> v
                                                                                Nothing -> (instanceLocalVars inst)!var
                                                       ) formula cur nxt)

  tmp_cur <- argVarsAnn annTV
  tmp_e <- argVarsAnn annTV
  tmp_l <- argVarsAnn annTV
  loop_exists <- SMT.varNamed "loopExists"
  se <- argVarsAnn (annGlobalInfo spec)
  te <- argVarsAnn procs
  fe <- mapM (\_ -> SMT.varNamed "fairnessE") [1..(schedulingFairnessCount sched procs)]
  start_time <- liftIO getCurrentTime
  bmc' cfg sched spec conn_fun const_fun formula g_init_fun g_step_fun dep_fun tmp_cur tmp_e tmp_l loop_exists se te fe [] start_time

data BMCState s = BMCState { bmcVars :: GlobalState
                           , bmcTemporals :: TemporalVars (String,String)
                           , bmcL :: SMTExpr Bool
                           , bmcInLoop :: SMTExpr Bool
                           , bmcScheduling :: SchedulingData s
                           , bmcFairness :: [SMTExpr Bool]
                           }

bmc' :: (Scheduling s) => 
        BMCConfig a -> s -> GlobalInfo
     -> ((GlobalState,GlobalState) -> SMTExpr Bool)
     -> (GlobalState -> SMTExpr Bool)
     -> TypedExpr (String,String) 
     -> ((GlobalState,SchedulingData s) -> SMTExpr Bool)
     -> ((GlobalState,GlobalState,SchedulingData s,SchedulingData s) -> SMTExpr Bool)
     -> ((GlobalState,TemporalVars (String,String),TemporalVars (String,String)) -> SMTExpr Bool)
     -> TemporalVars (String,String) -> TemporalVars (String,String) -> TemporalVars (String,String)
     -> SMTExpr Bool -> GlobalState -> SchedulingData s -> [SMTExpr Bool] -> [BMCState s] -> UTCTime
     -> SMT (Maybe [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)])
bmc' cfg sched spec conn const_fun formula init step deps tmp_cur tmp_e tmp_l loop_exists se te fe [] start_time = do
  let annTV = getTemporalVars formula
  init_st <- argVarsAnn (annGlobalInfo spec)
  assert $ const_fun init_st
  l <- SMT.varNamed "l"
  inloop <- SMT.varNamed "inloop"
  comment "Scheduling data"
  sdata <- argVarsAnn (getProcs spec)
  assert $ init (init_st,sdata)
  assert $ conn (init_st,init_st)
  assert $ not' l
  assert $ not' inloop
  tmp_nxt <- argVarsAnn annTV
  assert $ deps (init_st,tmp_cur,tmp_nxt)
  assert $ (formulaEnc tmp_cur)!formula
  incPLTLbase loop_exists tmp_cur tmp_e tmp_l
  case fe of
    [] -> return ()
    _ -> assert $ loop_exists .=>. app and' fe
  let hist = [BMCState init_st tmp_cur l inloop sdata (fmap (const $ SMT.constant False) fe)]
  res <- if bmcConfigCheckSat cfg (bmcConfigCur cfg)
         then stack' cfg (do
                      -- k-variant case for LoopConstraints
                      assert $ eqSt se init_st
                      assert $ eqScheduling sched te sdata
                      assert $ not' loop_exists
                      -- k-variant case for LastStateFormula
                      mapM_ (\(expr,var) -> do
                               assert $ var .==. ((formulaEnc tmp_cur)!expr)
                               assert $ ((formulaEnc tmp_nxt)!expr) .==. ((formulaEnc tmp_l)!expr)
                            ) (Map.toList $ formulaEnc tmp_e)
                      -- k-variant case for IncPLTL
                      incPLTLvar tmp_cur tmp_e
                      solvable <- checkSat
                      if solvable
                        then getPath sched spec hist >>= return.Just
                        else return Nothing)
         else return Nothing
  case res of
    Nothing -> if bmcConfigTerminate cfg (bmcConfigCur cfg)
               then return Nothing
               else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched spec conn const_fun formula init step deps tmp_nxt tmp_e tmp_l loop_exists se te fe hist start_time
    Just path -> return $ Just path
bmc' cfg sched spec conn const_fun formula init step deps tmp_cur tmp_e tmp_l loop_exists se te fe history@(last_state:_) start_time = do
  let sdata = bmcScheduling last_state
      i = length history
      annTV = getTemporalVars formula
  ctime <- liftIO $ getCurrentTime
  if bmcConfigDebug cfg (bmcConfigCur cfg)
    then liftIO $ do
      putStrLn ("Depth: "++show i++" ("++show (ctime `diffUTCTime` start_time)++")")
      hFlush stdout
    else return ()
  cur_state <- argVarsAnn (annGlobalInfo spec)
  assert $ const_fun cur_state
  tmp_nxt <- argVarsAnn annTV
  cur_fair <- mapM (\(i,_) -> SMT.varNamed ("fair"++show i)) (zip [0..] fe)
  l <- SMT.varNamed "l"
  inloop <- SMT.varNamed "inloop"
  nsdata <- argVarsAnn (getProcs spec)
  assert $ step (bmcVars last_state,cur_state,sdata,nsdata)
  assert $ conn (cur_state,cur_state)

  -- k-invariant case for LoopConstraints:
  assert $ l .=>. (app and' [eqSt (bmcVars last_state) se
                            ,eqScheduling sched (bmcScheduling last_state) te])
  assert $ inloop .==. (app or' [bmcInLoop last_state,l])
  assert $ (bmcInLoop last_state) .=>. (not' l)
  
  -- k-invariant case for LastStateFormula
  assert $ deps (cur_state,tmp_cur,tmp_nxt)
  mapM_ (\(expr,var) -> assert $ l .=>. (var .==. ((formulaEnc tmp_cur)!expr))
        ) (Map.toList $ formulaEnc tmp_l)
  
  -- k-invariant case for IncPLTL
  mapM_ (\(expr,var) -> let Just fe = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. app or' [(auxFEnc $ bmcTemporals last_state)!expr
                                                     ,app and' [inloop,fe]]) (Map.toList $ auxFEnc tmp_cur)
  mapM_ (\(expr,var) -> let Just ge = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. app and' [(auxGEnc $ bmcTemporals last_state)!expr
                                                      ,app or' [not' $ inloop,ge]]) (Map.toList $ auxGEnc tmp_cur)
  
  -- k-invariant case for fairness
  mapM (\(cf,lf,cur) -> assert $ cf .==. app or' [lf,app and' [inloop,cur]]) (zip3 cur_fair (bmcFairness last_state) (schedulingFairness sched sdata))
  
  let history' = (BMCState cur_state tmp_cur l inloop nsdata cur_fair):history
  simple_path <- case bmcConfigCompleteness cfg (bmcConfigCur cfg) of
    False -> return True
    True -> do
      mapM_ (\st -> assert $ app or' [not' $ eqSt (bmcVars last_state) (bmcVars st)
                                     ,not' $ (bmcInLoop last_state) .==. (bmcInLoop st)
                                     ,not' $ ((formulaEnc (bmcTemporals last_state))!formula)
                                      .==. ((formulaEnc (bmcTemporals st))!formula)
                                     ,app and' [bmcInLoop last_state
                                               ,bmcInLoop st
                                               ,app or' [not' $ ((formulaEnc (bmcTemporals last_state))!formula) 
                                                         .==. ((formulaEnc (bmcTemporals st))!formula)]
                                               ]
                                     ]
            ) (Prelude.drop 1 history)
      checkSat
  -- This does neither
  {-simple_path <- if i==1 then return True
                 else stack $ do
                   assert $ forAllList (fromIntegral i - 1) $
                     \lis -> (exactlyOne lis) .=>. (existsState enums spec $
                                                    \st -> and' [ li .==. (eqSt st (bmcVars si)) | (li,si) <- zip lis (Prelude.drop 1 history) ])
                   checkSat-}
  if not simple_path
    then return Nothing
    else (do
           res <- if bmcConfigCheckSat cfg (bmcConfigCur cfg)
                  then (stack' cfg $ do
                          -- k-variant case for LoopConstraints
                          assert $ loop_exists .==. inloop
                          assert $ eqSt cur_state se
                          assert $ eqScheduling sched nsdata te
                          -- k-variant case for LastStateFormula
                          mapM_ (\(expr,var) -> do
                                   assert $ ((formulaEnc tmp_e)!expr) .==. var
                                   assert $ ((formulaEnc tmp_nxt)!expr) .==. ((formulaEnc tmp_l)!expr)
                                ) (Map.toList $ formulaEnc tmp_cur)
                          -- k-variant case for IncPLTL
                          incPLTLvar tmp_cur tmp_e
                          -- k-variant case for fairness
                          mapM_ (\(f_now,f_end) -> assert $ f_end .==. f_now) (zip cur_fair fe)
                          r <- checkSat
                          if r then getPath sched spec history' >>= return.Just
                               else return Nothing
                       )
                  else return Nothing
           case res of  
             Just path -> return $ Just path
             Nothing -> if bmcConfigTerminate cfg (bmcConfigCur cfg)
                        then return Nothing
                        else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched spec conn const_fun formula init step deps tmp_nxt tmp_e tmp_l loop_exists se te fe history' start_time)
  
incPLTLbase :: SMTExpr Bool -> TemporalVars (String,String) -> TemporalVars (String,String) -> TemporalVars (String,String) -> SMT ()
incPLTLbase loop_exists tmp_cur tmp_e tmp_l = mapM_ (\(expr,var) -> do
                                                       assert $ (not' loop_exists) .=>. (not' $ (formulaEnc tmp_l)!expr)
                                                       -- Base case for IncPLTL:
                                                       case GTL.getValue (unfix expr) of
                                                         GTL.UnBoolExpr (Finally NoTime) e -> do
                                                                                        let f_e = (auxFEnc tmp_e)!e
                                                                                        assert $ loop_exists .=>. (var .=>. f_e)
                                                                                        assert $ not' $ (auxFEnc tmp_cur)!e
                                                         GTL.UnBoolExpr Always e -> do
                                                           let g_e = (auxGEnc tmp_e)!e
                                                           assert $ loop_exists .=>. (g_e .=>. var)
                                                           assert $ (auxGEnc tmp_cur)!e
                                                         GTL.BinBoolExpr (Until NoTime) lhs rhs -> do
                                                                                        let f_e = (auxFEnc tmp_e)!rhs
                                                                                        assert $ loop_exists .=>. (var .=>. f_e)
                                                                                        assert $ not' $ (auxFEnc tmp_cur)!rhs
                                                         GTL.BinBoolExpr (UntilOp NoTime) lhs rhs -> do
                                                                                        let g_e = (auxGEnc tmp_e)!rhs
                                                                                        assert $ loop_exists .=>. (g_e .=>. var)
                                                                                        assert $ not' $ (auxGEnc tmp_cur)!rhs
                                                         _ -> return ()
                                                    ) (Map.toList $ formulaEnc tmp_e)

incPLTLvar :: TemporalVars (String,String) -> TemporalVars (String,String) -> SMT ()
incPLTLvar tmp_cur tmp_e = do
  mapM_ (\(expr,var) -> assert $ ((auxFEnc tmp_e)!expr) .==. var) (Map.toList $ auxFEnc tmp_cur)
  mapM_ (\(expr,var) -> assert $ ((auxGEnc tmp_e)!expr) .==. var) (Map.toList $ auxGEnc tmp_cur)
  
-- | Extract a whole path from the SMT solver
getPath :: Scheduling s => s -> GlobalInfo -> [BMCState s] -> SMT [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)]
getPath sched info = mapM (\st -> do
                              vars <- getVarValues $ bmcVars st
                              sts <- getAutomataStates (bmcVars st) info
                              loop <- SMT.getValue $ bmcL st
                              inf <- showSchedulingInformation sched $ bmcScheduling st
                              return (vars,sts,loop,inf)
                          ) . Prelude.reverse

-- | Extract the values for all variables in the state once the SMT solver has produced a model
getVarValues :: GlobalState -> SMT (Map (String,String) GTLConstant)
getVarValues st = do
  lst <- mapM (\(iname,inst) -> mapM (\(vname,var) -> do
                                         c <- getGTLValue var
                                         return ((iname,vname),c)) (Map.toList $ Map.unions [instanceInputVars inst,instanceOutputVars inst,instanceLocalVars inst])) (Map.toList $ instanceStates st)
  return $ Map.fromList (concat lst)

getAutomataStates :: GlobalState -> GlobalInfo -> SMT (Map (String,String) String)
getAutomataStates st info = do
  lst <- mapM (\(iname,(inst,iinfo)) -> mapM (\(c,(_,mp)) -> case mp of 
                                                 Nothing -> return Nothing
                                                 Just (aname,mp',_) -> do
                                                   vc <- SMT.getValue c
                                                   return $ Just ((iname,aname),mp'!vc)
                                             ) (zip (instanceAutomata inst) (iiAutomataMapping iinfo))
              ) $ Map.toList $ Map.intersectionWith (\inst iinfo -> (inst,iinfo)) (instanceStates st) (instanceInfos info)
  return $ Map.fromList $ catMaybes $ concat lst
  
-- | Once the SMT solver has produced a model, extract the value of a given GTL variable from it
getGTLValue :: GTLSMTExpr -> SMT GTLConstant
getGTLValue (GSMTInt v) = do
#if SMTExts
  r <- SMT.getValue v
  return $ Fix $ GTLIntVal r
#else
  BitVector r <- SMT.getValue v
  return $ Fix $ GTLIntVal r
#endif
getGTLValue (GSMTByte v) = do
  BitVector r <- SMT.getValue v
  return $ Fix $ GTLByteVal (fromIntegral r)
getGTLValue (GSMTBool v) = do
  r <- SMT.getValue v
  return $ Fix $ GTLBoolVal r
getGTLValue (GSMTEnum v vs) = do
  r <- SMT.getValue v
  return $ Fix $ GTLEnumVal $ enumGet vs r
getGTLValue (GSMTArray vs) = do
  rv <- mapM getGTLValue vs
  return $ Fix $ GTLArrayVal rv
getGTLValue (GSMTTuple vs) = do
  rv <- mapM getGTLValue vs
  return $ Fix $ GTLTupleVal rv

-- | Display an extracted path to the user
renderPath :: [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)] -> String
renderPath = unlines . concat . renderPath' 1 Map.empty Map.empty
  where
    renderPath' _ _ _ [] = []
    renderPath' n prev_mp prev_sts ((mp,sts,loop,sched):xs)
      = (("Step "++show n
          ++(if loop
             then " (loop starts here) "
             else " ")
          ++sched):[ "| "++iname++"."++var++" = "++show c
                   | ((iname,var),c) <- Map.toList $ Map.differenceWith (\cur last -> if cur==last
                                                                                      then Nothing
                                                                                      else Just cur) mp prev_mp ]++
         [ "| "++iname++"."++aname++" = "++c
         | ((iname,aname),c) <- Map.toList $ Map.differenceWith (\cur last -> if cur==last
                                                                              then Nothing
                                                                              else Just cur) sts prev_sts ]
        ):renderPath' (n+1) mp sts xs

normalConfig :: Maybe Integer -> Bool -> BMCConfig Integer
normalConfig bound compl 
    = BMCConfig { bmcConfigCur = 0
                , bmcConfigNext = \x -> x+1
                , bmcConfigCompleteness = const compl
                , bmcConfigCheckSat = const True
                , bmcConfigTerminate = case bound of
                                         Nothing -> const False
                                         Just limit -> \x -> x==limit
                , bmcConfigDebug = const True
                , bmcConfigUseStacks = const True
                , bmcConfigInline = True
                }

sonolarConfig :: Maybe Integer -> Bool -> BMCConfig Integer
sonolarConfig (Just limit) compl
    = BMCConfig { bmcConfigCur = limit 
                , bmcConfigNext = \x -> x - 1
                , bmcConfigCompleteness = const compl
                , bmcConfigCheckSat = \x -> x == 0
                , bmcConfigTerminate = \x -> x == 0
                , bmcConfigDebug = \x -> x==0
                , bmcConfigUseStacks = const False
                , bmcConfigInline = False
                }

noInlineConfig :: Maybe Integer -> Bool -> BMCConfig Integer
noInlineConfig bound cmpl = (normalConfig bound cmpl) { bmcConfigInline = False }

verifyModelBMC :: Options -> GTLSpec String -> IO ()
verifyModelBMC opts spec = do
  let solve = case smtBinary opts of
        Nothing -> withZ3
        Just x -> case words x of
          solv:args -> withPipe solv args
      info = getGlobalInfo spec
      act :: Scheduling s => s -> SMT (Maybe [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)])
      act sched = bmc ((if useSonolar opts then noInlineConfig
                        else normalConfig) (bmcBound opts) (bmcCompleteness opts)) sched info
  res <- case scheduling opts of
    "none" -> solve $ act SimpleScheduling
    "sync" -> solve $ act SyncScheduling
    "fair" -> solve $ act FairScheduling
    "timed" -> solve $ act TimedScheduling2
  case res of
    Nothing -> putStrLn "No errors found in model"
    Just path -> do
      writeTraces (replaceExtension (gtlFile opts) "gtltrace") [smtTraceToTrace info path]
      putStrLn $ renderPath path

smtTraceToTrace :: GlobalInfo -> [(Map (String,String) GTLConstant,Map (String,String) String,Bool,String)] -> [[TypedExpr (String,String)]]
smtTraceToTrace info xs 
  = [ [ geq (GTL.var tp (inst,v) 0 usage) (typedConstantToExpr tp c) 
      | ((inst,v),c) <- Map.toList mp 
      , let mdl = iiModel $ (instanceInfos info)!inst
      , (tp,usage) <- case Map.lookup v (gtlModelInput mdl) of
        Just tp' -> [(tp',Input)]
        Nothing -> case Map.lookup v (gtlModelOutput mdl) of
          Just tp' -> [(tp',Output)]
          Nothing -> []
        ]
    | (mp,_,_,_) <- xs ]

{-
-- | Apply limits to all integers used to store the current state of a component. Used to strengthen k-induction.
limitPCs :: Map String (BA [TypedExpr String] Integer) -> GlobalState -> SMTExpr Bool
limitPCs bas st = and' $ concat
                  [ [(instancePC inst) .>=. 0
                    ,(instancePC inst) .<. (SMT.constant (fromIntegral sz))]
                  | (name,inst) <- Map.toList (instanceStates st)
                  , let sz = Map.size $ baTransitions $ bas!name ]

-- | Perform k-induction by providing a solver and a GTL specification.
kInduction :: (Scheduling s) 
              => BMCConfig a -> s -> (SMT () -> IO ()) -> GTLSpec String -> IO (Maybe [Map (String,String) GTLConstant])
kInduction cfg sched solver spec = do
  let enums = enumMap spec
      bas = fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               formula = List.foldl1 gand $ fmap gtlContractFormula $ (gtlInstanceContract inst)++(gtlModelContract mdl)
                           in gtl2ba (Just (gtlModelCycleTime mdl)) formula) (gtlSpecInstances spec)
      procs = getProcs spec
      Fix (Typed _ (UnBoolExpr Always formula)) = gtlSpecVerify spec
      --(init,step) = schedule sched (Map.keysSet enums) spec
  baseCaseOrders <- newChan
  indCaseOrders <- newChan
  baseCaseResults <- newChan
  indCaseResults <- newChan
  baseCase <- forkIO $ solver $ do
    (init_fun,step_fun,conn) <- createSMTFunctions cfg sched spec
    sched_data <- argVarsAnn procs
    start <- argVarsAnn spec
    assert $ init_fun (start,sched_data)
    kInductionBase baseCaseOrders baseCaseResults (encodeProperty formula) enums spec conn step_fun sched sched_data [] start 1
  indCase <- forkIO $ solver $ do
    (_,step_fun,conn) <- createSMTFunctions cfg sched spec
    sched_data <- argVarsAnn procs
    start <- argVarsAnn spec
    kInductionInd indCaseOrders indCaseResults (encodeProperty formula) enums spec bas conn step_fun sched sched_data start 1 
  kInduction' baseCaseOrders indCaseOrders baseCaseResults indCaseResults

kInduction' :: Chan Bool -> Chan Bool -> Chan (Maybe [Map (String,String) GTLConstant]) -> Chan Bool -> IO (Maybe [Map (String,String) GTLConstant])
kInduction' baseCaseOrders indCaseOrders baseCaseResults indCaseResults = do
  writeChan baseCaseOrders True
  writeChan indCaseOrders True
  base <- readChan baseCaseResults
  case base of
    Just counterExample -> do
      writeChan indCaseOrders False
      return (Just counterExample)
    Nothing -> do
      ind <- readChan indCaseResults
      if ind
        then return Nothing
        else kInduction' baseCaseOrders indCaseOrders baseCaseResults indCaseResults


encodeProperty :: TypedExpr (String,String) -> GlobalState -> SMTExpr Bool
encodeProperty expr st = let GSMTBool var = translateExpr (\(m,n) u h -> getVar n u $ (instanceStates st)!m) expr
                         in var

kInductionBase :: (Scheduling s) 
                  => Chan Bool -> Chan (Maybe [Map (String,String) GTLConstant])
                  -> (GlobalState -> SMTExpr Bool)
                  -> Map [String] Integer -> GTLSpec String 
                  -> ((GlobalState,GlobalState) -> SMTExpr Bool)
                  -> ((GlobalState,GlobalState,SchedulingData s,SchedulingData s) -> SMTExpr Bool)
                  -> s -> SchedulingData s
                  -> [GlobalState] -> GlobalState -> Integer -> SMT ()
kInductionBase orders results prop enums spec conn step sched sched_data all last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ conn (last,last)
             res <- stack $ do
               assert $ not' $ prop last
               r <- checkSat
               if r then (do
                             -- A counter example has been found
                             path <- mapM getVarValues (Prelude.reverse $ (last:all))
                             return (Just path)
                         )
                 else return Nothing
             case res of
               Just path -> liftIO $ writeChan results (Just path)
               Nothing -> do
                 liftIO $ writeChan results Nothing
                 next <- argVarsAnn spec
                 assert $ prop last
                 assert $ step (last,next,sched_data,sched_data)
                 kInductionBase orders results prop enums spec conn step sched sched_data (last:all) next (n+1)
         )
    else return ()

kInductionInd :: (Scheduling s) 
                 => Chan Bool -> Chan Bool
                 -> (GlobalState -> SMTExpr Bool)
                 -> Map [String] Integer -> GTLSpec String
                 -> Map String (BA [TypedExpr String] Integer)
                 -> ((GlobalState,GlobalState) -> SMTExpr Bool)
                 -> ((GlobalState,GlobalState,SchedulingData s,SchedulingData s) -> SMTExpr Bool)
                 -> s -> SchedulingData s
                 -> GlobalState -> Integer -> SMT ()
kInductionInd orders results prop enums spec bas conn step sched sched_data last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ conn (last,last)
             assert $ limitPCs bas last
             res <- stack $ do
               assert $ not' $ prop last
               checkSat
             if res then (do
                             -- The property is not n-inductive
                             liftIO $ writeChan results False
                             next <- argVarsAnn spec
                             assert $ prop last
                             --assert $ step bas last next
                             assert $ step (last,next,sched_data,sched_data)
                             kInductionInd orders results prop enums spec bas conn step sched sched_data next (n+1)
                         )
               else (liftIO $ writeChan results True)
         )
    else return ()


-- | Verify a given specification using K-Induction
verifyModelKInduction :: Maybe String -> GTLSpec String -> IO ()
verifyModelKInduction solver spec = do
  let solve = case solver of
        Nothing -> withZ3
        Just x -> withSMTSolver x
  res <- kInduction (noInlineConfig Nothing False) SimpleScheduling solve spec
  case res of
    Nothing -> putStrLn "No errors found in model"
    Just path -> putStrLn $ renderPath [ (st,False,"") | st <- path ] -}

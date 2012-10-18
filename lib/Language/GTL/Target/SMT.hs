{-# LANGUAGE RankNTypes,DeriveDataTypeable,ExistentialQuantification,TypeFamilies,CPP,FlexibleContexts,FlexibleInstances #-}
module Language.GTL.Target.SMT where

import Data.Typeable
import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.Types
import Language.GTL.Buchi
import Language.GTL.Translation
import Language.SMTLib2 as SMT
import Language.SMTLib2.Solver
import Language.SMTLib2.Internals as SMT
import Data.Text as T hiding (intersperse,length,concat,unlines,zip)
import Data.Map as Map hiding ((!))
import Data.Set as Set
import Data.AttoLisp as L
import Control.Monad.Trans
import Data.Traversable
import Prelude hiding (mapM,sequence)
import Data.List (genericIndex,intersperse)
import Data.Word
import Control.Concurrent
import Misc.ProgramOptions
import Data.List as List
import Data.Time
import System.IO (hFlush,stdout)

#ifdef SMTExts
type GTLSMTPc = Integer
type GTLSMTInt = Integer
#else
type GTLSMTPc = Word64
type GTLSMTInt = Word64
#endif

(!) :: (Ord k,Show k) => Map k v -> k -> v
(!) mp k = case Map.lookup k mp of
             Nothing -> error $ "Can't find key "++show k++" in "++show (Map.keys mp)
             Just v -> v

-- | Used to represent Enum values.
data EnumVal = EnumVal String deriving (Typeable,Eq)

instance ToGTL EnumVal where
  toGTL (EnumVal name) = GTLEnumVal name
  --gtlTypeOf (EnumVal enums _ _) = Fix $ GTLEnum enums

instance SMTType EnumVal where
  type SMTAnnotation EnumVal = [String]
#ifdef SMTExts
  getSort _ vals = L.Symbol (T.pack $ "Enum"++concat [ "_"++val | val <- vals ])
  declareType u vals = let name = "Enum"++concat [ "_"++val | val <- vals ] 
                       in declareType' (typeOf u) (declareDatatypes [] [(T.pack $ name,[(T.pack val,[]) | val <- vals])]) (return ())
  additionalConstraints _ _ _ = []
#else
  getSort _ vals = let bits = ceiling $ logBase 2 $ fromIntegral (List.length vals)
                   in getSort (undefined::BitVector) (fromIntegral bits) --L.List [L.Symbol "_",L.Symbol "BitVec",show bits]
  declareType _ vals = return ()
  additionalConstraints _ enums var = [BVULE var (SMT.constantAnn (EnumVal $ List.last enums) enums)]
#endif

instance SMTValue EnumVal where
#ifdef SMTExts
  mangle (EnumVal v) _ = L.Symbol $ T.pack v
  unmangle (L.Symbol v) vals = return $ Just $ EnumVal (T.unpack v)
  unmangle _ _ = return Nothing
#else
  mangle (EnumVal v) vals = let bits = ceiling $ logBase 2 $ fromIntegral (List.length vals)
                                Just idx = List.elemIndex v vals
                            in mangle (BitVector $ fromIntegral idx) (fromIntegral bits)
  unmangle v vs = do
    let bits = ceiling $ logBase 2 $ fromIntegral (List.length vs)
    v' <- unmangle v (fromIntegral bits)
    case v' of
      Nothing -> return Nothing
      Just (BitVector v'') -> return $ Just $ EnumVal $ vs!!(fromIntegral v'')
#endif

data GTLSMTExpr = GSMTInt { asSMTInt :: SMTExpr GTLSMTInt }
                | GSMTByte { asSMTByte :: SMTExpr Word8 }
                | GSMTBool { asSMTBool :: SMTExpr Bool }
                | GSMTEnum { asSMTEnum :: SMTExpr EnumVal }
                | GSMTArray { asSMTArray :: [GTLSMTExpr] }
                | GSMTTuple { asSMTTuple :: [GTLSMTExpr] }
                deriving (Eq,Typeable)

instance Args GTLSMTExpr where
  type ArgAnnotation GTLSMTExpr = GTLType
  foldExprs f s e (Fix GTLInt) = let (s',e') = f s (asSMTInt e) ()
                                 in (s',GSMTInt e')
  foldExprs f s e (Fix GTLByte) = let (s',e') = f s (asSMTByte e) ()
                                 in (s',GSMTByte e')
  foldExprs f s e (Fix GTLBool) = let (s',e') = f s (asSMTBool e) ()
                                  in (s',GSMTBool e')
  foldExprs f s e (Fix (GTLEnum vs)) = let (s',e') = f s (asSMTEnum e) vs
                                       in (s',GSMTEnum e')
  foldExprs f s e (Fix (GTLArray len tp)) = let (s',arr) = lenMapAccumL len (\cs el -> foldExprs f cs el tp) s (asSMTArray e)
                                            in (s',GSMTArray arr)
  foldExprs f s e (Fix (GTLTuple tps)) = let (s',els) = List.mapAccumL (\cs (tp,el) -> foldExprs f cs el tp) s (unsafeZip tps (asSMTTuple e))
                                         in (s',GSMTTuple els)
  foldExprs f s e (Fix (GTLNamed name tp)) = foldExprs f s e tp

lenMapAccumL :: Integer -> (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
lenMapAccumL 0 f s _ = (s,[])
lenMapAccumL n f s ~(x:xs) = let (s',y) = f s x
                                 (s'',ys) = lenMapAccumL (n-1) f s' xs
                             in (s'',y:ys)

unsafeZip :: [a] -> [b] -> [(a,b)]
unsafeZip [] _ = []
unsafeZip (x:xs) ~(y:ys) = (x,y):unsafeZip xs ys

-- | Saves the variables of one instance (including the state variable of the state machine)
data InstanceState = InstanceState
                     { instanceInputVars :: Map String GTLSMTExpr
                     , instanceOutputVars :: Map String GTLSMTExpr
                     , instanceLocalVars :: Map String GTLSMTExpr
                     , instancePC :: SMTExpr GTLSMTPc -- ^ Saves the state of the state machine
                     } deriving (Eq,Typeable)

getVar :: String -> VarUsage -> InstanceState -> GTLSMTExpr
getVar name u is = let mp = case u of
                              Input -> instanceInputVars is
                              Output -> instanceOutputVars is
                              _ -> instanceLocalVars is
                   in case Map.lookup name mp of
                        Nothing -> error $ "Variable "++show name++" ("++show u++") not found in "++show (Map.keys mp)
                        Just v -> v

instance Args InstanceState where
  type ArgAnnotation InstanceState = GTLModel String
  foldExprs f s is mdl = let (s1,inp) = List.mapAccumL (\cs (name,tp) -> let (cs',val') = foldExprs f cs ((instanceInputVars is)!name) tp
                                                                         in (cs',(name,val'))
                                                       ) s (Map.toAscList $ gtlModelInput mdl)
                             (s2,outp) = List.mapAccumL (\cs (name,tp) -> let (cs',val') = foldExprs f cs ((instanceOutputVars is)!name) tp
                                                                          in (cs',(name,val'))
                                                        ) s1 (Map.toAscList $ gtlModelOutput mdl)
                             (s3,loc) = List.mapAccumL (\cs (name,tp) -> let (cs',val') = foldExprs f cs ((instanceLocalVars is)!name) tp
                                                                         in (cs',(name,val'))
                                                        ) s2 (Map.toAscList $ gtlModelLocals mdl)
                             (s4,pc') = f s3 (instancePC is) ()
                         in (s4,InstanceState { instanceInputVars = Map.fromAscList inp
                                              , instanceOutputVars = Map.fromAscList outp
                                              , instanceLocalVars = Map.fromAscList loc 
                                              , instancePC = pc' })

-- | Saves the variables of all components in the GALS system
data GlobalState = GlobalState
                   { instanceStates :: Map String InstanceState
                   } deriving (Eq,Typeable)

instance Args GlobalState where
  type ArgAnnotation GlobalState = GTLSpec String
  foldExprs f s gs spec = let (s',gs') = List.mapAccumL (\cs (name,inst) -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                                                                (cs',is) = foldExprs f cs ((instanceStates gs)!name) mdl
                                                                            in (cs',(name,is))
                                                        ) s (Map.toAscList (gtlSpecInstances spec))
                          in (s',GlobalState { instanceStates = Map.fromAscList gs' })

indexGTLSMT :: GTLSMTExpr -> [Integer] -> GTLSMTExpr
indexGTLSMT x [] = x
indexGTLSMT (GSMTArray arr) (i:is) = indexGTLSMT (arr `genericIndex` i) is
indexGTLSMT (GSMTTuple arr) (i:is) = indexGTLSMT (arr `genericIndex` i) is

eqGTLSMT :: GTLSMTExpr -> GTLSMTExpr -> SMTExpr Bool
eqGTLSMT (GSMTInt l) (GSMTInt r) = l .==. r
eqGTLSMT (GSMTByte l) (GSMTByte r) = l .==. r
eqGTLSMT (GSMTBool l) (GSMTBool r) = l .==. r
eqGTLSMT (GSMTEnum l) (GSMTEnum r) = l .==. r
eqGTLSMT (GSMTArray l) (GSMTArray r) = and' $ List.zipWith eqGTLSMT l r
eqGTLSMT (GSMTTuple l) (GSMTTuple r) = and' $ List.zipWith eqGTLSMT l r

eqInst :: InstanceState -> InstanceState -> SMTExpr Bool
eqInst l r = and' $ (Map.elems $ Map.intersectionWith eqGTLSMT (instanceInputVars l) (instanceInputVars r)) ++
             (Map.elems $ Map.intersectionWith eqGTLSMT (instanceOutputVars l) (instanceOutputVars r)) ++
             (Map.elems $ Map.intersectionWith eqGTLSMT (instanceLocalVars l) (instanceLocalVars r))

eqSt :: GlobalState -> GlobalState -> SMTExpr Bool
eqSt l r = and' $ Map.elems $ Map.intersectionWith eqInst (instanceStates l) (instanceStates r)

connectionFun :: GTLSpec String -> (GlobalState,GlobalState) -> SMTExpr Bool
connectionFun spec = \(stf,stt) -> and' [ eqGTLSMT (indexGTLSMT ((instanceOutputVars $ (instanceStates stf)!f)!fv) fi)
                                                   (indexGTLSMT ((instanceInputVars $ (instanceStates stt)!t)!tv) ti)
                                          | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- gtlSpecConnections spec
                                        ]

translateRel :: SMTOrd a => Relation -> SMTExpr a -> SMTExpr a -> SMTExpr Bool
translateRel BinLT = (.<.)
translateRel BinLTEq = (.<=.)
translateRel BinGT = (.>.)
translateRel BinGTEq = (.>=.)
translateRel BinEq = (.==.)
translateRel BinNEq = \l r -> not' (l .==. r)

-- | Translate a GTL expression into a SMT expression
translateExpr :: (v -> VarUsage -> Integer -> GTLSMTExpr) -> TypedExpr v -> GTLSMTExpr
translateExpr f (Fix expr)
  = case GTL.getValue expr of
    GTL.Var n i u -> f n u i
    GTL.Value val -> case val of
      GTLIntVal i ->  GSMTInt $ SMT.constant (fromIntegral i)
      GTLByteVal w -> GSMTByte $ SMT.constant w
      GTLBoolVal b -> GSMTBool $ SMT.constant b
      GTLEnumVal v -> let Fix (GTLEnum vals) = GTL.getType expr
                      in GSMTEnum $ SMT.constantAnn (EnumVal v) vals
      GTLArrayVal vs -> GSMTArray $ fmap (translateExpr f) vs
      GTLTupleVal vs -> GSMTTuple $ fmap (translateExpr f) vs
    GTL.BinRelExpr BinEq l r -> GSMTBool $ eqGTLSMT (translateExpr f l) (translateExpr f r)
    GTL.BinRelExpr BinNEq l r -> GSMTBool $ not' $ eqGTLSMT (translateExpr f l) (translateExpr f r)
    GTL.BinRelExpr rel l r -> let ll = translateExpr f l
                                  rr = translateExpr f r
                                  mkRel rel (GSMTInt l) (GSMTInt r) = translateRel rel l r
                                  mkRel rel (GSMTByte l) (GSMTByte r) = translateRel rel l r
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
                                              GTL.And -> and' [ll,rr]
                                              GTL.Or -> or' [ll,rr]
                                              GTL.Implies -> ll .=>. rr
    GTL.UnBoolExpr GTL.Not arg -> let GSMTBool arg' = translateExpr f arg
                                  in GSMTBool $ not' arg'
    _ -> error $ "Implement translateExpr for " ++ showTermWith (\_ _ -> showString "_") (\_ _ -> showString "_") 0 (GTL.getValue expr) ""

-- | Perform a calculation step in a single component
instanceFuns :: Set [String] -> GTLModel String -> [GTLContract String] -> (InstanceState -> SMTExpr Bool,InstanceState -> InstanceState -> SMTExpr Bool)
instanceFuns enums mdl contr
  = (init,step)
    where
      ba = gtl2ba (Just (gtlModelCycleTime mdl)) formula
      formula = List.foldl1 gand $ fmap gtlContractFormula $ contr++(gtlModelContract mdl)
      init inst = and' $ (or' [ (instancePC inst) .==. SMT.constant (fromIntegral f)
                              | f <- Set.toList (baInits ba) ]):
                [ eqGTLSMT
                  (case Map.lookup var (instanceInputVars inst) of
                     Just var' -> var'
                     Nothing -> case Map.lookup var (instanceOutputVars inst) of
                                  Just var' -> var'
                                  Nothing -> (instanceLocalVars inst)!var)
                  (translateExpr (\v u _ -> getVar v u inst) (constantToExpr enums def))
                  | (var,Just def) <- Map.toList $ gtlModelDefaults mdl ]
      step stf stt = and' [ (instancePC stf .==. SMT.constant (fromIntegral st)) .=>. 
                            or' [ and' ((instancePC stt .==. SMT.constant (fromIntegral trg)):
                                        [let GSMTBool v = translateExpr (\v u i -> case u of
                                                                                     Input -> (instanceInputVars stf)!v
                                                                                     StateIn -> (instanceLocalVars stf)!v
                                                                                     Output -> (instanceOutputVars stt)!v
                                                                                     StateOut -> (instanceLocalVars stt)!v) c
                                         in v
                                         | c <- cond ])
                                  | (cond,trg) <- trans
                                ]
                            | (st,trans) <- Map.toList (baTransitions ba) ]

-- | Asserts that two instance states are equal in their output and state variables.
eqInstOutp :: InstanceState -> InstanceState -> SMTExpr Bool
eqInstOutp st1 st2 
  = and' ((instancePC st1 .==. instancePC st2):
          ((Map.elems $ Map.intersectionWith eqGTLSMT (instanceOutputVars st1) (instanceOutputVars st2))++
           (Map.elems $ Map.intersectionWith eqGTLSMT (instanceLocalVars st1) (instanceLocalVars st2))))

-- | A scheduling dictates which instance may perform a calculation step at which point in time.
class Scheduling s where
  -- | A scheduling may define extra data it needs to perform the scheduling
  type SchedulingData s
  initializeScheduling :: s -> SchedulingData s -> SMTExpr Bool
  -- | Perform scheduling on two global states: The current one and the next one
  schedule :: s
              -> Set [String]
              -> ArgAnnotation (SchedulingData s)
              -> (SchedulingData s 
                  -> GlobalState 
                  -> SMTExpr Bool,
                  SchedulingData s -- ^ The current scheduling data
                  -> SchedulingData s -- ^ The next scheduling data
                  -> GlobalState -- ^ The current state
                  -> GlobalState -- ^ The next state
                  -> SMTExpr Bool)
  showSchedulingInformation :: s -> SchedulingData s -> SMT String
  eqScheduling :: s -> SchedulingData s -> SchedulingData s -> SMTExpr Bool

data SimpleScheduling = SimpleScheduling

data SimpleSchedulingData = SimpleSchedulingData deriving (Typeable,Eq)

instance Args SimpleSchedulingData where
  type ArgAnnotation SimpleSchedulingData = GTLSpec String
  foldExprs _ s _ _ = (s,SimpleSchedulingData)

instance Scheduling SimpleScheduling where
  type SchedulingData SimpleScheduling = SimpleSchedulingData
  initializeScheduling _ _ = SMT.constant True
  schedule _ enums spec = (init,step)
    where
      init _ st = and' (Map.elems $ Map.intersectionWith (\(fun,_) inst -> fun inst) funs (instanceStates st))
      step _ _ stf stt = or' [ and' (((snd $ funs!iname)
                                      ((instanceStates stf)!iname)
                                      ((instanceStates stt)!iname))
                                     :[ eqInstOutp inst ((instanceStates stt)!iname')
                                        | (iname',inst) <- Map.toList (instanceStates stf)
                                      , iname /= iname'
                                      ])
                               | (iname,inst) <- Map.toList (gtlSpecInstances spec)
                             ]
      funs = fmap (\inst -> instanceFuns enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) (gtlInstanceContract inst)) (gtlSpecInstances spec)
  showSchedulingInformation _ _ = return "none"
  eqScheduling _ _ _ = SMT.constant True

data FairScheduling = FairScheduling

newtype FairSchedulingData = FairSchedulingData (Map String (SMTExpr Bool)) deriving (Typeable,Eq)

instance Args FairSchedulingData where
  type ArgAnnotation FairSchedulingData = GTLSpec String
  foldExprs f s ~(FairSchedulingData mp) spec = let (s',mp') = List.mapAccumL (\cs (name,_) -> let (cs',e) = f cs (mp!name) ()
                                                                                               in (cs',(name,e))) s (Map.toAscList (gtlSpecInstances spec))
                                                in (s',FairSchedulingData $ Map.fromAscList mp')

instance Scheduling FairScheduling where
  type SchedulingData FairScheduling = FairSchedulingData
  initializeScheduling _ (FairSchedulingData mp) = and' (fmap not' $ Map.elems mp)
  schedule _ enums spec = (init,step)
    where
      funs = fmap (\inst -> instanceFuns enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) (gtlInstanceContract inst)) (gtlSpecInstances spec)
      init _ st = and' (Map.elems $ Map.intersectionWith (\(fun,_) inst -> fun inst) funs (instanceStates st))
      step (FairSchedulingData ps) (FairSchedulingData ps') stf stt
          = let smap = Map.intersectionWithKey (\name p1 p2 -> let inst = (gtlSpecInstances spec)!name
                                                               in (p1,p2,and' $ ((snd $ funs!name) ((instanceStates stf)!name) ((instanceStates stt)!name))
                                                                         :[ eqInstOutp inst ((instanceStates stt)!name')
                                                                            | (name',inst) <- Map.toList (instanceStates stf)
                                                                          , name /= name'
                                                                          ])) ps ps'
            in or' $ (and' $ (or' [ and' $ sched:p2:[ not' p2' 
                                                      | (name',(_,p2',_)) <- Map.toList smap
                                                    , name /= name'
                                                    ]
                                    | (name,(p1,p2,sched)) <- Map.toList smap
                                  ]):(Map.elems ps)):
                   [and' $ sched:(not' p1):p2
                    :[ p1' .==. p2'
                       | (name',(p1',p2',_)) <- Map.toList smap
                     , name /= name'
                     ]
                    | (name,(p1,p2,sched)) <- Map.toList smap ]
  showSchedulingInformation _ (FairSchedulingData mp) = do
    mp' <- mapM (\(name,x) -> do
                    vx <- SMT.getValue x
                    return $ name ++ ":" ++ (if vx then "1" else "0")
                ) (Map.toList mp)
    return $ show mp'
  eqScheduling _ (FairSchedulingData p1) (FairSchedulingData p2)
      = and' $ Map.elems $ Map.intersectionWith (.==.) p1 p2

-- | Saves the variables needed for the encoding of LTL properties
data TemporalVars v = TemporalVars { formulaEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxFEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxGEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   } deriving (Typeable,Eq)

instance Args (TemporalVars (String,String)) where
  type ArgAnnotation (TemporalVars (String,String)) = TypedExpr (String,String)
  foldExprs f s tv expr = foldTV s tv (TemporalVars Map.empty Map.empty Map.empty) expr
      where
        foldTV s tv ntv expr
            | Map.member expr (formulaEnc ntv) = (s,ntv)
            | otherwise = case GTL.getValue (unfix expr) of
                            GTL.Var name h u -> let (s',nvar) = f s ((formulaEnc tv)!expr) ()
                                                in (s',ntv { formulaEnc = Map.insert expr nvar (formulaEnc ntv) })
                            GTL.BinRelExpr _ _ _ -> let (s',nvar) = f s ((formulaEnc tv)!expr) ()
                                                    in (s',ntv { formulaEnc = Map.insert expr nvar (formulaEnc ntv) })
                            GTL.BinBoolExpr op lhs rhs -> let (s1,ntv1) = foldTV s tv ntv lhs
                                                              (s2,ntv2) = foldTV s1 tv ntv1 rhs
                                                              (s3,v) = f s2 ((formulaEnc tv)!expr) ()
                                                              ntv3 = ntv2 { formulaEnc = Map.insert expr v (formulaEnc ntv2) }
                                                          in case op of
                                                               GTL.Until NoTime
                                                                   | Map.member rhs (auxFEnc ntv3) -> (s3,ntv3)
                                                                   | otherwise -> let (s4,v2) = f s3 ((auxFEnc tv)!rhs) ()
                                                                                  in (s4,ntv3 { auxFEnc = Map.insert rhs v2 (auxFEnc ntv3) })
                                                               GTL.UntilOp NoTime
                                                                   | Map.member rhs (auxGEnc ntv3) -> (s3,ntv3)
                                                                   | otherwise -> let (s4,v2) = f s3 ((auxGEnc tv)!rhs) ()
                                                                                  in (s4,ntv3 { auxGEnc = Map.insert rhs v2 (auxGEnc ntv3) })
                                                               _ -> (s3,ntv3)
                            GTL.UnBoolExpr op arg -> let (s1,ntv1) = foldTV s tv ntv arg
                                                     in case op of
                                                          GTL.Not -> (s1,ntv1 { formulaEnc = Map.insert expr (not' ((formulaEnc ntv1)!arg)) (formulaEnc ntv1) })
                                                          GTL.Always -> let (s2,v1) = f s1 ((formulaEnc tv)!expr) ()
                                                                            (s3,aux') = if Map.member arg (auxGEnc ntv1)
                                                                                        then (s2,auxGEnc ntv1)
                                                                                        else (let (s',v2) = f s2 ((auxGEnc tv)!arg) ()
                                                                                              in (s',Map.insert arg v2 (auxGEnc ntv1)))
                                                                        in (s3,ntv1 { formulaEnc = Map.insert expr v1 (formulaEnc ntv1)
                                                                                    , auxGEnc = aux' })
                                                          GTL.Finally NoTime -> let (s2,v1) = f s1 ((formulaEnc tv)!expr) ()
                                                                                    (s3,aux') = if Map.member arg (auxFEnc ntv1)
                                                                                                then (s2,auxFEnc ntv1)
                                                                                                else (let (s',v2) = f s2 ((auxFEnc tv)!arg) ()
                                                                                                      in (s',Map.insert arg v2 (auxFEnc ntv1)))
                                                                                in (s3,ntv1 { formulaEnc = Map.insert expr v1 (formulaEnc ntv1) 
                                                                                            , auxFEnc = aux' })
                            _ -> (s,ntv)

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
enumMap :: Ord v => GTLSpec v -> Map [String] Integer
enumMap spec = let enums = getEnums (Map.unions [ Map.unions [gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl]
                                                | (iname,inst) <- Map.toList (gtlSpecInstances spec),
                                                  let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
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
                                     GTL.And -> (self .==. and' [l,r]):ls++rs
                                     GTL.Or -> (self .==. or' [l,r]):ls++rs
                                     GTL.Implies -> (self .==. (l .=>. r)):ls++rs
                                     GTL.Until NoTime -> (self .==. or' [r,and' [l,nself]]):ls++rs
                                     GTL.UntilOp NoTime -> (self .==. and' [r,or' [l,nself]]):ls++rs
  GTL.UnBoolExpr op e -> let es = dependencies f e cur nxt
                             e' = (formulaEnc cur)!e
                         in case op of
                              GTL.Always -> (self .==. and' [e',nself]):es
                              GTL.Finally NoTime -> (self .==. or' [e',nself]):es
                              _ -> es
  GTL.BinRelExpr _ _ _ -> let GSMTBool v = translateExpr f expr
                          in [self .==. v]
  _ -> []
  where
    self = (formulaEnc cur)!expr
    nself = (formulaEnc nxt)!expr

bmc :: (Scheduling s,Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ GTLSpec String) => BMCConfig a -> s -> GTLSpec String -> SMT (Maybe [(Map (String,String) GTLConstant,Bool,String)])
bmc cfg sched spec = do
#ifndef SMTExts  
  setLogic $ T.pack "QF_BV"
#endif
  setOption $ PrintSuccess False
  setOption $ ProduceModels True
  let formula = GTL.distributeNot (gtlSpecVerify spec)
      enums = enumMap spec
      (init,step) = schedule sched (Map.keysSet enums) spec
  init_fun <- (if bmcConfigInline cfg
               then fmap app . defFunAnn (spec,spec) () 
               else return) $ \(sdata,st) -> init sdata st
  step_fun <- (if bmcConfigInline cfg
               then fmap app . defFunAnn ((spec,spec),(spec,spec)) ()
               else return) $ \((sdata1,st1),(sdata2,st2)) -> step sdata1 sdata2 st1 st2
  dep_fun <- (if bmcConfigInline cfg
              then fmap app . defFunAnn (spec,formula,formula) ()
              else return) $ \(st,cur,nxt) -> and' $ dependencies (\(iname,var) _ h -> let inst = (instanceStates st)!iname
                                                                                       in case Map.lookup var (instanceInputVars inst) of
                                                                                            Just v -> v
                                                                                            Nothing -> case Map.lookup var (instanceOutputVars inst) of
                                                                                                         Just v -> v
                                                                                                         Nothing -> (instanceLocalVars inst)!var
                                                                  ) formula cur nxt
  tmp_cur <- argVarsAnn formula
  tmp_e <- argVarsAnn formula
  tmp_l <- argVarsAnn formula
  loop_exists <- SMT.var
  se <- argVarsAnn spec
  te <- argVarsAnn spec
  start_time <- liftIO getCurrentTime
  conn <- (if bmcConfigInline cfg
           then fmap app . defFunAnn (spec,spec) ()
           else return) (connectionFun spec)
  bmc' cfg sched spec conn formula init_fun step_fun dep_fun tmp_cur tmp_e tmp_l loop_exists se te [] start_time

data BMCState s = BMCState { bmcVars :: GlobalState
                           , bmcTemporals :: TemporalVars (String,String)
                           , bmcL :: SMTExpr Bool
                           , bmcInLoop :: SMTExpr Bool
                           , bmcScheduling :: SchedulingData s
                           }

bmc' :: (Scheduling s,Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ GTLSpec String) => 
        BMCConfig a -> s -> GTLSpec String 
     -> ((GlobalState,GlobalState) -> SMTExpr Bool)
     -> TypedExpr (String,String) 
     -> ((SchedulingData s,GlobalState) -> SMTExpr Bool)
     -> (((SchedulingData s,GlobalState),(SchedulingData s,GlobalState)) -> SMTExpr Bool)
     -> ((GlobalState,TemporalVars (String,String),TemporalVars (String,String)) -> SMTExpr Bool)
     -> TemporalVars (String,String) -> TemporalVars (String,String) -> TemporalVars (String,String)
     -> SMTExpr Bool -> GlobalState -> SchedulingData s -> [BMCState s] -> UTCTime
     -> SMT (Maybe [(Map (String,String) GTLConstant,Bool,String)])
bmc' cfg sched spec conn formula init step deps tmp_cur tmp_e tmp_l loop_exists se te [] start_time = do
  init_st <- argVarsAnn spec
  l <- SMT.var
  inloop <- SMT.var
  comment "Scheduling data"
  sdata <- argVarsAnn spec
  assert $ initializeScheduling sched sdata
  assert $ init (sdata,init_st)
  assert $ conn (init_st,init_st)
  assert $ not' l
  assert $ not' inloop
  tmp_nxt <- argVarsAnn formula
  assert $ deps (init_st,tmp_cur,tmp_nxt)
  assert $ (formulaEnc tmp_cur)!formula
  incPLTLbase loop_exists tmp_cur tmp_e tmp_l
  let hist = [BMCState init_st tmp_cur l inloop sdata]
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
                        then getPath sched hist >>= return.Just
                        else return Nothing)
         else return Nothing
  case res of
    Nothing -> if bmcConfigTerminate cfg (bmcConfigCur cfg)
               then return Nothing
               else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched spec conn formula init step deps tmp_nxt tmp_e tmp_l loop_exists se te hist start_time
    Just path -> return $ Just path
bmc' cfg sched spec conn formula init step deps tmp_cur tmp_e tmp_l loop_exists se te history@(last_state:_) start_time = do
  let sdata = bmcScheduling last_state
      i = length history
  ctime <- liftIO $ getCurrentTime
  if bmcConfigDebug cfg (bmcConfigCur cfg)
    then liftIO $ do
      putStrLn ("Depth: "++show i++" ("++show (ctime `diffUTCTime` start_time)++")")
      hFlush stdout
    else return ()
  cur_state <- argVarsAnn spec
  tmp_nxt <- argVarsAnn formula
  l <- SMT.var
  inloop <- SMT.var
  nsdata <- argVarsAnn spec
  assert $ step ((sdata,bmcVars last_state),(nsdata,cur_state))
  assert $ conn (cur_state,cur_state)

  -- k-invariant case for LoopConstraints:
  assert $ l .=>. (and' [eqSt (bmcVars last_state) se
                        ,eqScheduling sched (bmcScheduling last_state) te])
  assert $ inloop .==. (or' [bmcInLoop last_state,l])
  assert $ (bmcInLoop last_state) .=>. (not' l)
  
  -- k-invariant case for LastStateFormula
  assert $ deps (cur_state,tmp_cur,tmp_nxt)
  mapM_ (\(expr,var) -> assert $ l .=>. (var .==. ((formulaEnc tmp_cur)!expr))
        ) (Map.toList $ formulaEnc tmp_l)
  
  -- k-invariant case for IncPLTL
  mapM_ (\(expr,var) -> let Just fe = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. or' [(auxFEnc $ bmcTemporals last_state)!expr
                                                 ,and' [inloop,fe]]) (Map.toList $ auxFEnc tmp_cur)
  mapM_ (\(expr,var) -> let Just ge = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. and' [(auxGEnc $ bmcTemporals last_state)!expr
                                                  ,or' [not' $ inloop,ge]]) (Map.toList $ auxGEnc tmp_cur)
  let history' = (BMCState cur_state tmp_cur l inloop nsdata):history
  simple_path <- case bmcConfigCompleteness cfg (bmcConfigCur cfg) of
    False -> return True
    True -> do
      mapM_ (\st -> assert $ or' [not' $ eqSt (bmcVars last_state) (bmcVars st)
                                 ,not' $ (bmcInLoop last_state) .==. (bmcInLoop st)
                                 ,not' $ ((formulaEnc (bmcTemporals last_state))!formula)
                                  .==. ((formulaEnc (bmcTemporals st))!formula)
                                 ,and' [bmcInLoop last_state
                                       ,bmcInLoop st
                                       ,or' [not' $ ((formulaEnc (bmcTemporals last_state))!formula) 
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
                          r <- checkSat
                          if r then getPath sched history' >>= return.Just
                               else return Nothing)
                  else return Nothing
           case res of  
             Just path -> return $ Just path
             Nothing -> if bmcConfigTerminate cfg (bmcConfigCur cfg)
                        then return Nothing
                        else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched spec conn formula init step deps tmp_nxt tmp_e tmp_l loop_exists se te history' start_time)

  
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
getPath :: Scheduling s => s -> [BMCState s] -> SMT [(Map (String,String) GTLConstant,Bool,String)]
getPath sched = mapM (\st -> do
                         vars <- getVarValues $ bmcVars st
                         loop <- SMT.getValue $ bmcL st
                         inf <- showSchedulingInformation sched $ bmcScheduling st
                         return (vars,loop,inf)
                     ) . Prelude.reverse

-- | Extract the values for all variables in the state once the SMT solver has produced a model
getVarValues :: GlobalState -> SMT (Map (String,String) GTLConstant)
getVarValues st = do
  lst <- mapM (\(iname,inst) -> mapM (\(vname,var) -> do
                                         c <- getGTLValue var
                                         return ((iname,vname),c)) (Map.toList $ Map.unions [instanceInputVars inst,instanceOutputVars inst,instanceLocalVars inst])) (Map.toList $ instanceStates st)
  return $ Map.fromList (Prelude.concat lst)

-- | Once the SMT solver has produced a model, extract the value of a given GTL variable from it
getGTLValue :: GTLSMTExpr -> SMT GTLConstant
getGTLValue (GSMTInt v) = do
  r <- SMT.getValue v
  return $ Fix $ GTLIntVal (fromIntegral r)
getGTLValue (GSMTByte v) = do
  r <- SMT.getValue v
  return $ Fix $ GTLByteVal (fromIntegral r)
getGTLValue (GSMTBool v) = do
  r <- SMT.getValue v
  return $ Fix $ GTLBoolVal r
getGTLValue (GSMTEnum v) = do
  r <- SMT.getValue v
  return $ Fix $ toGTL (r::EnumVal)
getGTLValue (GSMTArray vs) = do
  rv <- mapM getGTLValue vs
  return $ Fix $ GTLArrayVal rv
getGTLValue (GSMTTuple vs) = do
  rv <- mapM getGTLValue vs
  return $ Fix $ GTLTupleVal rv

-- | Display an extracted path to the user
renderPath :: [(Map (String,String) GTLConstant,Bool,String)] -> String
renderPath = unlines . concat . renderPath' 1 Map.empty
  where
    renderPath' _ _ [] = []
    renderPath' n prev ((mp,loop,sched):xs)
      = (("Step "++show n
          ++(if loop
             then " (loop starts here) "
             else " ")
          ++sched):[ "| "++iname++"."++var++" = "++show c
                   | ((iname,var),c) <- Map.toList $ Map.differenceWith (\cur last -> if cur==last
                                                                                      then Nothing
                                                                                      else Just cur) mp prev ]
        ):renderPath' (n+1) mp xs

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

verifyModelBMC :: Options -> GTLSpec String -> IO ()
verifyModelBMC opts spec = do
  let solve = case smtBinary opts of
        Nothing -> withZ3
        Just x -> withSMTSolver x
  res <- solve $ bmc ((if useSonolar opts then sonolarConfig
                       else normalConfig) (bmcBound opts) (bmcCompleteness opts)) SimpleScheduling spec
  case res of
    Nothing -> putStrLn "No errors found in model"
    Just path -> putStrLn $ renderPath path

-- | Apply limits to all integers used to store the current state of a component. Used to strengthen k-induction.
limitPCs :: Map String (BA [TypedExpr String] Integer) -> GlobalState -> SMTExpr Bool
limitPCs bas st = and' $ concat
                  [ [(instancePC inst) .>=. 0
                    ,(instancePC inst) .<. (SMT.constant (fromIntegral sz))]
                  | (name,inst) <- Map.toList (instanceStates st), let sz = Map.size $ baTransitions $ bas!name ]

-- | Perform k-induction by providing a solver and a GTL specification.
kInduction :: (Scheduling s,Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ GTLSpec String) 
              => s -> (SMT () -> IO ()) -> GTLSpec String -> IO (Maybe [Map (String,String) GTLConstant])
kInduction sched solver spec = do
  let enums = enumMap spec
      bas = fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               formula = List.foldl1 gand $ fmap gtlContractFormula $ (gtlInstanceContract inst)++(gtlModelContract mdl)
                           in gtl2ba (Just (gtlModelCycleTime mdl)) formula) (gtlSpecInstances spec)
      Fix (Typed _ (UnBoolExpr Always formula)) = gtlSpecVerify spec
      (init,step) = schedule sched (Map.keysSet enums) spec
  baseCaseOrders <- newChan
  indCaseOrders <- newChan
  baseCaseResults <- newChan
  indCaseResults <- newChan
  baseCase <- forkIO $ solver $ do
                                 init_fun <- defFunAnn (spec,spec) () $ \(sdata,st) -> init sdata st
                                 step_fun <- defFunAnn ((spec,spec),(spec,spec)) () $ \((sdata1,st1),(sdata2,st2)) -> step sdata1 sdata2 st1 st2
                                 conn <- defFunAnn (spec,spec) () (connectionFun spec)
                                 sched_data <- argVarsAnn spec
                                 start <- argVarsAnn spec
                                 assert $ init_fun `app` (sched_data,start)
                                 kInductionBase baseCaseOrders baseCaseResults (encodeProperty formula) enums spec conn step_fun sched sched_data [] start 1
  indCase <- forkIO $ solver $ do
               step_fun <- defFunAnn ((spec,spec),(spec,spec)) () $ \((sdata1,st1),(sdata2,st2)) -> step sdata1 sdata2 st1 st2
               conn <- defFunAnn (spec,spec) () (connectionFun spec)
               sched_data <- argVarsAnn spec
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

kInductionBase :: (Scheduling s,Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ GTLSpec String) 
                  => Chan Bool -> Chan (Maybe [Map (String,String) GTLConstant])
                  -> (GlobalState -> SMTExpr Bool)
                  -> Map [String] Integer -> GTLSpec String 
                  -> SMTExpr (SMTFun (GlobalState,GlobalState) Bool)
                  -> SMTExpr (SMTFun ((SchedulingData s,GlobalState),(SchedulingData s,GlobalState)) Bool)
                  -> s -> SchedulingData s
                  -> [GlobalState] -> GlobalState -> Integer -> SMT ()
kInductionBase orders results prop enums spec conn step sched sched_data all last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ conn `app` (last,last)
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
                 assert $ step `app` ((sched_data,last),(sched_data,next))
                 kInductionBase orders results prop enums spec conn step sched sched_data (last:all) next (n+1)
         )
    else return ()

kInductionInd :: (Scheduling s,Args (SchedulingData s),ArgAnnotation (SchedulingData s) ~ GTLSpec String) 
                 => Chan Bool -> Chan Bool
                 -> (GlobalState -> SMTExpr Bool)
                 -> Map [String] Integer -> GTLSpec String
                 -> Map String (BA [TypedExpr String] Integer)
                 -> SMTExpr (SMTFun (GlobalState,GlobalState) Bool)
                 -> SMTExpr (SMTFun ((SchedulingData s,GlobalState),(SchedulingData s,GlobalState)) Bool)
                 -> s -> SchedulingData s
                 -> GlobalState -> Integer -> SMT ()
kInductionInd orders results prop enums spec bas conn step sched sched_data last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ conn `app` (last,last)
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
                             assert $ step `app` ((sched_data,last),(sched_data,next))
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
  res <- kInduction SimpleScheduling solve spec
  case res of
    Nothing -> putStrLn "No errors found in model"
    Just path -> putStrLn $ renderPath [ (st,False,"") | st <- path ]
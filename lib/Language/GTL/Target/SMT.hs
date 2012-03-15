{-# LANGUAGE RankNTypes,DeriveDataTypeable,ExistentialQuantification,TypeFamilies,CPP,FlexibleContexts #-}
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
import Data.Map as Map
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
import qualified Data.Bitstream as BitS

#ifdef SMTExts
type GTLSMTPc = Integer
type GTLSMTInt = Integer
#else
type GTLSMTPc = Word64
type GTLSMTInt = Word64
#endif

-- | An untyped SMT expression
data USMTExpr = forall a. (SMTType a,Typeable a,ToGTL a,SMTValue a,Eq a) => USMTExpr (SMTExpr a) deriving Typeable

instance Show USMTExpr where
  show (USMTExpr e) = show e

instance Eq USMTExpr where
  (==) (USMTExpr l) (USMTExpr r) = case cast r of
                                     Nothing -> False
                                     Just r' -> l == r'

instance Args USMTExpr where
  type Unpacked USMTExpr = ()
  type ArgAnnotation USMTExpr = ()
  foldExprs f s (USMTExpr x) _ = let (s',e') = f s x (extractAnnotation x)
                                 in (s',USMTExpr e')

-- | Safely cast an untyped SMT expression into a typed one
castUSMT :: Typeable a => USMTExpr -> Maybe (SMTExpr a)
castUSMT (USMTExpr x) = gcast x

-- | Unsafely cast an untyped SMT expression.
--   Throws an error if it fails.
castUSMT' :: Typeable a => USMTExpr -> SMTExpr a
castUSMT' e = case castUSMT e of
  Nothing -> let res = error $ "Internal type-error in SMT target: Expected "++(show $ typeOf $ getUndef res)++", but got "++(show (typeOfUSMT e))
             in res
  Just e' -> e'

-- | Gets the type representation for the return type of the untyped SMT expression.
typeOfUSMT :: USMTExpr -> TypeRep
typeOfUSMT (USMTExpr e) = typeOf (getUndef e)

-- | Given a function which accepts a typed SMT expression of any type, applies that function to the untyped SMT expression.
useUSMT :: (forall a. (SMTType a,Typeable a,ToGTL a,SMTValue a) => SMTExpr a -> b) -> USMTExpr -> b
useUSMT f (USMTExpr x) = f x

-- | Saves the variables of all components in the GALS system
data GlobalState = GlobalState
                   { instanceStates :: Map String InstanceState
                   } deriving (Eq,Typeable)

instance Args GlobalState where
  type Unpacked GlobalState = ()
  type ArgAnnotation GlobalState = ()
  foldExprs f s gl _ = let (s',sts') = List.mapAccumL (\cs (name,is) -> let (cs',is') = foldExprs f cs is ()
                                                                        in (cs',(name,is'))) s (Map.toAscList (instanceStates gl))
                       in (s',GlobalState { instanceStates = Map.fromAscList sts' })

-- | Saves the variables of one instance (including the state variable of the state machine)
data InstanceState = InstanceState
                     { instanceVars :: Map String (UnrolledVar,GTLType,VarUsage)
                     , instancePC :: SMTExpr GTLSMTPc -- ^ Saves the state of the state machine
                     } deriving (Eq,Typeable)

instance Args InstanceState where
  type Unpacked InstanceState = ()
  type ArgAnnotation InstanceState = ()
  foldExprs f s is _ = let (s1,iv') = List.mapAccumL (\cs (name,(var,tp,usage)) -> let (cs',var') = foldExprs f cs var ()
                                                                                   in (cs',(name,(var',tp,usage)))
                                                     ) s (Map.toAscList (instanceVars is))
                           (s2,ipc') = f s1 (instancePC is) ()
                       in (s2,InstanceState { instanceVars = Map.fromAscList iv'
                                            , instancePC = ipc' })

-- | A GTL variable which is (possibly) composed from more than one SMT variable
data UnrolledVar = BasicVar USMTExpr -- ^ Just a simple SMT variable
                 | IndexedVar [UnrolledVar] -- ^ A composed variable
                 deriving (Show,Eq,Typeable)

instance Args UnrolledVar where
    type Unpacked UnrolledVar = ()
    type ArgAnnotation UnrolledVar = ()
    foldExprs f s (BasicVar var) _ = let (s',var') = foldExprs f s var ()
                                     in (s',BasicVar var')
    foldExprs f s (IndexedVar xs) _ = let (s',xs') = List.mapAccumL (\s x -> foldExprs f s x ()) s xs
                                      in (s',IndexedVar xs')

-- | Saves the variables needed for the encoding of LTL properties
data TemporalVars v = TemporalVars { formulaEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxFEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxGEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   }

-- | Create a new named unrolled variable of a given type.
newUnrolledVar :: Map [String] Integer -> GTLType -> String -> SMT UnrolledVar
newUnrolledVar enums (Fix tp) base = case tp of
  GTLArray sz tp -> do
    arr <- mapM (\i -> newUnrolledVar enums tp (base++"_"++show i)) [0..(sz-1)]
    return $ IndexedVar arr
  GTLTuple tps -> do
    arr <- mapM (\(tp,i) -> newUnrolledVar enums tp (base++"_"++show i)) (zip tps [0..])
    return $ IndexedVar arr
  GTLNamed _ tp' -> newUnrolledVar enums tp' base
  GTLEnum vals -> do
    v <- SMT.varNamedAnn (T.pack base) (vals,enums!vals)
    return $ BasicVar $ USMTExpr $ assertEq (undefined::EnumVal) v
  _ -> getUndefined enums (Fix tp) $ \u -> do
    v <- SMT.varNamed (T.pack base)
    return $ BasicVar $ USMTExpr $ assertEq u v

-- | Creates an anonymous existential unrolled variable
existsUnrolledVar :: Map [String] Integer -> GTLType -> (UnrolledVar -> SMTExpr Bool) -> SMTExpr Bool
existsUnrolledVar enums (Fix tp) f = case tp of
  GTLArray sz tp -> genExists sz []
    where
      genExists 0 ys = f (IndexedVar $ Prelude.reverse ys)
      genExists n ys = existsUnrolledVar enums tp (\v -> genExists (n-1) (v:ys))
  GTLTuple tps -> genExists tps []
    where
      genExists [] ys = f (IndexedVar $ Prelude.reverse ys)
      genExists (tp:tps) ys = existsUnrolledVar enums tp (\v -> genExists tps (v:ys))
  _ -> getUndefined enums (Fix tp) $ \u ->
    exists $ \v -> f (BasicVar $ USMTExpr $ assertEq u v)

-- | Creates an SMT expression which states that two GTL variables are to be equal
eqUnrolled :: UnrolledVar -> UnrolledVar -> SMTExpr Bool
eqUnrolled (BasicVar x) (BasicVar y) = useUSMT (\ex -> ex .==. (castUSMT' y)) x
eqUnrolled (IndexedVar x) (IndexedVar y) = and' (Prelude.zipWith eqUnrolled x y)

-- | Print a global variable mapping for debugging
debugState :: GlobalState -> String
debugState st = Prelude.unlines [ Prelude.unlines (iname:[ "|-"++vname++": "++debugVar var  | (vname,(var,tp,_)) <- Map.toList (instanceVars inst) ])
                                | (iname,inst) <- Map.toList (instanceStates st) ]

debugVar :: UnrolledVar -> String
debugVar (BasicVar v) = useUSMT (\v' -> show v') v
debugVar (IndexedVar vs) = "[" ++ Prelude.concat (intersperse "," $ fmap debugVar vs) ++ "]"

debugTemporalVars :: TemporalVars (String,String) -> String
debugTemporalVars tmp
  = Prelude.unlines $ [ "["++show expr++"] = "++show var | (expr,var) <- Map.toList (formulaEnc tmp) ]
    ++ [ "<F "++show expr++"> = "++show var | (expr,var) <- Map.toList (auxFEnc tmp) ]
    ++ [ "<G "++show expr++"> = "++show var | (expr,var) <- Map.toList (auxGEnc tmp) ]

-- | Create an unrestricted, global state with a given name
newState :: Map [String] Integer -> GTLSpec String -> String -> SMT GlobalState
newState enums spec n = do
  mp <- mapM (\(iname,inst) -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               in do
                                 is <- newInstanceState enums iname mdl n
                                 return (iname,is)
             ) (Map.toAscList $ gtlSpecInstances spec)
  return $ GlobalState { instanceStates = Map.fromAscList mp }

-- | Create a new instance state for a named instance
newInstanceState :: Map [String] Integer -> String -> GTLModel String -> String -> SMT InstanceState
newInstanceState enums iname mdl n = do
  mp_inp <- mapM (\(name,tp) -> do
                     var <- newUnrolledVar enums tp ("v"++n++"_"++iname++"_"++name)
                     return (name,(var,tp,Input))) $
            Map.toAscList $ gtlModelInput mdl
  mp_outp <- mapM (\(name,tp) -> do
                      var <- newUnrolledVar enums tp ("v"++n++"_"++iname++"_"++name)
                      return (name,(var,tp,Output))) $
             Map.toAscList $ gtlModelOutput mdl
  mp_loc <- mapM (\(name,tp) -> do
                     var <- newUnrolledVar enums tp ("v"++n++"_"++iname++"_"++name)
                     return (name,(var,tp,StateOut))) $
            Map.toAscList $ gtlModelLocals mdl
  pc <- SMT.varNamed $ T.pack $ "pc"++n++"_"++iname
  return $ InstanceState (Map.unions [Map.fromAscList mp_inp,Map.fromAscList mp_outp,Map.fromAscList mp_loc]) pc

-- | Assert that two instance states are equal
eqInst :: InstanceState -> InstanceState -> SMTExpr Bool
eqInst st1 st2 = and' ((instancePC st1 .==. instancePC st2):
                       (Map.elems $ Map.intersectionWith (\(v1,_,_) (v2,_,_) -> eqUnrolled v1 v2) (instanceVars st1) (instanceVars st2)))

-- | Asserts that two instance states are equal in their output and state variables.
eqInstOutp :: InstanceState -> InstanceState -> SMTExpr Bool
eqInstOutp st1 st2 
  = and' ((instancePC st1 .==. instancePC st2):
          (Map.elems $ Map.intersectionWith (\(v1,_,u) (v2,_,_)
                                             -> case u of
                                               Input -> SMT.constant True
                                               _ -> eqUnrolled v1 v2) (instanceVars st1) (instanceVars st2)))

-- | Asserts that two global states are equal.
eqSt :: GlobalState -> GlobalState -> SMTExpr Bool
eqSt st1 st2 = and' $ Map.elems $ Map.intersectionWith eqInst (instanceStates st1) (instanceStates st2)

-- | Existentially quantifies a global state
existsState :: Map [String] Integer -> GTLSpec String -> (GlobalState -> SMTExpr Bool) -> SMTExpr Bool
existsState enums spec f = genExists (Map.toDescList $ gtlSpecInstances spec) []
  where
    genExists [] ys = f (GlobalState { instanceStates = Map.fromAscList ys })
    genExists ((i,inst):xs) ys = existsInstanceState enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) $ \is -> genExists xs ((i,is):ys)

-- | Existentially quantifies an instance state
existsInstanceState :: Map [String] Integer -> GTLModel String -> (InstanceState -> SMTExpr Bool) -> SMTExpr Bool
existsInstanceState enums mdl f = genExists (Map.toDescList $ Map.unions 
                                             [fmap (\x -> (x,Input)) $ gtlModelInput mdl
                                             ,fmap (\x -> (x,Output)) $ gtlModelOutput mdl
                                             ,fmap (\x -> (x,StateOut)) $ gtlModelLocals mdl]) []
  where
    genExists [] ys = exists $ \pc -> f (InstanceState (Map.fromAscList ys) pc)
    genExists ((vn,(vt,vu)):xs) ys = existsUnrolledVar enums vt $ \v -> genExists xs ((vn,(v,vt,vu)):ys)

-- | Use a list of indices to navigate a GTL variable
indexUnrolled :: UnrolledVar -> [Integer] -> UnrolledVar
indexUnrolled v [] = v
indexUnrolled (IndexedVar vs) (i:is) = indexUnrolled (vs `genericIndex` i) is

-- | Extract a variable from a global state
getVar :: String -- ^ Name of the instance
          -> String -- ^ Name of the variable
          -> [Integer] -- ^ (possible empty) list of indices
          -> GlobalState -- ^ State from which to extract
          -> UnrolledVar
getVar inst name idx st = let (v,vt,vu) = (instanceVars $ (instanceStates st)!inst)!name
                          in indexUnrolled v idx

-- | Assert the declared connections from a GTL specification in the SMT model
connections :: [(GTLConnectionPoint String,GTLConnectionPoint String)] -> GlobalState -> GlobalState -> SMTExpr Bool
connections conns stf stt
  = and' [ eqUnrolled (getVar f fv fi stf) (getVar t tv ti stt)
         | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- conns
         ]

-- | A scheduling dictates which instance may perform a calculation step at which point in time.
class Scheduling s where
  -- | A scheduling may define extra data it needs to perform the scheduling
  type SchedulingData s
  -- | Allocate the needed data for the scheduling
  createSchedulingData :: s -- ^ The scheduling
                          -> Set String -- ^ The names of all components
                          -> SMT (SchedulingData s)
  initializeScheduling :: s -> SchedulingData s -> SMTExpr Bool
  -- | Perform scheduling on two global states: The current one and the next one
  schedule :: s
              -> Map String (BA [TypedExpr String] Integer) -- ^ The buchi automatons for all components
              -> SchedulingData s -- ^ The current scheduling data
              -> SchedulingData s -- ^ The next scheduling data
              -> GlobalState -- ^ The current state
              -> GlobalState -- ^ The next state
              -> SMTExpr Bool
  showSchedulingInformation :: s -> SchedulingData s -> SMT String
  eqScheduling :: s -> SchedulingData s -> SchedulingData s -> SMTExpr Bool

data SimpleScheduling = SimpleScheduling

instance Scheduling SimpleScheduling where
  type SchedulingData SimpleScheduling = ()
  createSchedulingData _ _ = return ()
  initializeScheduling _ _ = SMT.constant True
  schedule _ mp _ _ stf stt = or' [ and' ((stepInstance ba ((instanceStates stf)!iname) ((instanceStates stt)!iname))
                                          :[ eqInstOutp inst ((instanceStates stt)!iname')
                                           | (iname',inst) <- Map.toList (instanceStates stf)
                                           , iname /= iname'
                                           ])
                                  | (iname,ba) <- Map.toList mp
                                  ]
  showSchedulingInformation _ _ = return "none"
  eqScheduling _ _ _ = SMT.constant True

data FairScheduling = FairScheduling

instance Scheduling FairScheduling where
  type SchedulingData FairScheduling = Map String (SMTExpr Bool)
  createSchedulingData _ ps = fmap Map.fromList $ 
                              mapM (\p -> do
                                       v <- SMT.var
                                       return (p,v)) (Set.toList ps)
  initializeScheduling _ mp = and' (fmap not' $ Map.elems mp)
  schedule _ mp ps ps' stf stt = let smap = Map.intersectionWithKey (\name p1 p2 -> (p1,p2,and' $ (stepInstance (mp!name) ((instanceStates stf)!name) ((instanceStates stt)!name))
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
  showSchedulingInformation _ mp = do
    mp' <- mapM (\(name,x) -> do
                    vx <- SMT.getValue x
                    return $ name ++ ":" ++ (if vx then "1" else "0")
                ) (Map.toList mp)
    return $ show mp'
  eqScheduling _ p1 p2 = and' $ Map.elems $ Map.intersectionWith (.==.) p1 p2

-- | Perform a step in which each component performs a calculation step at the same time.
step :: Map String (BA [TypedExpr String] Integer) -> GlobalState -> GlobalState -> SMTExpr Bool
step bas stf stt 
  = and' [ stepInstance ba ((instanceStates stf)!name) ((instanceStates stt)!name)
         | (name,ba) <- Map.toList bas ]

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

-- | Perform a calculation step in a single component
stepInstance :: BA [TypedExpr String] Integer -> InstanceState -> InstanceState -> SMTExpr Bool
stepInstance ba stf stt
  = and' [ (instancePC stf .==. SMT.constant (fromIntegral st)) .=>. 
           or' [ and' ((instancePC stt .==. SMT.constant (fromIntegral trg)):
                       [let BasicVar v = translateExpr (\v u i -> case u of
                                                           Input -> fst3 $ (instanceVars stf)!v
                                                           StateIn -> fst3 $ (instanceVars stf)!v
                                                           Output -> fst3 $ (instanceVars stt)!v
                                                           StateOut -> fst3 $ (instanceVars stt)!v) c
                        in castUSMT' v
                       | c <- cond ])
               | (cond,trg) <- trans
               ]
         | (st,trans) <- Map.toList (baTransitions ba) ]

-- | Translate a GTL expression into a SMT expression
translateExpr :: (v -> VarUsage -> Integer -> UnrolledVar) ->  TypedExpr v -> UnrolledVar
translateExpr f (Fix expr)
  = case GTL.getValue expr of
    GTL.Var n i u -> f n u i
    GTL.Value val -> case val of
      GTLIntVal i -> BasicVar $ USMTExpr $ SMT.constant (fromIntegral i :: Word64)
      GTLByteVal w -> BasicVar $ USMTExpr $ SMT.constant w
      GTLBoolVal b -> BasicVar $ USMTExpr $ SMT.constant b
      GTLEnumVal v -> let Fix (GTLEnum vals) = GTL.getType expr
                          Just i = List.findIndex (==v) vals
                      in BasicVar $ USMTExpr $ SMT.constantAnn (EnumVal v) (vals,fromIntegral i)
      GTLArrayVal vs -> IndexedVar $ fmap (translateExpr f) vs
      GTLTupleVal vs -> IndexedVar $ fmap (translateExpr f) vs
    GTL.BinRelExpr rel l r
      | isNumeric (getType $ unfix l) -> getUndefinedNumeric (getType $ unfix l)
                                         $ \u -> BasicVar $ USMTExpr $ (case rel of
                                                                           BinLT -> BVULT
                                                                           BinLTEq -> BVULE
                                                                           BinGT -> BVUGT
                                                                           BinGTEq -> BVUGE
                                                                           BinEq -> Eq
                                                                           BinNEq -> \x y -> SMT.Not (Eq x y))
                                                 (let BasicVar lll = ll in assertEq u $ castUSMT' lll)
                                                 (let BasicVar rrr = rr in assertEq u $ castUSMT' rrr)
      | otherwise -> case rel of
        BinEq -> BasicVar $ USMTExpr $ eqUnrolled ll rr
        BinNEq -> BasicVar $ USMTExpr $ not' $ eqUnrolled ll rr
      where
        ll = translateExpr f l
        rr = translateExpr f r
    GTL.BinIntExpr op l r
      | getType (unfix l) == gtlInt -> BasicVar $ USMTExpr $ (case op of
                                                                 OpPlus -> BVAdd
                                                                 OpMinus -> BVSub
                                                                 OpMult -> BVMul
                                                                 --OpDiv -> Div
                                                             )
                                       (let BasicVar lll = ll in castUSMT' lll :: SMTExpr Word64)
                                       (let BasicVar rrr = rr in castUSMT' rrr)
      where
        ll = translateExpr f l
        rr = translateExpr f r
    GTL.IndexExpr expr' idx -> let IndexedVar vars = translateExpr f expr'
                               in genericIndex vars idx
    GTL.BinBoolExpr op l r -> BasicVar $ USMTExpr (case op of
                                                      GTL.And -> and' [lll,rrr]
                                                      GTL.Or -> or' [lll,rrr]
                                                      GTL.Implies -> lll .=>. rrr
                                                  )
      where
        BasicVar ll = translateExpr f l
        BasicVar rr = translateExpr f r
        lll = castUSMT' ll
        rrr = castUSMT' rr
    GTL.UnBoolExpr GTL.Not arg -> let BasicVar ll = translateExpr f arg
                                  in BasicVar $ USMTExpr $ not' $ castUSMT' ll
    _ -> error $ "Implement translateExpr for " ++ showTermWith (\_ _ -> showString "_") (\_ _ -> showString "_") 0 (GTL.getValue expr) ""

-- | Assert that an instance state is an initial state
initInstance :: Map [String] Integer -> GTLModel String -> BA [TypedExpr String] Integer -> InstanceState -> SMTExpr Bool
initInstance enums mdl ba inst
  = and' $ (or' [ (instancePC inst) .==. SMT.constant (fromIntegral f)
                | f <- Set.toList (baInits ba) ]):
    [ eqUnrolled
      (fst3 $ (instanceVars inst)!var)
      (translateExpr (\v _ _ -> fst3 $ (instanceVars inst)!v) (constantToExpr (Map.keysSet enums) def))
    | (var,Just def) <- Map.toList $ gtlModelDefaults mdl ]

-- | Assert that a global state is a combination of all initial component state
initState :: Map [String] Integer -> GTLSpec String -> Map String (BA [TypedExpr String] Integer) -> GlobalState -> SMTExpr Bool
initState enums spec bas st
  = and' [ initInstance enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) (bas!name) ((instanceStates st)!name)
         | (name,inst) <- Map.toList (gtlSpecInstances spec)
         ]

-- | Get the internal variable name for a GTL expression
typedExprVarName :: TypedExpr (String,String) -> String
typedExprVarName expr = case GTL.getValue (unfix expr) of
  GTL.Var (iname,name) h u -> iname++"_"++name
  GTL.BinRelExpr rel lhs rhs -> (case rel of
                                    BinLT -> "LT"
                                    BinLTEq -> "LTE"
                                    BinGT -> "GT"
                                    BinGTEq -> "GTE"
                                    BinEq -> "EQ"
                                    BinNEq -> "NEQ") ++ "_"++typedExprVarName lhs++"_"++typedExprVarName rhs
  GTL.Value (GTLIntVal v) -> show v
  GTL.Value (GTLBoolVal b) -> if b then "T" else "F"
  GTL.Value (GTLEnumVal v) -> "ENUM"++v
  GTL.UnBoolExpr op e' -> (case op of
                              GTL.Not -> "NOT"
                              Always -> "G"
                              Next _ -> "NEXT"
                              Finally _ -> "F")++"_"++typedExprVarName e'
  GTL.BinBoolExpr op lhs rhs -> (case op of
                                    GTL.And -> "AND"
                                    GTL.Or -> "OR"
                                    GTL.Implies -> "IMPL"
                                    GTL.Until _ -> "U"
                                    GTL.UntilOp _ -> "R")++"_"++typedExprVarName lhs++"_"++typedExprVarName rhs
  _ -> error $ "Please implement typedExprVarName for "++show expr
                                    
-- | Create new temporal variables to encode a piece of a LTL formula
newTemporalVars :: String -> TypedExpr (String,String) -> SMT (TemporalVars (String,String))
newTemporalVars n expr = newTemporalVars' n expr (TemporalVars Map.empty Map.empty Map.empty)

newTemporalVars' :: String -> TypedExpr (String,String) -> TemporalVars (String,String) -> SMT (TemporalVars (String,String))
newTemporalVars' n expr p
  | Map.member expr (formulaEnc p) = return p
  | otherwise = case GTL.getValue (unfix expr) of
    GTL.Var name h u -> do
      v <- mkvar
      return $ p { formulaEnc = Map.insert expr v (formulaEnc p) }
    GTL.BinRelExpr _ _ _ -> do
      v <- mkvar
      return $ p { formulaEnc = Map.insert expr v (formulaEnc p) }
    GTL.BinBoolExpr op lhs rhs -> do
      p1 <- newTemporalVars' n lhs p
      p2 <- newTemporalVars' n rhs p1
      v <- mkvar
      let p3 = p2 { formulaEnc = Map.insert expr v (formulaEnc p2) }
      case op of
        GTL.Until NoTime
          | Map.member rhs (auxFEnc p3) -> return p3
          | otherwise -> do
            v2 <- SMT.varNamed $ T.pack $ "faux"++n++"_"++typedExprVarName rhs
            return $ p3 { auxFEnc = Map.insert rhs v2 (auxFEnc p3) }
        GTL.UntilOp NoTime
          | Map.member rhs (auxGEnc p3) -> return p3
          | otherwise -> do
            v2 <- SMT.varNamed $ T.pack $ "gaux"++n++"_"++typedExprVarName rhs
            return $ p3 { auxGEnc = Map.insert rhs v2 (auxGEnc p3) }
        _ -> return p3
    GTL.UnBoolExpr op arg -> do
      p1 <- newTemporalVars' n arg p
      case op of
        GTL.Not -> return $ p1 { formulaEnc = Map.insert expr (not' ((formulaEnc p1)!arg)) (formulaEnc p1) }
        GTL.Always -> do
          v1 <- mkvar
          aux' <- if Map.member arg (auxGEnc p1)
                  then return (auxGEnc p1)
                  else (do
                           v2 <- SMT.varNamed $ T.pack $ "gaux"++n++"_"++typedExprVarName arg
                           return $ Map.insert arg v2 (auxGEnc p1))
          return $ p1 { formulaEnc = Map.insert expr v1 (formulaEnc p1)
                      , auxGEnc = aux' }
        GTL.Finally NoTime -> do
          v1 <- mkvar
          aux' <- if Map.member arg (auxFEnc p1)
                  then return (auxFEnc p1)
                  else (do
                           v2 <- SMT.varNamed $ T.pack $ "faux"++n++"_"++typedExprVarName arg
                           return $ Map.insert arg v2 (auxFEnc p1))
          return $ p1 { formulaEnc = Map.insert expr v1 (formulaEnc p1)
                      , auxFEnc = aux' }
    _ -> return p
    where
      mkvar = SMT.varNamed $ T.pack $ "fe"++n++"_"++typedExprVarName expr

-- | Create dependencies between the temporal variables of a previous and the current state
dependencies :: Ord v => (v -> VarUsage -> Integer -> UnrolledVar) -> TypedExpr v -> TemporalVars v -> TemporalVars v -> SMT (SMTExpr Bool)
dependencies f expr cur nxt = case GTL.getValue (unfix expr) of
  GTL.Var v h u -> do
    let BasicVar var = f v u h
    assert $ self .==. castUSMT' var
    return self
  GTL.UnBoolExpr GTL.Not (Fix (Typed _ (GTL.Var v h u))) -> do
    let BasicVar var = f v u h
    assert $ self .==. not' (castUSMT' var)
    return self
  GTL.Value (GTLBoolVal x) -> return $ SMT.constant x
  GTL.BinBoolExpr op lhs rhs -> do
    l <- dependencies f lhs cur nxt
    r <- dependencies f rhs cur nxt
    case op of
      GTL.And -> assert $ self .==. and' [l,r]
      GTL.Or -> assert $ self .==. or' [l,r]
      GTL.Until NoTime -> assert $ self .==. or' [r,and' [l,nself]]
      GTL.UntilOp NoTime -> assert $ self .==. and' [r,or' [l,nself]]
    return self
  GTL.UnBoolExpr op e -> do
    e' <- dependencies f e cur nxt
    case op of
      GTL.Always -> assert $ self .==. and' [e',nself]
      GTL.Finally NoTime -> assert $ self .==. or' [e',nself]
      _ -> return ()
    return self
  GTL.BinRelExpr _ _ _ -> do
    let BasicVar v = translateExpr f expr
    assert $ self .==. castUSMT' v
    return self
  _ -> return self
  where
    self = (formulaEnc cur)!expr
    nself = (formulaEnc nxt)!expr

-- | Perform bounded model checking of a given GTL specification
bmc :: Scheduling s => BMCConfig a -> s -> GTLSpec String -> SMT (Maybe [(Map (String,String) GTLConstant,Bool,String)])
bmc cfg sched spec = do
#ifndef SMTExts  
  setLogic $ T.pack "QF_ABV"
#endif
  setOption $ PrintSuccess False
  setOption $ ProduceModels True
  let enums = enumMap spec
      bas = fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               formula = List.foldl1 gand (case gtlInstanceContract inst of
                                                              Nothing -> gtlModelContract mdl
                                                              Just con -> con:(gtlModelContract mdl)
                                                          )
                           in gtl2ba (Just (gtlModelCycleTime mdl)) formula) (gtlSpecInstances spec)
      formula = GTL.distributeNot (gtlSpecVerify spec)
  tmp_cur <- newTemporalVars "0" formula
  tmp_e <- newTemporalVars "e" formula
  tmp_l <- newTemporalVars "l" formula
  loop_exists <- SMT.varNamed $ T.pack $ "loop_exists"
  se <- newState enums spec "e"
  te <- createSchedulingData sched (Map.keysSet $ gtlSpecInstances spec)
  start_time <- liftIO getCurrentTime
  bmc' cfg sched enums spec formula bas tmp_cur tmp_e tmp_l loop_exists se te [] start_time

data BMCState s = BMCState { bmcVars :: GlobalState
                           , bmcTemporals :: TemporalVars (String,String)
                           , bmcL :: SMTExpr Bool
                           , bmcInLoop :: SMTExpr Bool
                           , bmcScheduling :: SchedulingData s
                           }

-- | Once the SMT solver has produced a model, extract the value of a given GTL variable from it
getGTLValue :: GTLType -> UnrolledVar -> SMT GTLConstant
getGTLValue (Fix (GTLEnum es)) (BasicVar v) = do
  r <- SMT.getValue (castUSMT' v)
  return $ Fix $ toGTL (r::EnumVal)
getGTLValue _ (BasicVar v) = useUSMT (\rv -> do
                                         r <- SMT.getValue rv
                                         return $ Fix $ toGTL r) v
getGTLValue (Fix (GTLArray _ tp)) (IndexedVar vs)
  = do
  rv <- mapM (getGTLValue tp) vs
  return $ Fix $ GTLArrayVal rv
getGTLValue (Fix (GTLTuple tps)) (IndexedVar vs)
  = do
  rv <- mapM (\(v,tp) -> getGTLValue tp v) (zip vs tps)
  return $ Fix $ GTLTupleVal rv
getGTLValue (Fix (GTLNamed _ tp)) v = getGTLValue tp v
getGTLValue tp v = error $ "Can't match type "++show tp++" with "++show v

-- | Extract the values for all variables in the state once the SMT solver has produced a model
getVarValues :: GlobalState -> SMT (Map (String,String) GTLConstant)
getVarValues st = do
  lst <- mapM (\(iname,inst) -> mapM (\(vname,(var,tp,us)) -> do
                                         c <- getGTLValue tp var
                                         return ((iname,vname),c)) (Map.toList $ instanceVars inst)) (Map.toList $ instanceStates st)
  return $ Map.fromList (Prelude.concat lst)

-- | Extract a whole path from the SMT solver
getPath :: Scheduling s => s -> [BMCState s] -> SMT [(Map (String,String) GTLConstant,Bool,String)]
getPath sched = mapM (\st -> do
                         vars <- getVarValues $ bmcVars st
                         loop <- SMT.getValue $ bmcL st
                         inf <- showSchedulingInformation sched $ bmcScheduling st
                         return (vars,loop,inf)
                     ) . Prelude.reverse

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

data BMCConfig a = BMCConfig { bmcConfigCur :: a
                             , bmcConfigNext :: a -> a
                             , bmcConfigCompleteness :: a -> Bool
                             , bmcConfigCheckSat :: a -> Bool
                             , bmcConfigTerminate :: a -> Bool
                             , bmcConfigDebug :: a -> Bool
                             , bmcConfigUseStacks :: a -> Bool
                             }

stack' :: BMCConfig c -> SMT a -> SMT a
stack' cfg = if bmcConfigUseStacks cfg (bmcConfigCur cfg) then stack else id

bmc' :: Scheduling s => BMCConfig a
        -> s
        -> Map [String] Integer -> GTLSpec String
        -> TypedExpr (String,String)
        -> Map String (BA [TypedExpr String] Integer)
        -> TemporalVars (String,String)
        -> TemporalVars (String,String)
        -> TemporalVars (String,String)
        -> SMTExpr Bool 
        -> GlobalState
        -> SchedulingData s
        -> [BMCState s] 
        -> UTCTime
        -> SMT (Maybe [(Map (String,String) GTLConstant,Bool,String)])
bmc' cfg sched enums spec f bas tmp_cur tmp_e tmp_l loop_exists se te [] start_time = do
  init <- newState enums spec "0"
  l <- SMT.varNamed $ T.pack "l0"
  inloop <- SMT.varNamed $ T.pack "inloop0"
  sdata <- createSchedulingData sched (Map.keysSet bas)
  assert $ initState enums spec bas init
  assert $ connections (gtlSpecConnections spec) init init
  assert $ not' l
  assert $ not' inloop
  assert $ initializeScheduling sched sdata
  tmp_nxt <- newTemporalVars "1" f
  genc <- dependencies (\(iname,var) u h -> getVar iname var [] init) f tmp_cur tmp_nxt
  assert genc
  incPLTLbase loop_exists tmp_cur tmp_e tmp_l
  let hist = [BMCState init tmp_cur l inloop sdata]
  res <- if bmcConfigCheckSat cfg (bmcConfigCur cfg) 
         then stack' cfg (do
                      -- k-variant case for LoopConstraints
                      assert $ eqSt se init
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
               else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched enums spec f bas tmp_nxt tmp_e tmp_l loop_exists se te hist start_time
    Just path -> return $ Just path
bmc' cfg sched enums spec f bas tmp_cur tmp_e tmp_l loop_exists se te history@(last_state:_) start_time = do
  let i = length history
      sdata = bmcScheduling last_state
  ctime <- liftIO $ getCurrentTime
  if bmcConfigDebug cfg (bmcConfigCur cfg)
    then liftIO $ do
      putStrLn ("Depth: "++show i++" ("++show (ctime `diffUTCTime` start_time)++")")
      hFlush stdout
    else return ()
  cur_state <- newState enums spec (show i)
  tmp_nxt <- newTemporalVars (show $ i+1) f
  l <- SMT.varNamed $ T.pack $ "l"++show i
  inloop <- SMT.varNamed $ T.pack $ "inloop"++show i
  --assert $ step bas (bmcVars last_state) cur_state
  nsdata <- createSchedulingData sched (Map.keysSet bas)
  assert $ schedule sched bas sdata nsdata (bmcVars last_state) cur_state
  assert $ connections (gtlSpecConnections spec) cur_state cur_state
  
  -- k-invariant case for LoopConstraints:
  assert $ l .=>. (and' [eqSt (bmcVars last_state) se
                        ,eqScheduling sched (bmcScheduling last_state) te])
  assert $ inloop .==. (or' [bmcInLoop last_state,l])
  assert $ (bmcInLoop last_state) .=>. (not' l)
  
  -- k-invariant case for LastStateFormula
  genc <- dependencies (\(iname,var) u h -> getVar iname var [] cur_state) f tmp_cur tmp_nxt
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
  -- Simple Path restriction
  simple_path <- case bmcConfigCompleteness cfg (bmcConfigCur cfg) of
    False -> return True
    True -> do
      mapM_ (\st -> assert $ or' [not' $ eqSt (bmcVars last_state) (bmcVars st)
                                 ,not' $ (bmcInLoop last_state) .==. (bmcInLoop st)
                                 ,not' $ ((formulaEnc (bmcTemporals last_state))!f)
                                  .==. ((formulaEnc (bmcTemporals st))!f)
                                 ,and' [bmcInLoop last_state
                                       ,bmcInLoop st
                                       ,or' [not' $ ((formulaEnc (bmcTemporals last_state))!f) 
                                             .==. ((formulaEnc (bmcTemporals st))!f)]
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
                          r <- return False --checkSat
                          if r then getPath sched history' >>= return.Just
                               else return Nothing)
                  else return Nothing
           case res of  
             Just path -> return $ Just path
             Nothing -> if bmcConfigTerminate cfg (bmcConfigCur cfg)
                        then return Nothing
                        else bmc' (cfg { bmcConfigCur = bmcConfigNext cfg (bmcConfigCur cfg) }) sched enums spec f bas tmp_nxt tmp_e tmp_l loop_exists se te history' start_time)

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
                }

verifyModelBMC :: Options -> GTLSpec String -> IO ()
verifyModelBMC opts spec = do
  let solve = case smtBinary opts of
        Nothing -> withZ3
        Just x -> withSMTSolver x
  res <- solve $ bmc (sonolarConfig (bmcBound opts) (bmcCompleteness opts)) SimpleScheduling spec
  case res of
    Nothing -> putStrLn "No errors found in model"
    Just path -> putStrLn $ renderPath path


{-
let y3 = l3
    n3 = not l3
    y2 = if l2 then n3 else y3
    n2 = not l2 and n3
    y1 = if l1 then n2 else y2
    n1 = not l1 and n2
    y0 = if l0 then n1 else y1
    n0 = not l0 and n1
 in y0
 -}

-- Encodes the contraint that exactly one of the given expressions must be true
exactlyOne :: [SMTExpr Bool] -> SMTExpr Bool
exactlyOne [] = SMT.constant False
exactlyOne (y:ys) = exactlyOne' y (not' y) ys
  where
    exactlyOne' y n [] = y
    exactlyOne' y n (x:xs) = let' (ite x n y) (\y' -> let' (and' [not' x,n]) (\n' -> exactlyOne' y' n' xs))

-- | Used to represent Enum values. Stores not only the value but also the type and the derived type-number of the enum.
data EnumVal = EnumVal String deriving (Typeable,Eq)

instance ToGTL EnumVal where
  toGTL (EnumVal name) = GTLEnumVal name
  --gtlTypeOf (EnumVal enums _ _) = Fix $ GTLEnum enums

instance SMTType EnumVal where
  type SMTAnnotation EnumVal = ([String],Integer)
#ifdef SMTExts
  getSort _ (_,nr) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType _ (vals,nr) = let decl = declareDatatypes [] [(T.pack $ "Enum"++show nr,[(T.pack val,[]) | val <- vals])]
                            in [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],decl)]
  additionalConstraints _ _ _ = []
#else
  getSort _ (vals,nr) = let bits = ceiling $ logBase 2 $ fromIntegral (List.length vals)
                        in getSort (undefined::BitS.Bitstream BitS.Left) (BitstreamLen $ fromIntegral bits) --L.List [L.Symbol "_",L.Symbol "BitVec",show bits]
  declareType _ (vals,nr) = []
  additionalConstraints _ (enums,nr) var = [BVULE var (SMT.constantAnn (EnumVal $ List.last enums) (enums,nr))]
  {-
  getSort _ (_,nr) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType _ (vals,nr) = let decl = do
                                  let tname = T.pack $ "Enum"++show nr
                                  declareSort tname 0
                                  mapM_ (\val -> declareFun (T.pack val) [] (L.Symbol tname)) vals
                                  assert $ distinct [SMT.Var (T.pack val) (vals,nr) :: SMTExpr EnumVal | val <- vals]
                            in [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],decl)]
  additionalConstraints _ (enums,nr) var = [or' [var .==. (SMT.Var (T.pack val) (enums,nr)) | val <- enums]] -}
#endif

instance SMTValue EnumVal where
#ifdef SMTExts
  mangle (EnumVal v) _ = L.Symbol $ T.pack v
  unmangle (L.Symbol v) (vals,nr) = return $ Just $ EnumVal (T.unpack v)
#else
  mangle (EnumVal v) (vals,nr) = let bits = ceiling $ logBase 2 $ fromIntegral (List.length vals)
                                     Just idx = List.elemIndex v vals
                                 in mangle (BitS.fromNBits bits idx :: BitS.Bitstream BitS.Left) (BitstreamLen $ fromIntegral bits)
  unmangle v (vs,nr) = do
    let bits = ceiling $ logBase 2 $ fromIntegral (List.length vs)
    v' <- unmangle v (BitstreamLen $ fromIntegral bits)
    case v' of
      Nothing -> return Nothing
      Just v'' -> return $ Just $ EnumVal $ vs!!(BitS.toBits (v'' :: BitS.Bitstream BitS.Left))
  {-unmangle v (vs,nr) = do
    vs' <- mapM (\e -> do
                    l <- getRawValue (SMT.Var (T.pack e) (vs,nr) :: SMTExpr EnumVal)
                    return (e,l)) vs
    case List.find (\(_,l) -> l==v) vs' of
      Just (e,_) -> return $ Just $ EnumVal e-}
#endif
  unmangle _ _ = return Nothing

instance ToGTL Word64 where
  toGTL x = GTLIntVal (fromIntegral x)
  gtlTypeOf _ = gtlInt

-- | Create a undefined value for a given type and apply it to the supplied function.
getUndefined :: Map [String] Integer -- ^ Map of all enum types
                -> GTLType -- ^ The type for the undefined value
                -> (forall a. (Typeable a,SMTType a,ToGTL a,SMTValue a,SMTAnnotation a ~ ()) => a -> b) -- ^ The function to apply the undefined value to
                -> b
getUndefined mp rep f = case unfix rep of
  GTLInt -> f (undefined::GTLSMTInt)
  GTLBool -> f (undefined::Bool)
  --GTLEnum enums -> f (EnumVal enums (mp!enums) undefined)
  GTLNamed _ r -> getUndefined mp r f
  _ -> error $ "Please implement getUndefined for "++show rep++" you lazy fuck"

-- | Like 'getUndefined', but also restrict the type to be numeric
getUndefinedNumeric :: GTLType -> (forall a. (Typeable a,SMTType a,Num a,ToGTL a,SMTValue a,SMTBV a) => a -> b) -> b
getUndefinedNumeric rep f
  | rep == gtlInt = f (undefined::Word64)

-- | Returns 'True' if the given type is a numeric one
isNumeric :: GTLType -> Bool
isNumeric (Fix GTLInt) = True
isNumeric (Fix GTLByte) = True
isNumeric (Fix GTLFloat) = True
isNumeric _ = False

-- | Helper function to make sure that two haskell expressions have the same type
assertEq :: a -> b a -> b a
assertEq _ = id

-- | Create a mapping from enum types to Integers for all the enums in the spec.
enumMap :: Ord v => GTLSpec v -> Map [String] Integer
enumMap spec = let enums = getEnums (Map.unions [ Map.unions [gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl]
                                                | (iname,inst) <- Map.toList (gtlSpecInstances spec),
                                                  let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                                ])
               in Map.fromList (Prelude.zip (Set.toList enums) [0..])

-- | Perform k-induction by providing a solver and a GTL specification.
kInduction :: Scheduling s => s -> (SMT () -> IO ()) -> GTLSpec String -> IO (Maybe [Map (String,String) GTLConstant])
kInduction sched solver spec = do
  let enums = enumMap spec
      bas = fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               formula = List.foldl1 gand (case gtlInstanceContract inst of
                                                              Nothing -> gtlModelContract mdl
                                                              Just con -> con:(gtlModelContract mdl)
                                                          )
                           in gtl2ba (Just (gtlModelCycleTime mdl)) formula) (gtlSpecInstances spec)
      Fix (Typed _ (UnBoolExpr Always formula)) = gtlSpecVerify spec
  baseCaseOrders <- newChan
  indCaseOrders <- newChan
  baseCaseResults <- newChan
  indCaseResults <- newChan
  baseCase <- forkIO $ solver $ do
    sched_data <- createSchedulingData sched (Map.keysSet bas)
    start <- newState enums spec "0"
    assert $ initState enums spec bas start
    kInductionBase baseCaseOrders baseCaseResults (encodeProperty formula) enums spec bas sched sched_data [] start 1
  indCase <- forkIO $ solver $ do
    sched_data <- createSchedulingData sched (Map.keysSet bas)
    start <- newState enums spec "0"
    kInductionInd indCaseOrders indCaseResults (encodeProperty formula) enums spec bas sched sched_data start 1 
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
encodeProperty expr st = let BasicVar var = translateExpr (\(m,n) _ h -> fst3 $ (instanceVars $ (instanceStates st)!m)!n) expr
                         in castUSMT' var

kInductionBase :: Scheduling s => Chan Bool -> Chan (Maybe [Map (String,String) GTLConstant])
                  -> (GlobalState -> SMTExpr Bool)
                  -> Map [String] Integer -> GTLSpec String -> Map String (BA [TypedExpr String] Integer)
                  -> s -> SchedulingData s
                  -> [GlobalState] -> GlobalState -> Integer -> SMT ()
kInductionBase orders results prop enums spec bas sched sched_data all last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ connections (gtlSpecConnections spec) last last
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
                 next <- newState enums spec (show n)
                 assert $ prop last
                 assert $ schedule sched bas sched_data sched_data last next
                 kInductionBase orders results prop enums spec bas sched sched_data (last:all) next (n+1)
         )
    else return ()

kInductionInd :: Scheduling s => Chan Bool -> Chan Bool
                 -> (GlobalState -> SMTExpr Bool)
                 -> Map [String] Integer -> GTLSpec String -> Map String (BA [TypedExpr String] Integer)
                 -> s -> SchedulingData s
                 -> GlobalState -> Integer -> SMT ()
kInductionInd orders results prop enums spec bas sched sched_data last n = do
  continue <- liftIO $ readChan orders
  if continue
    then (do
             assert $ connections (gtlSpecConnections spec) last last
             assert $ limitPCs bas last
             res <- stack $ do
               assert $ not' $ prop last
               checkSat
             if res then (do
                             -- The property is not n-inductive
                             liftIO $ writeChan results False
                             next <- newState enums spec (show n)
                             assert $ prop last
                             --assert $ step bas last next
                             assert $ schedule sched bas sched_data sched_data last next
                             kInductionInd orders results prop enums spec bas sched sched_data next (n+1)
                         )
               else (liftIO $ writeChan results True)
         )
    else return ()

-- | Apply limits to all integers used to store the current state of a component. Used to strengthen k-induction.
limitPCs :: Map String (BA [TypedExpr String] Integer) -> GlobalState -> SMTExpr Bool
limitPCs bas st = and' $ concat
                  [ [(instancePC inst) .>=. 0
                    ,(instancePC inst) .<. (SMT.constant (fromIntegral sz))]
                  | (name,inst) <- Map.toList (instanceStates st), let sz = Map.size $ baTransitions $ bas!name ]
{-limitPCs bas st = and' $ concat
                  [ [BVUGE (instancePC inst) 0
                    ,BVULT (instancePC inst) (SMT.constant (fromIntegral sz))]
                  | (name,inst) <- Map.toList (instanceStates st), let sz = Map.size $ baTransitions $ bas!name ] -}
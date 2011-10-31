{-# LANGUAGE RankNTypes,DeriveDataTypeable,ExistentialQuantification,TypeFamilies #-}
module Language.GTL.Target.SMT where

import Data.Typeable
import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.Types
import Language.GTL.Buchi
import Language.GTL.Translation
import Language.SMTLib2
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

data USMTExpr = forall a. (SMTType a,Typeable a,ToGTL a,SMTValue a) => USMTExpr (SMTExpr a)

instance Show USMTExpr where
  show (USMTExpr e) = show e

castUSMT :: Typeable a => USMTExpr -> Maybe (SMTExpr a)
castUSMT (USMTExpr x) = gcast x

castUSMT' :: Typeable a => USMTExpr -> SMTExpr a
castUSMT' e = case castUSMT e of
  Nothing -> let res = error $ "Internal type-error in SMT target: Expected "++(show $ typeOf $ getUndef res)++", but got "++(show (typeOfUSMT e))
             in res
  Just e' -> e'

typeOfUSMT :: USMTExpr -> TypeRep
typeOfUSMT (USMTExpr e) = typeOf (getUndef e)

useUSMT :: (forall a. (SMTType a,Typeable a,ToGTL a,SMTValue a) => SMTExpr a -> b) -> USMTExpr -> b
useUSMT f (USMTExpr x) = f x

data GlobalState = GlobalState
                   { instanceStates :: Map String InstanceState
                   }

data InstanceState = InstanceState
                     { instanceVars :: Map String (UnrolledVar,GTLType,VarUsage)
                     , instancePC :: SMTExpr Word64
                     }

data UnrolledVar = BasicVar USMTExpr
                 | IndexedVar [UnrolledVar]
                 deriving Show

data TemporalVars v = TemporalVars { formulaEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxFEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   , auxGEnc :: Map (TypedExpr v) (SMTExpr Bool)
                                   }

newUnrolledVar :: Map [String] Integer -> GTLType -> String -> SMT UnrolledVar
newUnrolledVar enums (Fix tp) base = case tp of
  GTLArray sz tp -> do
    arr <- mapM (\i -> newUnrolledVar enums tp (base++"_"++show i)) [0..(sz-1)]
    return $ IndexedVar arr
  GTLTuple tps -> do
    arr <- mapM (\(tp,i) -> newUnrolledVar enums tp (base++"_"++show i)) (zip tps [0..])
    return $ IndexedVar arr
  GTLNamed _ tp' -> newUnrolledVar enums tp' base
  _ -> getUndefined enums (Fix tp) $ \u -> do
    v <- SMT.varNamed' u $ T.pack base
    return $ BasicVar $ USMTExpr $ assertEq u v

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

eqUnrolled :: UnrolledVar -> UnrolledVar -> SMTExpr Bool
eqUnrolled (BasicVar x) (BasicVar y) = useUSMT (\ex -> ex .==. (castUSMT' y)) x
eqUnrolled (IndexedVar x) (IndexedVar y) = and' (Prelude.zipWith eqUnrolled x y)

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

newState :: Map [String] Integer -> GTLSpec String -> String -> SMT GlobalState
newState enums spec n = do
  mp <- mapM (\(iname,inst) -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               in do
                                 is <- newInstanceState enums iname mdl n
                                 return (iname,is)
             ) (Map.toAscList $ gtlSpecInstances spec)
  return $ GlobalState { instanceStates = Map.fromAscList mp }

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

eqInst :: InstanceState -> InstanceState -> SMTExpr Bool
eqInst st1 st2 = and' ((instancePC st1 .==. instancePC st2):
                       (Map.elems $ Map.intersectionWith (\(v1,_,_) (v2,_,_) -> eqUnrolled v1 v2) (instanceVars st1) (instanceVars st2)))

eqInstOutp :: InstanceState -> InstanceState -> SMTExpr Bool
eqInstOutp st1 st2 
  = and' ((instancePC st1 .==. instancePC st2):
          (Map.elems $ Map.intersectionWith (\(v1,_,u) (v2,_,_)
                                             -> case u of
                                               Input -> SMT.constant True
                                               _ -> eqUnrolled v1 v2) (instanceVars st1) (instanceVars st2)))

eqSt :: GlobalState -> GlobalState -> SMTExpr Bool
eqSt st1 st2 = and' $ Map.elems $ Map.intersectionWith eqInst (instanceStates st1) (instanceStates st2)

existsState :: Map [String] Integer -> GTLSpec String -> (GlobalState -> SMTExpr Bool) -> SMTExpr Bool
existsState enums spec f = genExists (Map.toDescList $ gtlSpecInstances spec) []
  where
    genExists [] ys = f (GlobalState { instanceStates = Map.fromAscList ys })
    genExists ((i,inst):xs) ys = existsInstanceState enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) $ \is -> genExists xs ((i,is):ys)

existsInstanceState :: Map [String] Integer -> GTLModel String -> (InstanceState -> SMTExpr Bool) -> SMTExpr Bool
existsInstanceState enums mdl f = genExists (Map.toDescList $ Map.unions 
                                             [fmap (\x -> (x,Input)) $ gtlModelInput mdl
                                             ,fmap (\x -> (x,Output)) $ gtlModelOutput mdl
                                             ,fmap (\x -> (x,StateOut)) $ gtlModelLocals mdl]) []
  where
    genExists [] ys = exists $ \pc -> f (InstanceState (Map.fromAscList ys) pc)
    genExists ((vn,(vt,vu)):xs) ys = existsUnrolledVar enums vt $ \v -> genExists xs ((vn,(v,vt,vu)):ys)

indexUnrolled :: UnrolledVar -> [Integer] -> UnrolledVar
indexUnrolled v [] = v
indexUnrolled (IndexedVar vs) (i:is) = indexUnrolled (vs `genericIndex` i) is

getVar :: String -> String -> [Integer] -> GlobalState -> UnrolledVar
getVar inst name idx st = let (v,vt,vu) = (instanceVars $ (instanceStates st)!inst)!name
                          in indexUnrolled v idx

connections :: [(GTLConnectionPoint String,GTLConnectionPoint String)] -> GlobalState -> GlobalState -> SMTExpr Bool
connections conns stf stt
  = and' [ eqUnrolled (getVar f fv fi stf) (getVar t tv ti stt)
         | (GTLConnPt f fv fi,GTLConnPt t tv ti) <- conns
         ]

class Scheduling s where
  type SchedulingData s
  createSchedulingData :: s -> Set String -> SMT (SchedulingData s)
  schedule :: s -> SchedulingData s -> Map String (BA [TypedExpr String] Integer) -> GlobalState -> GlobalState -> SMTExpr Bool

data SimpleScheduling = SimpleScheduling

instance Scheduling SimpleScheduling where
  type SchedulingData SimpleScheduling = ()
  createSchedulingData _ _ = return ()
  schedule _ _ mp stf stt = or' [ and' ((stepInstance ba ((instanceStates stf)!iname) ((instanceStates stt)!iname))
                                        :[ eqInstOutp inst ((instanceStates stt)!iname')
                                         | (iname',inst) <- Map.toList (instanceStates stf)
                                         , iname /= iname'
                                         ])
                                | (iname,ba) <- Map.toList mp
                                ]

step :: Map String (BA [TypedExpr String] Integer) -> GlobalState -> GlobalState -> SMTExpr Bool
step bas stf stt 
  = and' [ stepInstance ba ((instanceStates stf)!name) ((instanceStates stt)!name)
         | (name,ba) <- Map.toList bas ]

fst3 :: (a,b,c) -> a
fst3 (x,_,_) = x

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

translateExpr :: (v -> VarUsage -> Integer -> UnrolledVar) ->  TypedExpr v -> UnrolledVar
translateExpr f (Fix expr)
  = case GTL.getValue expr of
    GTL.Var n i u -> f n u i
    GTL.Value val -> case val of
      GTLIntVal i -> BasicVar $ USMTExpr $ SMT.constant (fromIntegral i :: Word64)
      GTLByteVal w -> BasicVar $ USMTExpr $ SMT.constant w
      GTLBoolVal b -> BasicVar $ USMTExpr $ SMT.constant b
      GTLEnumVal v -> BasicVar $ USMTExpr $ SMT.constant (EnumVal undefined undefined v)
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
    GTL.UnBoolExpr GTL.Not arg -> let BasicVar ll = translateExpr f arg
                                  in BasicVar $ USMTExpr $ not' $ castUSMT' ll

initInstance :: Map [String] Integer -> GTLModel String -> BA [TypedExpr String] Integer -> InstanceState -> SMTExpr Bool
initInstance enums mdl ba inst
  = and' $ (or' [ (instancePC inst) .==. SMT.constant (fromIntegral f)
                | f <- Set.toList (baInits ba) ]):
    [ eqUnrolled
      (fst3 $ (instanceVars inst)!var)
      (translateExpr (\v _ _ -> fst3 $ (instanceVars inst)!v) (constantToExpr (Map.keysSet enums) def))
    | (var,Just def) <- Map.toList $ gtlModelDefaults mdl ]

initState :: Map [String] Integer -> GTLSpec String -> Map String (BA [TypedExpr String] Integer) -> GlobalState -> SMTExpr Bool
initState enums spec bas st
  = and' [ initInstance enums ((gtlSpecModels spec)!(gtlInstanceModel inst)) (bas!name) ((instanceStates st)!name)
         | (name,inst) <- Map.toList (gtlSpecInstances spec)
         ]

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
          v1 <- SMT.var
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


bmc :: Scheduling s => s -> GTLSpec String -> SMT (Maybe [Map (String,String) GTLConstant])
bmc sched spec = do
  let enums = enumMap spec
      bas = fmap (\inst -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                               formula = case gtlInstanceContract inst of
                                 Nothing -> gtlModelContract mdl
                                 Just con -> gand con (gtlModelContract mdl)
                           in gtl2ba (Just (gtlModelCycleTime mdl)) formula) (gtlSpecInstances spec)
      formula = GTL.distributeNot (gtlSpecVerify spec)
  if Map.null enums
    then return ()
    else declareEnums enums
  tmp_cur <- newTemporalVars "0" formula
  tmp_e <- newTemporalVars "e" formula
  tmp_l <- newTemporalVars "l" formula
  loop_exists <- SMT.varNamed $ T.pack $ "loop_exists"
  se <- newState enums spec "e"
  sdata <- createSchedulingData sched (Map.keysSet $ gtlSpecInstances spec)
  bmc' sched sdata enums spec formula bas tmp_cur tmp_e tmp_l loop_exists se []

data BMCState = BMCState { bmcVars :: GlobalState
                         , bmcTemporals :: TemporalVars (String,String)
                         , bmcL :: SMTExpr Bool
                         , bmcInLoop :: SMTExpr Bool
                         }

getGTLValue :: GTLType -> UnrolledVar -> SMT GTLConstant
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

getVarValues :: GlobalState -> SMT (Map (String,String) GTLConstant)
getVarValues st = do
  lst <- mapM (\(iname,inst) -> mapM (\(vname,(var,tp,us)) -> do
                                         c <- getGTLValue tp var
                                         return ((iname,vname),c)) (Map.toList $ instanceVars inst)) (Map.toList $ instanceStates st)
  return $ Map.fromList (Prelude.concat lst)

getPath :: [BMCState] -> SMT [Map (String,String) GTLConstant]
getPath = mapM (getVarValues.bmcVars) . Prelude.reverse

renderPath :: [Map (String,String) GTLConstant] -> String
renderPath path = unlines $ concat [ ("Step "++show i):[ "| "++iname++"."++var++" = "++show c | ((iname,var),c) <- Map.toList mp ] | (i,mp) <- zip [0..] path ]

bmc' :: Scheduling s => s -> SchedulingData s
        -> Map [String] Integer -> GTLSpec String
        -> TypedExpr (String,String)
        -> Map String (BA [TypedExpr String] Integer)
        -> TemporalVars (String,String)
        -> TemporalVars (String,String)
        -> TemporalVars (String,String)
        -> SMTExpr Bool 
        -> GlobalState
        -> [BMCState] -> SMT (Maybe [Map (String,String) GTLConstant])
bmc' sched sdata enums spec f bas tmp_cur tmp_e tmp_l loop_exists se [] = do
  init <- newState enums spec "0"
  l <- SMT.varNamed $ T.pack "l0"
  inloop <- SMT.varNamed $ T.pack "inloop0"
  assert $ initState enums spec bas init
  assert $ connections (gtlSpecConnections spec) init init
  assert $ not' l
  assert $ not' inloop
  tmp_nxt <- newTemporalVars "1" f
  genc <- dependencies (\(iname,var) u h -> getVar iname var [] init) f tmp_cur tmp_nxt
  assert genc
  mapM_ (\(expr,var) -> do
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
                assert $ not' $ (auxGEnc tmp_cur)!e
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
  let hist = [BMCState init tmp_cur l inloop]
  res <- stack $ do
    -- k-variant case for LoopConstraints
    assert $ eqSt se init
    assert $ not' loop_exists
    -- k-variant case for LastStateFormula
    mapM_ (\(expr,var) -> do
              assert $ var .==. ((formulaEnc tmp_cur)!expr)
              assert $ ((formulaEnc tmp_nxt)!expr) .==. ((formulaEnc tmp_l)!expr)
          ) (Map.toList $ formulaEnc tmp_e)
    -- k-variant case for IncPLTL
    mapM_ (\(expr,var) -> assert $ var .==. ((auxFEnc tmp_cur)!expr)
          ) (Map.toList $ auxFEnc tmp_e)
    mapM_ (\(expr,var) -> assert $ var .==. ((auxGEnc tmp_cur)!expr)
          ) (Map.toList $ auxGEnc tmp_e)
    solvable <- checkSat
    if solvable
      then getPath hist >>= return.Just
      else return Nothing
  case res of
    Nothing -> bmc' sched sdata enums spec f bas tmp_nxt tmp_e tmp_l loop_exists se hist
    Just path -> return $ Just path
bmc' sched sdata enums spec f bas tmp_cur tmp_e tmp_l loop_exists se history@(last_state:_) = do
  let i = length history
  cur_state <- newState enums spec (show i)
  tmp_nxt <- newTemporalVars (show $ i+1) f
  l <- SMT.varNamed $ T.pack $ "l"++show i
  inloop <- SMT.varNamed $ T.pack $ "inloop"++show i
  --assert $ step bas (bmcVars last_state) cur_state
  assert $ schedule sched sdata bas (bmcVars last_state) cur_state
  assert $ connections (gtlSpecConnections spec) cur_state cur_state
  
  -- k-invariant case for LoopConstraints:
  assert $ l .=>. (eqSt cur_state se)
  assert $ inloop .==. (or' [bmcInLoop last_state,l])
  assert $ (bmcInLoop last_state) .=>. (not' l)
  
  -- k-invariant case for LastStateFormula
  genc <- dependencies (\(iname,var) u h -> getVar iname var [] cur_state) f tmp_cur tmp_nxt
  mapM_ (\(expr,var) -> assert $ l .=>. (var .==. ((formulaEnc tmp_cur)!expr))
        ) (Map.toList $ formulaEnc tmp_l)
  
  -- k-invariant case for IncPLTL
  mapM_ (\(expr,var) -> let Just fe = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. and' [(auxFEnc $ bmcTemporals last_state)!expr
                                                  ,and' [inloop,fe]]) (Map.toList $ auxFEnc tmp_cur)
  mapM_ (\(expr,var) -> let Just ge = Map.lookup expr (formulaEnc tmp_cur)
                        in assert $ var .==. and' [(auxGEnc $ bmcTemporals last_state)!expr
                                                  ,or' [not' $ inloop,ge]]) (Map.toList $ auxGEnc tmp_cur)
  let history' = (BMCState cur_state tmp_cur l inloop):history
  -- Simple Path restriction
  simple_path <- return True
  -- This doesn't work
  {-mapM_ (\st -> assert $ or' [not' $ eqSt (bmcVars last_state) (bmcVars st)
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
  simple_path <- checkSat-}
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
             res <- stack $ do
               -- k-variant case for LoopConstraints
               assert $ loop_exists .==. inloop
               assert $ eqSt cur_state se
               -- k-variant case for LastStateFormula
               mapM_ (\(expr,var) -> do
                         assert $ ((formulaEnc tmp_e)!expr) .==. var
                         assert $ ((formulaEnc tmp_nxt)!expr) .==. ((formulaEnc tmp_l)!expr)
                     ) (Map.toList $ formulaEnc tmp_cur)
               -- k-variant case for IncPLTL
               mapM_ (\(expr,var) -> assert $ ((auxFEnc tmp_e)!expr) .==. var) (Map.toList $ auxFEnc tmp_cur)
               mapM_ (\(expr,var) -> assert $ ((auxGEnc tmp_e)!expr) .==. var) (Map.toList $ auxGEnc tmp_cur)
               r <- checkSat
               if r then getPath history' >>= return.Just
                 else return Nothing
             case res of  
               Just path -> return $ Just path
               Nothing -> bmc' sched sdata enums spec f bas tmp_nxt tmp_e tmp_l loop_exists se history')

verifyModel :: Maybe String -> GTLSpec String -> IO ()
verifyModel solver spec = do
  let solve = case solver of
        Nothing -> withZ3
        Just x -> withSMTSolver x
  res <- solve $ bmc SimpleScheduling spec
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

exactlyOne :: [SMTExpr Bool] -> SMTExpr Bool
exactlyOne [] = SMT.constant False
exactlyOne (y:ys) = exactlyOne' y (not' y) ys
  where
    exactlyOne' y n [] = y
    exactlyOne' y n (x:xs) = let' (ite x n y) (\y' -> let' (and' [not' x,n]) (\n' -> exactlyOne' y' n' xs))

data EnumVal = EnumVal [String] Integer String deriving Typeable

instance ToGTL EnumVal where
  toGTL (EnumVal _ _ name) = GTLEnumVal name
  gtlTypeOf (EnumVal enums _ _) = Fix $ GTLEnum enums

instance SMTType EnumVal where
  getSort (EnumVal _ nr _) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType (EnumVal vals nr _) = [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],declareDatatypes [] [(T.pack $ "Enum"++show nr,[(T.pack val,[]) | val <- vals])])]

instance SMTValue EnumVal where
  mangle (EnumVal _ _ v) = L.Symbol (T.pack v)
  unmangle (L.Symbol v) = EnumVal undefined undefined (T.unpack v)

instance ToGTL Word64 where
  toGTL x = GTLIntVal (fromIntegral x)
  gtlTypeOf _ = gtlInt

getUndefined :: Map [String] Integer -> GTLType -> (forall a. (Typeable a,SMTType a,ToGTL a,SMTValue a) => a -> b) -> b
getUndefined mp rep f = case unfix rep of
  GTLInt -> f (undefined::Word64)
  GTLBool -> f (undefined::Bool)
  GTLEnum enums -> f (EnumVal enums (mp!enums) undefined)
  GTLNamed _ r -> getUndefined mp r f
  _ -> error $ "Please implement getUndefined for "++show rep++" you lazy fuck"

getUndefinedNumeric :: GTLType -> (forall a. (Typeable a,SMTType a,Num a,ToGTL a,SMTValue a,SMTBV a) => a -> b) -> b
getUndefinedNumeric rep f
  | rep == gtlInt = f (undefined::Word64)

isNumeric :: GTLType -> Bool
isNumeric (Fix GTLInt) = True
isNumeric (Fix GTLByte) = True
isNumeric (Fix GTLFloat) = True
isNumeric _ = False

assertEq :: a -> b a -> b a
assertEq _ = id

enumMap :: Ord v => GTLSpec v -> Map [String] Integer
enumMap spec = let enums = getEnums (Map.unions [ Map.unions [gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl]
                                                | (iname,inst) <- Map.toList (gtlSpecInstances spec),
                                                  let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                                ])
               in Map.fromList (Prelude.zip (Set.toList enums) [0..])

declareEnums :: Map [String] Integer -> SMT ()
declareEnums mp = declareDatatypes [] 
                  [ (T.pack $ "Enum"++show n,[ (T.pack val,[]) | val <- vals ])
                  | (vals,n) <- Map.toList mp ]
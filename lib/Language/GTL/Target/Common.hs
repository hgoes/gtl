{-| Provides some common code that can be shared between multiple translation targets.
    As most translation targets operate on the notion of states and variables, the code to
    generate those can be shared between almost all targets.
 -}
module Language.GTL.Target.Common 
       (TargetModel(..),
        TransitionConditions(..),
        TargetVar,
        buildTargetModel
        ) where

import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.Types
import Language.GTL.Translation
import Language.GTL.Buchi
import Language.GTL.Restriction

import Data.Set as Set
import Data.Map as Map
import Data.List (genericIndex)
import Control.Monad.Identity
import Data.Foldable
import Prelude hiding (foldl,concat,foldl1)

-- | A qualified variable with instance name, variable name and index.
type TargetVar = (String,String,[Integer])

type OutputMap = Map TargetVar (Set TargetVar,Maybe Integer,GTLType)
type InputMap = Map TargetVar (Integer,GTLType)

-- | Represents conditions which can be used in transitions.
data TransitionConditions = TransitionConditions
                            { tcOutputs :: [([(TargetVar,Integer)],Restriction TargetVar)] -- ^ How should the output variables be assigned
                            , tcAtoms :: [TypedExpr TargetVar] -- ^ What conditions must hold for the transition to fire
                            , tcOriginal :: [TypedExpr (String,String)] -- ^ Original expressions which were used to generate this
                            } deriving (Show,Eq,Ord)

-- | A flattened out model without arrays or tuples.
data TargetModel = TargetModel
                   { tmodelVars :: [(TargetVar,Integer,GTLType,Maybe (Set GTLConstant))] -- ^ All variables used in the model with type and default values
                   , tmodelProcs :: Map String (BA TransitionConditions Integer) -- ^ A map of processes, represented by B&#xFC;chi automata
                   , tmodelVerify :: TypedExpr TargetVar -- ^ The verification goal
                   } deriving Show

completeRestrictions :: Ord a => Map a (Restriction b) -> Map a GTLType -> Map a c -> Map a (Restriction b)
completeRestrictions restr outp om = Map.intersection (Map.union restr (fmap emptyRestriction outp)) om

-- | Creates a flattened model from a GTL specification.
buildTargetModel :: GTLSpec String -> TargetModel
buildTargetModel spec = buildTargetModel' spec (buildInputMap spec) (buildOutputMap spec)

buildTargetModel' :: GTLSpec String -> InputMap -> OutputMap -> TargetModel
buildTargetModel' spec inmp outmp
  = let all_vars = Map.foldrWithKey (\(mf,vf,fi) (vars,lvl,tp) cur
                                     -> case lvl of
                                       Nothing -> cur
                                       Just rlvl -> Map.insertWith (\(lvl1,inp,tp) (lvl2,_,_) -> (max lvl1 lvl2,inp,tp)
                                                                   ) (mf,vf,fi) (rlvl,False,tp) cur
                                    ) (fmap (\(lvl,tp) -> (lvl,True,tp)) inmp) outmp
        all_vars2 = Map.foldrWithKey
                    (\iname inst mp
                     -> let defs = Map.union
                                   (gtlInstanceDefaults inst)
                                   (gtlModelDefaults mdl)
                            mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                        in Map.foldrWithKey
                           (\var def mp
                            -> let tp = case Map.lookup var (gtlModelInput mdl) of
                                     Nothing -> (gtlModelOutput mdl)!var
                                     Just p -> p
                               in case def of
                                 Just v -> foldl (\mp (c,(rtp,idx))
                                                  -> let nmp = Map.adjust (\(lvl,inp,tp,restr)
                                                                           -> (lvl,inp,tp,case restr of
                                                                                  Nothing -> Just $ Set.singleton c
                                                                                  Just r -> Just (Set.insert c r)
                                                                              )) (iname,var,idx) mp
                                                     in case Map.lookup (iname,var,idx) outmp of
                                                       Nothing -> nmp
                                                       Just (tvars,_,_) -> foldl (\mp' tvar -> Map.adjust (\(lvl,inp,tp,restr)
                                                                                                           -> (lvl,inp,tp,case restr of
                                                                                                                  Nothing -> Just $ Set.singleton c
                                                                                                                  Just r -> Just (Set.insert c r)
                                                                                                              )) tvar mp') nmp tvars
                                                 ) mp $ zip (flattenConstant v) (flattenVar tp [])
                                 Nothing -> mp) mp defs
                    ) (fmap (\(lvl,inp,tp) -> (lvl,inp,tp,Nothing)) all_vars) (gtlSpecInstances spec)
    in TargetModel
       { tmodelVars = [ ((mdl,var,idx),lvl,tp,inits)
                      | ((mdl,var,idx),(lvl,inp,tp,inits)) <- Map.toList all_vars2
                      ]
       , tmodelProcs = buildModelProcs spec outmp inmp
       , tmodelVerify = flattenExpr (\(m,v) i -> (m,v,i)) [] (gtlSpecVerify spec)
       }

buildModelProcs :: GTLSpec String -> OutputMap -> InputMap -> Map String (BA TransitionConditions Integer)
buildModelProcs spec outmp inmp = Map.mapWithKey instanceToBuchi (gtlSpecInstances spec)
  where
    instanceToBuchi :: String -> (GTLInstance String) -> BA TransitionConditions Integer
    instanceToBuchi name inst = let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                in baMapAlphabet (atomsToRestr name mdl outmp inmp) $ gtl2ba $ gtlModelContract mdl

atomsToRestr :: String -> GTLModel String -> OutputMap -> InputMap -> [TypedExpr String] -> TransitionConditions
atomsToRestr name mdl outmp inmp atm 
  = let (restr,cond) = translateAtoms
                       (\v idx -> (name,v,idx))
                       (\(n,v,is) i -> (n,v,i:is))
                       (Just (name,mdl)
                       ) atm
        rrestr = completeRestrictions restr (Map.fromList 
                                             [ ((name,var,idx),rtp)
                                             | (var,tp) <- Map.toList $ gtlModelOutput mdl, 
                                               (rtp,idx) <- flattenVar tp []
                                             ]) outmp
    in TransitionConditions
       [ ([ (tvar,case Map.lookup tvar inmp of
                Nothing -> error (show (tvar,var,r))
                Just (p,_) -> p
            )
          | tvar <- Set.toList tvars
          ] ++ (case nvr of
                   Nothing -> []
                   Just lvl -> [(var,lvl)]),r)
       | (var,r) <- Map.toList rrestr,
         let (tvars,nvr) = case Map.lookup var outmp of
               Nothing -> (Set.empty,Nothing)
               Just (p1,p2,_) -> (p1,p2)
       ] cond (fmap (mapGTLVars (\v -> (name,v))) atm)

buildOutputMap :: GTLSpec String -> OutputMap
buildOutputMap spec
  = let mp1 = foldl (\mp (GTLConnPt mf vf fi,GTLConnPt mt vt ti)
                     -> let tp_out = getInstanceVariableType spec False mf vf
                            tp_in = getInstanceVariableType spec True mt vt
                            idx_in = Set.fromList [ (mt,vt,i) | (_,i) <- flattenVar tp_in ti ]
                            mp_out = Map.fromList [ ((mf,vf,i),(idx_in,Nothing,tp)) | (tp,i) <- flattenVar tp_out fi ]
                        in Map.unionWith (\(set1,nvr1,tp1) (set2,nvr2,tp2) -> (Set.union set1 set2,nvr1,tp1)) mp mp_out
                    ) Map.empty (gtlSpecConnections spec)
        mp2 = foldl (\mp (var,idx,lvl,tp)
                     -> Map.unionWith (\(set1,nvr1,tp1) (set2,nvr2,tp2) -> (Set.union set1 set2,case nvr1 of
                                                                                  Nothing -> nvr2
                                                                                  Just rnvr1 -> case nvr2 of
                                                                                    Nothing -> nvr1
                                                                                    Just rnvr2 -> Just $ max rnvr1 rnvr2,tp1))
                        mp (Map.fromList [ ((fst var,snd var,i),(Set.empty,Just lvl,tp)) | (tp,i) <- flattenVar tp idx ])
                    ) mp1 (getVars $ gtlSpecVerify spec)
    in mp2

buildInputMap :: GTLSpec String -> InputMap
buildInputMap spec
  = Map.foldlWithKey (\mp name inst
                      -> let mdl = case Map.lookup (gtlInstanceModel inst) (gtlSpecModels spec) of
                               Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel inst)++" not found."
                               Just p -> p
                         in foldl (\mp' (var,idx,lvl,tp)
                                   -> if Map.member var (gtlModelInput mdl)
                                      then foldl (\mp'' (tp',idx')
                                                  -> Map.insertWith (\(i1,tp1) (i2,_) -> (max i1 i2,tp1))
                                                     (name,var,idx') (lvl,tp') mp'') mp' (flattenVar tp idx)
                                      else mp'
                                  ) (Map.union mp (Map.fromList
                                                   [ ((name,var,idx),(0,t))
                                                   | (var,tp) <- Map.toList $ gtlModelInput mdl,
                                                     (t,idx) <- allPossibleIdx tp
                                                   ]
                                                  )) (getVars $ gtlModelContract mdl)
                     ) Map.empty (gtlSpecInstances spec)

lookupType :: GTLSpec String -> String -> String -> [Integer] -> Bool -> GTLType
lookupType spec inst var idx inp
  = let rinst = case Map.lookup inst (gtlSpecInstances spec) of
          Nothing -> error $ "Internal error: Instance "++show inst++" not found."
          Just p -> p
        mdl = case Map.lookup (gtlInstanceModel rinst) (gtlSpecModels spec) of
          Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel rinst)++" not found."
          Just p -> p
        ttp = case Map.lookup var (if inp then gtlModelInput mdl
                                   else gtlModelOutput mdl) of
                Nothing -> error $ "Internal error: Variable "++show var++" not found."
                Just p -> p
        tp = case resolveIndices ttp idx of
          Right p -> p
          _ -> error $ "Internal error: Unable to resolve type "++show ttp
    in tp

flattenVar :: GTLType -> [Integer] -> [(GTLType,[Integer])]
flattenVar (GTLArray sz tp) (i:is) = fmap (\(t,is) -> (t,i:is)) (flattenVar tp is)
flattenVar (GTLArray sz tp) [] = concat [fmap (\(t,is) -> (t,i:is)) (flattenVar tp []) | i <- [0..(sz-1)] ]
flattenVar (GTLTuple tps) (i:is) = fmap (\(t,is) -> (t,i:is)) (flattenVar (tps `genericIndex` i) is)
flattenVar (GTLTuple tps) [] = concat [ fmap (\(t,is) -> (t,i:is)) (flattenVar tp []) | (i,tp) <- zip [0..] tps ]
flattenVar tp [] = allPossibleIdx tp --[(tp,[])]

flattenConstant :: GTLConstant -> [GTLConstant]
flattenConstant c = case unfix c of
  GTLArrayVal vs -> concat $ fmap flattenConstant vs
  GTLTupleVal vs -> concat $ fmap flattenConstant vs
  _ -> [c]

allPossibleIdx :: GTLType -> [(GTLType,[Integer])]
allPossibleIdx (GTLArray sz tp) = concat [ [(t,i:idx) | i <- [0..(sz-1)] ] | (t,idx) <- allPossibleIdx tp ]
allPossibleIdx (GTLTuple tps) = concat [ [ (t,i:idx) | (t,idx) <- allPossibleIdx tp ] | (i,tp) <- zip [0..] tps ]
allPossibleIdx tp = [(tp,[])]

flattenExpr :: (Ord a,Ord b) => (a -> [Integer] -> b) -> [Integer] -> TypedExpr a -> TypedExpr b
flattenExpr f idx e = Typed (getType e) $ case getValue e of
  Var v i -> Var (f v idx) i
  Value v -> case idx of
    [] -> Value (fmap (Fix . flattenExpr f [].unfix) v)
    (i:is) -> case v of
      GTLArrayVal vs -> getValue $ flattenExpr f is (unfix $ vs `genericIndex` i)
      GTLTupleVal vs -> getValue $ flattenExpr f is (unfix $ vs `genericIndex` i)
  BinBoolExpr op l r -> BinBoolExpr op (Fix $ flattenExpr f idx $ unfix l) (Fix $ flattenExpr f idx $ unfix r)
  BinRelExpr rel l r -> getValue $ foldl1 gand [ Typed GTLBool (BinRelExpr rel (Fix el) (Fix er))
                                               | (el,er) <- zip (unpackExpr f idx (unfix l)) (unpackExpr f idx (unfix r)) ]
  BinIntExpr op l r -> BinIntExpr op (Fix $ flattenExpr f idx $ unfix l) (Fix $ flattenExpr f idx $ unfix r)
  UnBoolExpr op ne -> UnBoolExpr op (Fix $ flattenExpr f idx $ unfix ne)
  IndexExpr e i -> getValue $ flattenExpr f (i:idx) (unfix e)
  Automaton buchi -> Automaton (baMapAlphabet (fmap $ Fix . flattenExpr f idx . unfix) buchi)

unpackExpr :: (Ord a,Ord b) => (a -> [Integer] -> b) -> [Integer] -> TypedExpr a -> [TypedExpr b]
unpackExpr f i e = case getValue e of
  Var v lvl -> case getType e of
    GTLArray sz tp -> concat [ unpackExpr f (j:i) (Typed tp (Var v lvl)) | j <- [0..(sz-1)] ]
    GTLTuple tps -> concat [ unpackExpr f (j:i) (Typed t (Var v lvl)) | (t,j) <- zip tps [0..] ]
    _ -> [Typed (getType e) (Var (f v i) lvl)]
  Value (GTLArrayVal vs) -> concat $ fmap (unpackExpr f i . unfix) vs
  Value (GTLTupleVal vs) -> concat $ fmap (unpackExpr f i . unfix) vs
  Value v -> [Typed (getType e) (Value $ fmap (Fix . flattenExpr f i . unfix) v)]
  BinBoolExpr op l r -> [Typed (getType e) (BinBoolExpr op (Fix $ flattenExpr f i $ unfix l) (Fix $ flattenExpr f i $ unfix r))]
  BinRelExpr rel l r -> [Typed (getType e) (BinRelExpr rel (Fix $ flattenExpr f i $ unfix l) (Fix $ flattenExpr f i $ unfix r))]
  BinIntExpr op l r -> [Typed (getType e) (BinIntExpr op (Fix $ flattenExpr f i $ unfix l) (Fix $ flattenExpr f i $ unfix r))]
  UnBoolExpr op ne -> [Typed (getType e) (UnBoolExpr op (Fix $ flattenExpr f i $ unfix ne))]
  IndexExpr ne ni -> unpackExpr f (ni:i) (unfix ne)
  Automaton buchi -> [ flattenExpr f i e ]

translateAtoms :: (Ord a,Ord b) => (a -> [Integer] -> b) -> (b -> Integer -> b) -> Maybe (String,GTLModel a) -> [TypedExpr a] -> (Map b (Restriction b),[TypedExpr b])
translateAtoms f g mmdl
  = foldl (\(restrs,expr) e -> case translateAtom f g mmdl e True [] of
              Left nrestr -> (foldl (\mp (var,re) -> Map.insertWith (\x y -> let Just p = plusRestriction x y in p) var re mp) restrs nrestr,expr)
              Right ne -> (restrs,ne++expr)) (Map.empty,[])

translateAtom :: (Ord a,Ord b) => (a -> [Integer] -> b) -> (b -> Integer -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> Bool -> [Integer]
                 -> Either [(b,Restriction b)] [TypedExpr b]
translateAtom f g mmdl expr t idx
  = case getValue expr of
    BinRelExpr rel lhs rhs -> case translateExpr f g mmdl (unfix lhs) of
      Left trg -> case translateExpr f g mmdl (unfix rhs) of
        Left _ -> error "Can't relate more than one output var (yet)"
        Right src -> Left $ buildAssign rrel (getType $ unfix lhs) trg src
      Right src -> case translateExpr f g mmdl (unfix rhs) of
        Left trg -> Left $ buildAssign (relTurn rrel) (getType $ unfix lhs) trg src
        Right src2 -> Right [ Typed GTLBool (BinRelExpr rrel (Fix s1) (Fix s2)) | (s1,s2) <- zip src src2 ]
      where
        rrel = if t then rel else relNot rel
        buildAssign BinLT tp trg [src] = [(trg,(emptyRestriction tp) { upperLimits = [(False,src)] })]
        buildAssign BinLTEq tp trg [src] = [(trg,(emptyRestriction tp) { upperLimits = [(True,src)] })]
        buildAssign BinGT tp trg [src] = [(trg,(emptyRestriction tp) { lowerLimits = [(False,src)] })]
        buildAssign BinGTEq tp trg [src] = [(trg,(emptyRestriction tp) { lowerLimits = [(True,src)] })]
        buildAssign BinEq tp trg [src] = [ (trg,(emptyRestriction tp) { equals = [src] }) ]
        buildAssign BinEq tp trg src = [ (g trg i,(emptyRestriction tp) { equals = [s] }) | (i,s) <- zip [0..] src ]
        buildAssign BinNEq tp trg [src] = [ (trg,(emptyRestriction tp) { unequals = [src] }) ]
        buildAssign BinNEq tp trg src = [ (g trg i,(emptyRestriction tp) { unequals = [s] }) | (i,s) <- zip [0..] src ]
    Var var lvl -> let chk = [(if t then id else gnot) (Typed GTLBool (Var (f var idx) lvl))]
                   in case mmdl of
                     Nothing -> Right chk
                     Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                                        then Right chk
                                        else Left [ (f var (reverse idx),(emptyRestriction GTLBool) { allowedValues = Just (Set.singleton (GTLBoolVal t)) }) ]
    IndexExpr e i -> translateAtom f g mmdl (unfix e) t (i:idx)
    UnBoolExpr GTL.Not p -> translateAtom f g mmdl (unfix p) (not t) idx

translateExpr :: (Ord a,Ord b) => (a -> [Integer] -> b) -> (b -> Integer -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> Either b [TypedExpr b]
translateExpr f g mmdl expr = case getValue expr of
  Var var 0 -> case mmdl of
    Nothing -> Right $ translateCheckExpr f Nothing expr []
    Just (name,mdl) -> if Map.member var (gtlModelOutput mdl)
                       then Left $ f var []
                       else Right $ translateCheckExpr f mmdl expr []
  IndexExpr e i -> case translateExpr f g mmdl (unfix e) of
    Left v -> Left $ g v i
    Right _ -> Right $ translateCheckExpr f mmdl (unfix e) [i]
  _ -> Right $ translateCheckExpr f mmdl expr []

translateCheckExpr :: (Ord a,Ord b) => (a -> [Integer] -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> [Integer] -> [TypedExpr b]
translateCheckExpr f mmdl expr idx = case getValue expr of
    Var var lvl -> case mmdl of
      Nothing -> [Typed (getType expr) (Var (f var (reverse idx)) lvl)]
      Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                         then [Typed (getType expr) (Var (f var (reverse idx)) lvl)]
                         else error "Can't relate more than one output var (yet)"
    Value (GTLTupleVal xs) -> case idx of
      i:is -> translateCheckExpr f mmdl (unfix $ xs `genericIndex` i) is
      [] -> concat [ translateCheckExpr f mmdl (unfix x) [] | x <- xs ]
    Value (GTLArrayVal xs) -> case idx of
      i:is -> translateCheckExpr f mmdl (unfix $ xs `genericIndex` i) is
      [] -> concat [ translateCheckExpr f mmdl (unfix x) [] | x <- xs ]
    BinIntExpr op lhs rhs -> [ Typed (getType expr) (BinIntExpr op (Fix l) (Fix r))
                             | (l,r) <- zip (translateCheckExpr f mmdl (unfix lhs) idx)
                                        (translateCheckExpr f mmdl (unfix rhs) idx) ]
    IndexExpr e i -> translateCheckExpr f mmdl (unfix e) (i:idx)
    _ -> [mapGTLVars (const undefined) expr]

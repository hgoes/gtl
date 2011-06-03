module Language.GTL.Target.Common where

import Language.GTL.Model
import Language.GTL.Expression
import Language.GTL.Types
import Language.GTL.Translation
import Language.GTL.Buchi

import Data.Set as Set
import Data.Map as Map
import Data.List (genericIndex)
import Control.Monad.Identity

type TargetVar = (String,String,[Integer])

type OutputMap = Map TargetVar (Set TargetVar,Maybe Integer)
type InputMap = Map TargetVar Integer

data TargetModel = TargetModel
                   { tmodelVars :: [(TargetVar,Integer,GTLType)]
                   , tmodelProcs :: Map String (GBuchi (Integer,Int) ([([(TargetVar,Integer)],Restriction TargetVar)],[TypedExpr TargetVar]) Bool)
                   , tmodelVerify :: TypedExpr TargetVar
                   , tmodelInits :: [(TargetVar,Integer,GTLType,Maybe GTLConstant)]
                   } deriving Show

data Restriction v = Restriction
                     { restrictionType :: GTLType
                     , lowerLimits :: [(Bool,TypedExpr v)]
                     , upperLimits :: [(Bool,TypedExpr v)]
                     , allowedValues :: Maybe (Set (GTLValue ()))
                     , forbiddenValues :: Set (GTLValue ())
                     , equals :: [TypedExpr v]
                     , unequals :: [TypedExpr v]
                     } deriving Show

emptyRestriction :: GTLType -> Restriction v
emptyRestriction tp = Restriction tp [] [] Nothing Set.empty [] []

plusRestriction :: Restriction v -> Restriction v -> Restriction v
plusRestriction r1 r2
  | restrictionType r1 == restrictionType r2
    = Restriction { restrictionType = restrictionType r1
                  , upperLimits = (upperLimits r1)++(upperLimits r2)
                  , lowerLimits = (lowerLimits r1)++(lowerLimits r2)
                  , allowedValues = case allowedValues r1 of
                    Nothing -> allowedValues r2
                    Just a1 -> case allowedValues r2 of
                      Nothing -> Just a1
                      Just a2 -> Just (Set.intersection a1 a2)
                  , forbiddenValues = Set.union (forbiddenValues r1) (forbiddenValues r2)
                  , equals = (equals r1)++(equals r2)
                  , unequals = (unequals r1)++(unequals r2)
                  }
  | otherwise = error $ "Merging restrictions of type "++show (restrictionType r1)++" and "++show (restrictionType r2)

completeRestrictions :: Ord a => Map a (Restriction b) -> Map a GTLType -> Map a (Restriction b)
completeRestrictions restr outp = Map.union restr (fmap emptyRestriction outp)

buildTargetModel :: GTLSpec String -> InputMap -> OutputMap -> TargetModel
buildTargetModel spec inmp outmp
  = let all_vars = Map.foldrWithKey (\(mf,vf,fi) (vars,lvl) cur
                                     -> case lvl of
                                       Nothing -> cur
                                       Just rlvl -> Map.insertWith (\(lvl1,inp) (lvl2,_) -> (max lvl1 lvl2,inp)) (mf,vf,fi) (rlvl,False) cur
                                    ) (fmap (\lvl -> (lvl,True)) inmp) outmp
    in TargetModel
       { tmodelVars = [ ((mdl,var,idx),lvl,lookupType spec mdl var idx inp)
                      | ((mdl,var,idx),(lvl,inp)) <- Map.toList all_vars ]
       , tmodelProcs = Map.mapWithKey (\name inst
                                       -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                          in translateGBA $ runIdentity $ 
                                             gtlToBuchi (\atm -> let (restr,cond) = translateAtoms
                                                                                    (\v idx -> (name,v,idx))
                                                                                    (\(n,v,is) i -> (n,v,i:is))
                                                                                    (Just (name,mdl)) atm
                                                                     rrestr = completeRestrictions restr (Map.fromList 
                                                                                                          [ ((name,var,idx),rtp)
                                                                                                          | (var,tp) <- Map.toList $ gtlModelOutput mdl, 
                                                                                                            (rtp,idx) <- flattenVar tp []
                                                                                                          ])
                                                                 in return ([ ([ (tvar,case Map.lookup tvar inmp of
                                                                                     Nothing -> error (show (tvar,var,r))
                                                                                     Just p -> p
                                                                                 )
                                                                               | tvar <- Set.toList tvars
                                                                               ] ++ (case nvr of
                                                                                        Nothing -> []
                                                                                        Just lvl -> [(var,lvl)]),r)
                                                                            | (var,r) <- Map.toList rrestr,
                                                                              let (tvars,nvr) = case Map.lookup var outmp of
                                                                                    Nothing -> (Set.empty,Nothing)
                                                                                    Just p -> p
                                                                            ],cond)
                                                        )
                                             (gtlModelContract mdl)
                                      )
                       (gtlSpecInstances spec)
       , tmodelVerify = flattenExpr (\(m,v) i -> (m,v,i)) [] (gtlSpecVerify spec)
       , tmodelInits = [ (rvar,lvl,tp,c)
                       | (iname,inst) <- Map.toList $ gtlSpecInstances spec,
                         let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst),
                         (var,def) <- Map.toList $ gtlModelDefaults mdl,
                         (rvar,lvl,tp,c) <- case Map.lookup var (gtlModelInput mdl) of
                           Just mtp -> [ ((iname,var,idx),inmp!(iname,var,idx),rtp,c)
                                       | ((rtp,idx),c) <- zip (flattenVar mtp []) 
                                                          (case def of
                                                              Nothing -> repeat Nothing
                                                              Just rdef -> fmap Just (flattenConstant rdef))
                                       ]
                           Nothing -> [ (nvar,lvl,rtp,c)
                                      | ((rtp,idx),c) <- zip (flattenVar ((gtlModelOutput mdl)!var) []) 
                                                         (case def of
                                                             Nothing -> repeat Nothing
                                                             Just rdef -> fmap Just (flattenConstant rdef)),
                                        let (nvars,nvr) = outmp!(iname,var,idx),
                                        (nvar,lvl) <- (case nvr of
                                                          Nothing -> id
                                                          Just n -> (((iname,var,idx),n):))
                                                      (fmap (\v -> (v,inmp!v)) $ Set.toList nvars)
                                      ]
                       ]
       }

buildOutputMap :: GTLSpec String -> OutputMap
buildOutputMap spec
  = let mp1 = foldl (\mp (GTLConnPt mf vf fi,GTLConnPt mt vt ti)
                     -> let tp_out = getInstanceVariableType spec False mf vf
                            tp_in = getInstanceVariableType spec True mt vt
                            idx_in = Set.fromList [ (mt,vt,i) | (_,i) <- flattenVar tp_in ti ]
                            mp_out = Map.fromList [ ((mf,vf,i),(idx_in,Nothing)) | (_,i) <- flattenVar tp_out fi ]
                        in Map.unionWith (\(set1,nvr1) (set2,nvr2) -> (Set.union set1 set2,nvr1)) mp mp_out
                    ) Map.empty (gtlSpecConnections spec)
        mp2 = foldl (\mp (var,idx,lvl)
                     -> let tp = getInstanceVariableType spec False (fst var) (snd var)
                        in Map.unionWith (\(set1,nvr1) (set2,nvr2) -> (Set.union set1 set2,case nvr1 of
                                                                          Nothing -> nvr2
                                                                          Just rnvr1 -> case nvr2 of
                                                                            Nothing -> nvr1
                                                                            Just rnvr2 -> Just $ max rnvr1 rnvr2))
                           mp (Map.fromList [ ((fst var,snd var,i),(Set.empty,Just lvl)) | (_,i) <- flattenVar tp idx ])
                    ) mp1 (getVars $ gtlSpecVerify spec)
    in mp2

buildInputMap :: GTLSpec String -> InputMap
buildInputMap spec
  = Map.foldlWithKey (\mp name inst
                      -> let mdl = case Map.lookup (gtlInstanceModel inst) (gtlSpecModels spec) of
                               Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel inst)++" not found."
                               Just p -> p
                         in foldl (\mp' (var,idx,lvl)
                                   -> if Map.member var (gtlModelInput mdl)
                                      then Map.insertWith max (name,var,idx) lvl mp'
                                      else mp'
                                  ) (Map.union mp (Map.fromList
                                                   [ ((name,var,idx),0)
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

flattenExpr :: (a -> [Integer] -> b) -> [Integer] -> TypedExpr a -> TypedExpr b
flattenExpr f idx e = Typed (getType e) $ case getValue e of
  Var v i -> Var (f v idx) i
  Value v -> case idx of
    [] -> Value (fmap (Fix . flattenExpr f [].unfix) v)
    (i:is) -> case v of
      GTLArrayVal vs -> getValue $ flattenExpr f is (unfix $ vs `genericIndex` i)
      GTLTupleVal vs -> getValue $ flattenExpr f is (unfix $ vs `genericIndex` i)
  BinBoolExpr op l r -> BinBoolExpr op (Fix $ flattenExpr f idx $ unfix l) (Fix $ flattenExpr f idx $ unfix r)
  BinRelExpr rel l r -> getValue $ foldl1 gtlAnd [ Typed GTLBool (BinRelExpr rel (Fix el) (Fix er))
                                                 | (el,er) <- zip (unpackExpr f idx (unfix l)) (unpackExpr f idx (unfix r)) ]
  BinIntExpr op l r -> BinIntExpr op (Fix $ flattenExpr f idx $ unfix l) (Fix $ flattenExpr f idx $ unfix r)
  UnBoolExpr op ne -> UnBoolExpr op (Fix $ flattenExpr f idx $ unfix ne)
  IndexExpr e i -> getValue $ flattenExpr f (i:idx) (unfix e)
  Automaton buchi -> Automaton (buchiMapVars (Fix . flattenExpr f idx . unfix) buchi)

unpackExpr :: (a -> [Integer] -> b) -> [Integer] -> TypedExpr a -> [TypedExpr b]
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
              Left nrestr -> (foldl (\mp (var,re) -> Map.insertWith plusRestriction var re mp) restrs nrestr,expr)
              Right ne -> (restrs,ne++expr)) (Map.empty,[])

translateAtom :: (Ord a) => (a -> [Integer] -> b) -> (b -> Integer -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> Bool -> [Integer]
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
    UnBoolExpr Not p -> translateAtom f g mmdl (unfix p) (not t) idx

translateExpr :: (Ord a) => (a -> [Integer] -> b) -> (b -> Integer -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> Either b [TypedExpr b]
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

translateCheckExpr :: (Ord a) => (a -> [Integer] -> b) -> Maybe (String,GTLModel a) -> TypedExpr a -> [Integer] -> [TypedExpr b]
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

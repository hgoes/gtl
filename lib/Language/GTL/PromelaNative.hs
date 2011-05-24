{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
module Language.GTL.PromelaNative where

import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.Promela.Syntax as Pr
import Language.GTL.Translation
import Language.GTL.Buchi
import Language.GTL.Types

import Data.Set as Set
import Data.Map as Map
import Data.List (genericIndex,elemIndex)
import Data.Dynamic
import Data.Foldable
import Prelude hiding (foldl,concat,foldl1)
import Control.Monad.Identity
import Data.Monoid
import Data.Maybe

type OutputMap = Map (String,String,[Integer]) (Set (String,String,[Integer]),Maybe Integer)
type InputMap = Map (String,String,[Integer]) Integer

translateSpec :: GTLSpec String -> [Pr.Module]
translateSpec spec = let outmp = buildOutputMap spec
                         inmp = buildInputMap spec
                     in declareVars spec outmp inmp ++
                        [ translateInstance name (gtlSpecModels spec) inst inmp outmp | (name,inst) <- Map.toList $ gtlSpecInstances spec]++
                        [ translateNever (gtlSpecVerify spec) inmp outmp
                        , translateInit spec outmp inmp ]

translateInit :: GTLSpec String -> OutputMap -> InputMap -> Pr.Module
translateInit spec outmp inmp
  = Pr.Init Nothing
    [Pr.toStep $ prAtomic $
     (concat [ case def of
                  Nothing -> []
                  Just rdef -> case Map.lookup var (gtlModelInput mdl) of
                    Just tp -> assign iname var [] 0 (convertValue tp rdef)
                    Nothing -> outputAssign iname var [] (convertValue ((gtlModelOutput mdl)!var) rdef) outmp inmp
             | (iname,inst) <- Map.toList (gtlSpecInstances spec),
               let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst),
               (var,def) <- Map.toList $ gtlModelDefaults mdl ]) ++
     [ Pr.StmtRun name [] | (name,_) <- Map.toList (gtlSpecInstances spec) ]
    ]

declareVars :: GTLSpec String -> OutputMap -> InputMap -> [Pr.Module]
declareVars spec outmp inmp
  = let all_vars = Map.foldrWithKey (\(mf,vf,fi) (vars,lvl) cur
                                     -> case lvl of
                                       Nothing -> cur
                                       Just rlvl -> Map.insertWith (\(lvl1,inp) (lvl2,_) -> (max lvl1 lvl2,inp)) (mf,vf,fi) (rlvl,False) cur
                                    ) (fmap (\lvl -> (lvl,True)) inmp) outmp
    in [ Pr.Decl $ Pr.Declaration Nothing (convertType $ lookupType spec mdl var idx inp)
         [(mdl++"_"++var++concat [ "_"++show i | i <- idx ],Just (lvl+1),Nothing)]
       | ((mdl,var,idx),(lvl,inp)) <- Map.toList all_vars ]

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

convertValue :: GTLType -> GTLConstant -> Pr.AnyExpression
convertValue tp c = case unfix c of
  GTLIntVal v -> Pr.ConstExpr $ Pr.ConstInt v
  GTLBoolVal v -> Pr.ConstExpr $ Pr.ConstInt $ if v then 1 else 0
  GTLEnumVal x -> let GTLEnum xs = tp 
                      Just i = elemIndex x xs
                  in Pr.ConstExpr $ Pr.ConstInt $ fromIntegral i
  _ -> error $ "Can't convert value "++show c

convertType :: GTLType -> Pr.Typename
convertType GTLInt = Pr.TypeInt
convertType GTLBool = Pr.TypeBool
convertType (GTLEnum _) = Pr.TypeInt

translateNever :: TypedExpr (String,String) -> InputMap -> OutputMap -> Pr.Module
translateNever expr inmp outmp
  = let buchi = runIdentity (gtlToBuchi
                             (return.(translateAtoms Nothing (\Nothing (mdl,var) -> varName mdl var)))
                             (gnot expr))
    in Pr.Never $ fmap Pr.toStep (Pr.StmtSkip:(translateBuchi Nothing id buchi inmp outmp))

flattenVar :: GTLType -> [Integer] -> [(GTLType,[Integer])]
flattenVar (GTLArray sz tp) (i:is) = fmap (\(t,is) -> (t,i:is)) (flattenVar tp is)
flattenVar (GTLArray sz tp) [] = concat [fmap (\(t,is) -> (t,i:is)) (flattenVar tp []) | i <- [0..(sz-1)] ]
flattenVar (GTLTuple tps) (i:is) = fmap (\(t,is) -> (t,i:is)) (flattenVar (tps `genericIndex` i) is)
flattenVar (GTLTuple tps) [] = concat [ fmap (\(t,is) -> (t,i:is)) (flattenVar tp []) | (i,tp) <- zip [0..] tps ]
flattenVar tp [] = allPossibleIdx tp --[(tp,[])]

allPossibleIdx :: GTLType -> [(GTLType,[Integer])]
allPossibleIdx (GTLArray sz tp) = concat [ [(t,i:idx) | i <- [0..(sz-1)] ] | (t,idx) <- allPossibleIdx tp ]
allPossibleIdx (GTLTuple tps) = concat [ [ (t,i:idx) | (t,idx) <- allPossibleIdx tp ] | (i,tp) <- zip [0..] tps ]
allPossibleIdx tp = [(tp,[])]

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

varName :: String -> String -> [Integer] -> Integer -> Pr.VarRef
varName mdl var idx lvl = VarRef (mdl ++ "_" ++ var ++ concat [ "_"++show i | i <- idx]) (Just lvl) Nothing

outputAssign :: String -> String -> [Integer] -> Pr.AnyExpression -> OutputMap -> InputMap -> [Pr.Statement]
outputAssign mdl var idx expr outmp inmp = case Map.lookup (mdl,var,idx) outmp of
  Nothing -> []
  Just (tos,nvr) -> let rest = fmap (\(mt,vt,it) -> assign mt vt it (case Map.lookup (mt,vt,it) inmp of
                                                                        Nothing -> error $ "Internal error: "++show (mt,vt,it)++" not found in input map "++show inmp++"."
                                                                        Just p -> p
                                                                    ) expr) (Set.toList tos)
                    in concat $ case nvr of
                      Nothing -> rest
                      Just lvl -> assign mdl var idx lvl expr : rest

firstAssignTarget :: String -> String -> [Integer] -> OutputMap -> InputMap -> Maybe Pr.VarRef
firstAssignTarget mdl var idx outmp inmp = case Map.lookup (mdl,var,idx) outmp of
  Nothing -> Nothing
  Just (tos,nvr) -> if Set.null tos
                    then (case nvr of
                             Nothing -> Nothing
                             Just lvl -> Just $ varName mdl var idx 0)
                    else (let (rmdl,rvar,ridx) = Set.findMin tos
                          in Just $ varName rmdl rvar ridx 0)


assign :: String -> String -> [Integer] -> Integer -> Pr.AnyExpression -> [Pr.Statement]
assign mdl var idx lvl expr 
  = foldl (\stmts cl -> Pr.StmtAssign (varName mdl var idx cl) (if cl==0
                                                                then expr
                                                                else RefExpr (varName mdl var idx (cl-1))):stmts)
    []
    [0..lvl]

translateInstance :: String -> Map String (GTLModel String) -> GTLInstance String -> InputMap -> OutputMap -> Pr.Module
translateInstance name models inst inmp outmp
  = translateModel name (let mdl = case Map.lookup (gtlInstanceModel inst) models of
                               Nothing -> error $ "Internal error: Model "++show (gtlInstanceModel inst)++" not found."
                               Just p -> p
                         in mdl
                         { gtlModelContract = case gtlInstanceContract inst of
                              Nothing -> gtlModelContract mdl
                              Just c -> gtlAnd (gtlModelContract mdl) c
                         }
                        ) inmp outmp

translateModel :: String -> GTLModel String -> InputMap -> OutputMap -> Pr.Module
translateModel name model inmp outmp
  = let buchi = runIdentity (gtlToBuchi (\x -> let (restr,cond) = translateAtoms (Just (name,model)) (\(Just name) var -> varName name var) x
                                               in return (completeRestrictions (gtlModelOutput model) restr,cond)
                                        )
                             (gtlModelContract model))
    in Pr.ProcType
       { proctypeActive = Nothing
       , proctypeName = name
       , proctypeArguments = []
       , proctypePriority = Nothing
       , proctypeProvided = Nothing
       , proctypeSteps = fmap Pr.toStep $ translateBuchi (Just name) (\var -> (name,var)) buchi inmp outmp
       }

translateBuchi :: Maybe String -> (a -> (String,String)) -> Buchi (Map (a,[Integer]) Restriction,Maybe Pr.AnyExpression) -> InputMap -> OutputMap -> [Pr.Statement]
translateBuchi mmdl f buchi inmp outmp
  = let rbuchi = translateGBA buchi
    in [ prIf [ (case snd $ vars st of
                    Nothing -> []
                    Just cond -> [Pr.StmtExpr $ Pr.ExprAny cond])++
                catMaybes [ translateRestriction mdl rvar idx outmp inmp restr
                          | ((var,idx),restr) <- Map.toList (fst $ vars st), let (mdl,rvar) = f var ] ++
                [ Pr.StmtGoto $ "st_"++show s1++"_"++show s2 ]
              | ((s1,s2),st) <- Map.toList rbuchi, isStart st ]
       ] ++
       [ translateState mmdl f outmp inmp stname st rbuchi | (stname,st) <- Map.toList rbuchi ]

data Restriction = IntRestr IntRestriction
                 | ArrayRestr ArrayRestriction
                 | EnumRestr (Maybe (Set String))

data IntRestriction = IntRestriction
                      { upperLimits :: [(Bool,Pr.AnyExpression)]
                      , lowerLimits :: [(Bool,Pr.AnyExpression)]
                      , allowedValues :: Maybe (Set Integer)
                      , forbiddenValues :: Set Integer
                      , equals :: [Pr.AnyExpression]
                      , unequals :: [Pr.AnyExpression]
                      }

data ArrayRestriction = ArrayRestriction
                        { arrEquals :: [[Pr.AnyExpression]]
                        , arrUnequals :: [[Pr.AnyExpression]]
                        }

instance Monoid IntRestriction where
  mempty = IntRestriction [] [] Nothing Set.empty [] []
  mappend r1 r2 = IntRestriction
                  { upperLimits = (upperLimits r1)++(upperLimits r2)
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

instance Monoid ArrayRestriction where
  mempty = ArrayRestriction [] []
  mappend r1 r2 = ArrayRestriction { arrEquals = (arrEquals r1)++(arrEquals r2)
                                   , arrUnequals = (arrUnequals r1)++(arrUnequals r2)
                                   }

mergeRestriction :: Restriction -> Restriction -> Restriction
mergeRestriction (IntRestr x) (IntRestr y) = IntRestr (mappend x y)
mergeRestriction (ArrayRestr x) (ArrayRestr y) = ArrayRestr (mappend x y)
mergeRestriction (EnumRestr x) (EnumRestr y) = case x of
  Nothing -> EnumRestr y
  Just rx -> case y of
    Nothing -> EnumRestr (Just rx)
    Just ry -> EnumRestr (Just (Set.intersection rx ry))

translateAtoms :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> [Integer] -> Integer -> Pr.VarRef) -> [TypedExpr a] -> (Map (a,[Integer]) Restriction,Maybe Pr.AnyExpression)
translateAtoms mmdl f = foldl (\(mp,expr) at -> case translateAtom mmdl f at True [] of
                                  Left (name,restr) -> (Map.insertWith mergeRestriction name restr mp,expr)
                                  Right cond -> case expr of
                                    Nothing -> (mp,Just cond)
                                    Just cond2 -> (mp,Just $ Pr.BinExpr Pr.BinAnd cond cond2)
                              ) (Map.empty,Nothing)

completeRestrictions :: Ord a => Map a GTLType -> Map (a,[Integer]) Restriction -> Map (a,[Integer]) Restriction
completeRestrictions tp mp = Map.union mp (Map.fromList
                                           [ ((v,idx),case rtp of
                                                 GTLInt -> IntRestr mempty
                                                 GTLBool -> IntRestr $ mempty { allowedValues = Just (Set.fromList [0,1]) }
                                                 GTLEnum enums -> IntRestr $ mempty { allowedValues = Just (Set.fromList $ fmap fst (zip [0..] enums))
                                                                                    })
                                           | (v,t) <- Map.toList tp,
                                             (rtp,idx) <- allPossibleIdx t ])
                                           
translateAtom :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> [Integer] -> Integer -> Pr.VarRef) -> TypedExpr a -> Bool -> [Integer]
                 -> Either ((a,[Integer]),Restriction) Pr.AnyExpression
translateAtom mmdl f expr t idx
  = case getValue expr of
    BinRelExpr rel lhs rhs -> case translateExpr mmdl f (unfix lhs) of
      Left trg -> case translateExpr mmdl f (unfix rhs) of
        Left _ -> error "Can't relate more than one output var (yet)"
        Right src -> Left $ buildAssign rrel trg src
      Right src -> case translateExpr mmdl f (unfix rhs) of
        Left trg -> Left $ buildAssign (relTurn rrel) trg src
        Right src2 -> Right $ buildComp rrel src src2
      where
        rrel = if t then rel else relNot rel
        buildAssign GTL.BinLT trg [src] = (trg,IntRestr $ mempty { upperLimits = [(False,src)] })
        buildAssign GTL.BinLTEq trg [src] = (trg,IntRestr $ mempty { upperLimits = [(True,src)] })
        buildAssign GTL.BinGT trg [src] = (trg,IntRestr $ mempty { lowerLimits = [(False,src)] })
        buildAssign GTL.BinGTEq trg [src] = (trg,IntRestr $ mempty { lowerLimits = [(True,src)] })
        buildAssign GTL.BinEq trg [src] = (trg,IntRestr $ mempty { equals = [src] })
        buildAssign GTL.BinEq trg src = (trg,ArrayRestr $ mempty { arrEquals = [src] })
        buildAssign GTL.BinNEq trg [src] = (trg,IntRestr $ mempty { unequals = [src] })
        buildAssign GTL.BinNEq trg src = (trg,ArrayRestr $ mempty { arrUnequals = [src] })
        buildComp op s1 s2 = case [ Pr.BinExpr (case rel of
                                                   GTL.BinLT -> Pr.BinLT
                                                   GTL.BinLTEq -> Pr.BinLTE
                                                   GTL.BinGT -> Pr.BinGT
                                                   GTL.BinGTEq -> Pr.BinGTE
                                                   GTL.BinEq -> Pr.BinEquals
                                                   GTL.BinNEq -> Pr.BinNotEquals) p1 p2
                                  | (p1,p2) <- zip s1 s2 ] of
                               [x] -> x
                               xs -> foldl1 (Pr.BinExpr Pr.BinAnd) xs
    Var var lvl -> let chk = (if t then id else Pr.UnExpr Pr.UnLNot) (Pr.RefExpr (f (fmap fst mmdl) var idx lvl))
                   in case mmdl of
                     Nothing -> Right chk
                     Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                                        then Right chk
                                        else Left ((var,reverse idx),IntRestr $ mempty { allowedValues = Just (Set.singleton (if t then 1 else 0)) })
    IndexExpr e i -> translateAtom mmdl f (unfix e) t (i:idx)
    UnBoolExpr GTL.Not p -> translateAtom mmdl f (unfix p) (not t) idx
{-translateAtom mmdl f (GTLBoolExpr (ElemExpr var lits eq) p)
  = let chk = foldl1 (\expr trg
                      -> Pr.BinExpr (if c then Pr.BinOr else Pr.BinAnd)
                         expr (Pr.BinExpr (if c then Pr.BinEquals else Pr.BinNotEquals)
                               (Pr.RefExpr (f (fmap fst mmdl) (name var) (time var)))
                               trg)) (fmap (\i -> Pr.ConstExpr $ ConstInt $ fromIntegral i) ints)
        c = (eq && p) || (not eq && not p)
        ints = fmap (\(Constant (GTLIntVal i) _) -> fromIntegral i) lits
    in case mmdl of
      Nothing -> Right chk
      Just (_,mdl) -> if Map.member (name var) (gtlModelInput mdl)
                      then Right chk
                      else Left (name var,if c
                                          then mempty { allowedValues = Just $ Set.fromList ints }
                                          else mempty { forbiddenValues = Set.fromList ints })-}

translateExpr :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> [Integer] -> Integer -> Pr.VarRef) -> TypedExpr a -> Either (a,[Integer]) [Pr.AnyExpression]
translateExpr mmdl f expr = case getValue expr of
  Var var 0 -> case mmdl of
    Nothing -> Right $ translateCheckExpr Nothing f expr []
    Just (name,mdl) -> if Map.member var (gtlModelOutput mdl)
                       then Left (var,[])
                       else Right $ translateCheckExpr mmdl f expr []
  IndexExpr e i -> case translateExpr mmdl f (unfix e) of
    Left (v,idx) -> Left (v,i:idx)
    Right _ -> Right $ translateCheckExpr mmdl f (unfix e) [i]
  _ -> Right $ translateCheckExpr mmdl f expr []

translateCheckExpr :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> [Integer] -> Integer -> Pr.VarRef)
                      -> TypedExpr a -> [Integer] -> [Pr.AnyExpression]
translateCheckExpr mmdl f expr idx = case getValue expr of
    Var var lvl -> case mmdl of
      Nothing -> [RefExpr (f Nothing var (reverse idx) lvl)]
      Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                         then [RefExpr (f (Just name) var (reverse idx) lvl)]
                         else error "Can't relate more than one output var (yet)"
    Value (GTLIntVal x) -> [Pr.ConstExpr $ ConstInt $ fromIntegral x]
    Value (GTLBoolVal x) -> [Pr.ConstExpr $ ConstInt (if x then 1 else 0)]
    Value (GTLEnumVal x) -> let GTLEnum enums = getType expr
                                Just v = elemIndex x enums
                            in [Pr.ConstExpr $ ConstInt $ fromIntegral v]
    Value (GTLTupleVal xs) -> case idx of
      i:is -> translateCheckExpr mmdl f (unfix $ xs `genericIndex` i) is
      [] -> concat [ translateCheckExpr mmdl f (unfix x) [] | x <- xs ]
    Value (GTLArrayVal xs) -> case idx of
      i:is -> translateCheckExpr mmdl f (unfix $ xs `genericIndex` i) is
      [] -> concat [ translateCheckExpr mmdl f (unfix x) [] | x <- xs ]
    BinIntExpr op lhs rhs -> [ Pr.BinExpr (case op of
                                              OpPlus -> Pr.BinPlus
                                              OpMinus -> Pr.BinMinus
                                              OpMult -> Pr.BinMult
                                              OpDiv -> Pr.BinDiv) p1 p2
                             | (p1,p2) <- zip (translateCheckExpr mmdl f (unfix lhs) idx)
                                          (translateCheckExpr mmdl f (unfix rhs) idx) ]
    IndexExpr e i -> translateCheckExpr mmdl f (unfix e) (i:idx)

translateRestriction :: String -> String -> [Integer] -> OutputMap -> InputMap -> Restriction -> Maybe Pr.Statement
translateRestriction mdl var idx outmp inmp (ArrayRestr restr)
  = let assignEquals = [ concat [ outputAssign mdl var (i:idx) e outmp inmp | (i,e) <- zip [0..] eq ]
                       | eq <- arrEquals restr
                       ]
    in case assignEquals of
      [] -> Nothing
      [[x]] -> Just x
      [x] -> Just $ prSequence x
      _ -> Just $ prIf assignEquals
translateRestriction mdl var idx outmp inmp (IntRestr restr)
  = let checkNEquals to = case unequals restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (Pr.BinExpr Pr.BinNotEquals to) (unequals restr))
        checkEquals to = case equals restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (Pr.BinExpr Pr.BinEquals to) (equals restr))
        checkAllowed to = case allowedValues restr of
          Nothing -> Nothing
          Just s -> Just $ if Set.null s
                           then Pr.ConstExpr $ Pr.ConstInt 0
                           else foldl1 (Pr.BinExpr Pr.BinOr) (fmap (\i -> Pr.BinExpr Pr.BinEquals to
                                                                          (Pr.ConstExpr $ Pr.ConstInt i)
                                                                   ) (Set.toList s))
        checkNAllowed to = if Set.null (forbiddenValues restr)
                           then Nothing
                           else Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\i -> Pr.BinExpr Pr.BinNotEquals to
                                                                                  (Pr.ConstExpr $ Pr.ConstInt i)
                                                                           ) (Set.toList $ forbiddenValues restr))
        checkUppers to = case upperLimits restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\(incl,expr) -> Pr.BinExpr (if incl
                                                                                       then Pr.BinLTE
                                                                                       else Pr.BinLT) to expr)
                                                     (upperLimits restr))
        checkLowers to = case lowerLimits restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\(incl,expr) -> Pr.BinExpr (if incl
                                                                                       then Pr.BinGTE
                                                                                       else Pr.BinGT) to expr)
                                                     (lowerLimits restr))
        build f = foldl (\cur el -> case el of
                            Nothing -> cur
                            Just rel -> case cur of
                              Nothing -> Just rel
                              Just rcur -> Just (f rel rcur)) Nothing
    in case equals restr of
      [] -> case allowedValues restr of
        Just r -> let rr = Set.difference r (forbiddenValues restr)
                      check v = build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f (Pr.ConstExpr $ ConstInt v)) [checkNEquals,checkUppers,checkLowers])
                  in case catMaybes [ case ((case check v of
                                                Nothing -> []
                                                Just chk -> [ Pr.StmtExpr $ Pr.ExprAny chk ])++
                                            (outputAssign mdl var idx (Pr.ConstExpr $ Pr.ConstInt v) outmp inmp)) of
                                        [] -> Nothing
                                        p -> Just p
                                    | v <- Set.toList rr ] of 
                       [] -> Nothing
                       p -> Just $ prIf p
        Nothing -> Just $ prSequence $ buildGenerator (upperLimits restr) (lowerLimits restr) (\v -> build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f v) [checkNEquals,checkNAllowed])) mdl var idx outmp inmp
      _ -> case catMaybes  [ case ((case build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f v) [checkAllowed,checkNEquals,checkNAllowed,checkUppers,checkLowers]) of
                                       Nothing -> []
                                       Just chk -> [Pr.StmtExpr $ Pr.ExprAny chk])++
                                   (outputAssign mdl var idx v outmp inmp)) of
                               [] -> Nothing
                               p -> Just p
                           | v <- equals restr ] of
                    [] -> Nothing
                    p -> Just $ prIf p

buildGenerator :: [(Bool,Pr.AnyExpression)] -> [(Bool,Pr.AnyExpression)] -> (Pr.AnyExpression -> Maybe Pr.AnyExpression) -> String -> String -> [Integer] -> OutputMap -> InputMap -> [Pr.Statement]
buildGenerator upper lower check mdl var idx outmp inmp
  = let rupper e = case upper of
          [] -> Pr.BinExpr Pr.BinLT e (Pr.ConstExpr $ Pr.ConstInt (fromIntegral (maxBound::Int)))
          _ -> foldl1 (Pr.BinExpr Pr.BinAnd) $
               fmap (\(inc,expr) -> Pr.BinExpr Pr.BinLT e (if inc
                                                           then expr
                                                           else Pr.BinExpr Pr.BinMinus expr (Pr.ConstExpr $ Pr.ConstInt 1))
                    ) upper
        rlower = fmap (\(inc,expr) -> if inc
                                      then expr
                                      else Pr.BinExpr Pr.BinPlus expr (Pr.ConstExpr $ Pr.ConstInt 1)) lower
    in case firstAssignTarget mdl var idx outmp inmp of
      Nothing -> [Pr.StmtSkip]
      Just trg -> [minimumAssignment (Pr.ConstExpr $ Pr.ConstInt (fromIntegral (minBound::Int)))
                   (\e -> prSequence $ outputAssign mdl var idx e outmp inmp)
                   rlower]++
                  [prDo $ [[Pr.StmtExpr $ Pr.ExprAny $ rupper (Pr.RefExpr trg)]++
                           (outputAssign mdl var idx (Pr.BinExpr Pr.BinPlus (Pr.RefExpr trg) (Pr.ConstExpr $ Pr.ConstInt 1)) outmp inmp)
                          ]++(case check (Pr.RefExpr trg) of
                                   Nothing -> [[Pr.StmtBreak]]
                                   Just rcheck -> [[Pr.StmtExpr $ Pr.ExprAny rcheck
                                                   ,Pr.StmtBreak]
                                                  ,[Pr.StmtElse,Pr.StmtSkip]
                                                  ])
                  ]

minimumAssignment :: Pr.AnyExpression -> (Pr.AnyExpression -> Pr.Statement) -> [Pr.AnyExpression] -> Pr.Statement
minimumAssignment def f []     = f def
minimumAssignment _   f (x:xs) = minimumAssignment' x xs
  where
    minimumAssignment' x [] = f x
    minimumAssignment' x (y:ys) = prIf [ [Pr.StmtExpr $ Pr.ExprAny $ Pr.BinExpr Pr.BinLT x y
                                         ,minimumAssignment' x ys
                                         ]
                                       , [Pr.StmtElse
                                         ,minimumAssignment' y ys
                                         ]
                                       ]

translateState :: Maybe String -> (a -> (String,String)) -> OutputMap -> InputMap -> (Integer,Int)
                  -> BuchiState (Integer,Int) (Map (a,[Integer]) Restriction,Maybe Pr.AnyExpression) Bool
                  -> GBuchi (Integer,Int) (Map (a,[Integer]) Restriction,Maybe Pr.AnyExpression) Bool -> Pr.Statement
translateState mmdl f outmp inmp (n1,n2) st buchi
  = (if finalSets st && isNothing mmdl
     then Pr.StmtLabel ("accept_"++show n1++"_"++show n2)
     else id) $
    Pr.StmtLabel ("st_"++show n1++"_"++show n2)
    (prAtomic $ (case mmdl of
                    Nothing -> []
                    Just mdl -> [Pr.StmtPrintf ("ENTER "++mdl++" "++show n1++" "++show n2++"\n") []]
                )++
     [prIf [ (case mcond of
                 Nothing -> []
                 Just cond -> [Pr.StmtExpr $ Pr.ExprAny cond])++
             catMaybes [ translateRestriction mdl rvar idx outmp inmp restr
                       | ((var,idx),restr) <- Map.toList assign, let (mdl,rvar) = f var ] ++
             [Pr.StmtGoto $ "st_"++show s1++"_"++show s2]
           | (s1,s2) <- Set.toList $ successors st,
             let (assign,mcond) = vars $ case Map.lookup (s1,s2) buchi of
                   Nothing -> error $ "Internal error: Buchi state "++show (s1,s2)++" not found."
                   Just p -> p
           ]
     ]
    )

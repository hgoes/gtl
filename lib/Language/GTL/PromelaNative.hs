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
import Data.Dynamic
import Data.Foldable
import Prelude hiding (foldl,concat,foldl1)
import Control.Monad.Identity
import Data.Monoid
import Data.Maybe

type OutputMap = Map (String,String) (Set (String,String),Maybe Integer)
type InputMap = Map (String,String) Integer

translateSpec :: GTLSpec String -> [Pr.Module]
translateSpec spec = let outmp = buildOutputMap spec
                         inmp = buildInputMap spec
                     in declareVars spec outmp inmp ++
                        [ translateModel name mdl inmp outmp | (name,mdl) <- Map.toList $ gtlSpecModels spec]++
                        [ translateNever (gtlSpecVerify spec) inmp outmp
                        , translateInit spec outmp inmp ]

translateInit :: GTLSpec String -> OutputMap -> InputMap -> Pr.Module
translateInit spec outmp inmp
  = Pr.Init Nothing
    $ fmap Pr.toStep $
    (concat [ case def of
                 Nothing -> []
                 Just rdef -> if Map.member var (gtlModelInput mdl)
                              then assign name var 0 (convertValue rdef)
                              else outputAssign name var (convertValue rdef) outmp inmp
            | (name,mdl) <- Map.toList (gtlSpecModels spec),
              (var,def) <- Map.toList $ gtlModelDefaults mdl ]) ++
    [ Pr.StmtRun name [] | (name,_) <- Map.toList (gtlSpecModels spec) ]

declareVars :: GTLSpec String -> OutputMap -> InputMap -> [Pr.Module]
declareVars spec outmp inmp
  = let all_vars = Map.foldrWithKey (\(mf,vf) (vars,lvl) cur
                                     -> case lvl of
                                       Nothing -> cur
                                       Just rlvl -> Map.insertWith (\(lvl1,inp) (lvl2,_) -> (max lvl1 lvl2,inp)) (mf,vf) (rlvl,False) cur
                                    ) (fmap (\lvl -> (lvl,True)) inmp) outmp
    in [ Pr.Decl $ Pr.Declaration Nothing (convertType $ lookupType spec mdl var inp)
         [(mdl++"_"++var,Just (lvl+1),Nothing)]
       | ((mdl,var),(lvl,inp)) <- Map.toList all_vars ]

lookupType :: GTLSpec String -> String -> String -> Bool -> GTLType
lookupType spec mdl var inp = case Map.lookup mdl (gtlSpecModels spec) of
  Nothing -> error $ "Internal error: Model "++mdl++" not found"
  Just model -> (if inp then gtlModelInput model
                 else gtlModelOutput model)!var

convertValue :: GTLConstant -> Pr.AnyExpression
convertValue c = case unfix c of
  GTLIntVal v -> Pr.ConstExpr $ Pr.ConstInt v
  GTLBoolVal v -> Pr.ConstExpr $ Pr.ConstInt $ if v then 1 else 0
  _ -> error $ "Can't convert value "++show c

convertType :: GTLType -> Pr.Typename
convertType GTLInt = Pr.TypeInt
convertType GTLBool = Pr.TypeBool

translateNever :: TypedExpr (String,String) -> InputMap -> OutputMap -> Pr.Module
translateNever expr inmp outmp
  = let buchi = runIdentity (gtlToBuchi
                             (return.(translateAtoms Nothing (\Nothing (mdl,var) -> varName mdl var)))
                             (gnot expr))
    in Pr.Never $ fmap Pr.toStep (translateBuchi Nothing id buchi inmp outmp)

buildOutputMap :: GTLSpec String -> OutputMap
buildOutputMap spec
  = let mp1 = foldl (\mp (GTLConnPt mf vf [],GTLConnPt mt vt []) 
                     -> Map.alter (\mentr -> case mentr of
                                      Nothing -> Just (Set.singleton (mt,vt),Nothing)
                                      Just (tos,nvr) -> Just (Set.insert (mt,vt) tos,nvr)
                                  ) (mf,vf) mp) Map.empty (gtlSpecConnections spec)
        mp2 = foldl (\mp (var,lvl) -> Map.alter (\mentr -> case mentr of
                                                    Nothing -> Just (Set.empty,Just lvl)
                                                    Just (tos,nvr) -> Just (tos,Just (case nvr of
                                                                                         Nothing -> lvl
                                                                                         Just olvl -> max lvl olvl)
                                                                           )
                                                ) var mp) mp1 (getVars $ gtlSpecVerify spec)
    in mp2

buildInputMap :: GTLSpec String -> InputMap
buildInputMap spec
  = Map.foldlWithKey (\mp name mdl
                      -> foldl (\mp' (var,lvl)
                                -> if Map.member var (gtlModelInput mdl)
                                   then Map.insertWith max (name,var) lvl mp'
                                   else mp'
                               ) mp (getVars $ gtlModelContract mdl)
                     ) Map.empty (gtlSpecModels spec)

varName :: String -> String -> Integer -> Pr.VarRef
varName mdl var lvl = VarRef (mdl ++ "_" ++ var) (Just lvl) Nothing

outputAssign :: String -> String -> Pr.AnyExpression -> OutputMap -> InputMap -> [Pr.Statement]
outputAssign mdl var expr outmp inmp = case Map.lookup (mdl,var) outmp of
  Nothing -> []
  Just (tos,nvr) -> let rest = fmap (\(mt,vt) -> assign mt vt (inmp!(mt,vt)) expr) (Set.toList tos)
                    in concat $ case nvr of
                      Nothing -> rest
                      Just lvl -> assign mdl var lvl expr : rest

firstAssignTarget :: String -> String -> OutputMap -> InputMap -> Maybe Pr.VarRef
firstAssignTarget mdl var outmp inmp = case Map.lookup (mdl,var) outmp of
  Nothing -> Nothing
  Just (tos,nvr) -> if Set.null tos
                    then (case nvr of
                             Nothing -> Nothing
                             Just lvl -> Just $ varName mdl var 0)
                    else (let (rmdl,rvar) = Set.findMin tos
                          in Just $ varName rmdl rvar 0)


assign :: String -> String -> Integer -> Pr.AnyExpression -> [Pr.Statement]
assign mdl var lvl expr = foldl (\stmts cl -> Pr.StmtAssign (varName mdl var cl) (if cl==0
                                                                                  then expr
                                                                                  else RefExpr (varName mdl var (cl-1))):stmts)
                          []
                          [0..lvl]

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

translateBuchi :: Maybe String -> (a -> (String,String)) -> Buchi (Map a IntRestriction,Maybe Pr.AnyExpression) -> InputMap -> OutputMap -> [Pr.Statement]
translateBuchi mmdl f buchi inmp outmp
  = let rbuchi = translateGBA buchi
    in [ prIf [ (case snd $ vars st of
                    Nothing -> []
                    Just cond -> [Pr.StmtExpr $ Pr.ExprAny cond])++
                [ Pr.StmtGoto $ "st_"++show s1++"_"++show s2 ]
              | ((s1,s2),st) <- Map.toList rbuchi, isStart st ]
       ] ++
       [ translateState mmdl f outmp inmp stname st rbuchi | (stname,st) <- Map.toList rbuchi ]

data IntRestriction = IntRestriction
                      { upperLimits :: [(Bool,Pr.AnyExpression)]
                      , lowerLimits :: [(Bool,Pr.AnyExpression)]
                      , allowedValues :: Maybe (Set Integer)
                      , forbiddenValues :: Set Integer
                      , equals :: [Pr.AnyExpression]
                      , unequals :: [Pr.AnyExpression]
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

translateAtoms :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> Integer -> Pr.VarRef) -> [TypedExpr a] -> (Map a IntRestriction,Maybe Pr.AnyExpression)
translateAtoms mmdl f = foldl (\(mp,expr) at -> case translateAtom mmdl f at True of
                                  Left (name,restr) -> (Map.insertWith mappend name restr mp,expr)
                                  Right cond -> case expr of
                                    Nothing -> (mp,Just cond)
                                    Just cond2 -> (mp,Just $ Pr.BinExpr Pr.BinAnd cond cond2)
                              ) (Map.empty,Nothing)

completeRestrictions :: Ord a => Map a GTLType -> Map a IntRestriction -> Map a IntRestriction
completeRestrictions tp mp = Map.union mp (fmap (const mempty) tp)

translateAtom :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> Integer -> Pr.VarRef) -> TypedExpr a -> Bool
                 -> Either (a,IntRestriction) Pr.AnyExpression
translateAtom mmdl f expr t
  | getType expr == GTLBool = case getValue expr of
    BinRelExpr rel lhs rhs -> case translateExpr mmdl f (unfix lhs) of
      Left trg -> case translateExpr mmdl f (unfix rhs) of
        Left _ -> error "Can't relate more than one output var (yet)"
        Right src -> Left $ buildAssign rrel trg src
      Right src -> case translateExpr mmdl f (unfix rhs) of
        Left trg -> Left $ buildAssign (relTurn rrel) trg src
        Right src2 -> Right $ buildComp rrel src src2
      where
        rrel = if t then rel else relNot rel
        buildAssign GTL.BinLT trg src = (trg,mempty { upperLimits = [(False,src)] })
        buildAssign GTL.BinLTEq trg src = (trg,mempty { upperLimits = [(True,src)] })
        buildAssign GTL.BinGT trg src = (trg,mempty { lowerLimits = [(False,src)] })
        buildAssign GTL.BinGTEq trg src = (trg,mempty { lowerLimits = [(True,src)] })
        buildAssign GTL.BinEq trg src = (trg,mempty { equals = [src] })
        buildAssign GTL.BinNEq trg src = (trg,mempty { unequals = [src] })
        buildComp op s1 s2 = Pr.BinExpr (case rel of
                                            GTL.BinLT -> Pr.BinLT
                                            GTL.BinLTEq -> Pr.BinLTE
                                            GTL.BinGT -> Pr.BinGT
                                            GTL.BinGTEq -> Pr.BinGTE
                                            GTL.BinEq -> Pr.BinEquals
                                            GTL.BinNEq -> Pr.BinNotEquals) s1 s2
    Var var lvl -> let chk = (if t then id else Pr.UnExpr Pr.UnLNot) (Pr.RefExpr (f (fmap fst mmdl) var lvl))
                   in case mmdl of
                     Nothing -> Right chk
                     Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                                        then Right chk
                                        else Left (var,mempty { allowedValues = Just (Set.singleton (if t then 1 else 0)) })
    UnBoolExpr GTL.Not p -> translateAtom mmdl f (unfix p) (not t)
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

translateExpr :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> Integer -> Pr.VarRef) -> TypedExpr a -> Either a Pr.AnyExpression
translateExpr mmdl f expr
  | getType expr == GTLInt = case getValue expr of
    Var var 0 -> case mmdl of
      Nothing -> Right $ translateCheckExpr Nothing f expr
      Just (name,mdl) -> if Map.member var (gtlModelOutput mdl)
                         then Left var
                         else Right $ translateCheckExpr mmdl f expr
    _ -> Right $ translateCheckExpr mmdl f expr

translateCheckExpr :: (Ord a) => Maybe (String,GTLModel a) -> (Maybe String -> a -> Integer -> Pr.VarRef) -> TypedExpr a -> Pr.AnyExpression
translateCheckExpr mmdl f expr
  | getType expr == GTLInt = case getValue expr of
    Var var lvl -> case mmdl of
      Nothing -> RefExpr (f Nothing var lvl)
      Just (name,mdl) -> if Map.member var (gtlModelInput mdl)
                         then RefExpr (f (Just name) var lvl)
                         else error "Can't relate more than one output var (yet)"
    Value (GTLIntVal x) -> Pr.ConstExpr $ ConstInt $ fromIntegral x
    Value (GTLBoolVal x) -> Pr.ConstExpr $ ConstInt (if x then 1 else 0)
    BinIntExpr op lhs rhs -> Pr.BinExpr (case op of
                                            OpPlus -> Pr.BinPlus
                                            OpMinus -> Pr.BinMinus
                                            OpMult -> Pr.BinMult
                                            OpDiv -> Pr.BinDiv)
                             (translateCheckExpr mmdl f $ unfix lhs)
                             (translateCheckExpr mmdl f $ unfix rhs)

translateRestriction :: String -> String -> OutputMap -> InputMap -> IntRestriction -> Pr.Statement
translateRestriction mdl var outmp inmp restr
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
                  in prIf [ (case check v of
                                Nothing -> []
                                Just chk -> [ Pr.StmtExpr $ Pr.ExprAny chk ])++
                            (outputAssign mdl var (Pr.ConstExpr $ Pr.ConstInt v) outmp inmp)
                          | v <- Set.toList rr ]
        Nothing -> prSequence $ buildGenerator (upperLimits restr) (lowerLimits restr) (\v -> build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f v) [checkNEquals,checkNAllowed])) mdl var outmp inmp
      _ -> prIf [ (case build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f v) [checkAllowed,checkNEquals,checkNAllowed,checkUppers,checkLowers]) of
                      Nothing -> []
                      Just chk -> [Pr.StmtExpr $ Pr.ExprAny chk])++
                  (outputAssign mdl var v outmp inmp)
                | v <- equals restr ]

buildGenerator :: [(Bool,Pr.AnyExpression)] -> [(Bool,Pr.AnyExpression)] -> (Pr.AnyExpression -> Maybe Pr.AnyExpression) -> String -> String -> OutputMap -> InputMap -> [Pr.Statement]
buildGenerator upper lower check mdl var outmp inmp
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
    in case firstAssignTarget mdl var outmp inmp of
      Nothing -> []
      Just trg -> [minimumAssignment (Pr.ConstExpr $ Pr.ConstInt (fromIntegral (minBound::Int)))
                   (\e -> prSequence $ outputAssign mdl var e outmp inmp)
                   rlower]++
                  [prDo $ [[Pr.StmtExpr $ Pr.ExprAny $ rupper (Pr.RefExpr trg)]++
                           (outputAssign mdl var (Pr.BinExpr Pr.BinPlus (Pr.RefExpr trg) (Pr.ConstExpr $ Pr.ConstInt 1)) outmp inmp)
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

translateState :: Maybe String -> (a -> (String,String)) -> OutputMap -> InputMap -> (Integer,Int) -> BuchiState (Integer,Int) (Map a IntRestriction,Maybe Pr.AnyExpression) Bool -> GBuchi (Integer,Int) (Map a IntRestriction,Maybe Pr.AnyExpression) Bool -> Pr.Statement
translateState mmdl f outmp inmp (n1,n2) st buchi
  = (if finalSets st && isNothing mmdl
     then Pr.StmtLabel ("accept_"++show n1++"_"++show n2)
     else id) $
    Pr.StmtLabel ("st_"++show n1++"_"++show n2)
    (prAtomic $ (case mmdl of
                    Nothing -> []
                    Just mdl -> [Pr.StmtPrintf ("ENTER "++mdl++" "++show n1++" "++show n2++"\n") []]
                )++
     [ translateRestriction mdl rvar outmp inmp restr
     | (var,restr) <- Map.toList (fst $ vars st), let (mdl,rvar) = f var ] ++
     [prIf [ (case snd $ vars (buchi!(s1,s2)) of
                 Nothing -> []
                 Just cond -> [Pr.StmtExpr $ Pr.ExprAny cond])++
             [Pr.StmtGoto $ "st_"++show s1++"_"++show s2]
           | (s1,s2) <- Set.toList $ successors st]]
    )

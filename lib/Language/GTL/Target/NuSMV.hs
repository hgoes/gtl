{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
{-| Implements the native NuSMV target. -}
module Language.GTL.Target.NuSMV 
       (verifyModel) where

import Language.GTL.Model
import Language.GTL.Buchi
import Language.GTL.Types
import Language.GTL.LTL as LTL
import Language.GTL.Expression as E
import Language.GTL.Translation
import Language.NuSMV.Syntax as S
import Language.NuSMV.Misc as S
import Language.NuSMV.Pretty as S

import System.Process

import Data.Map as Map hiding (foldl)
import Data.List as List
import Data.Maybe
import Prelude hiding (foldl,foldl1,mapM)

-- | Do a comp lete verification of a given GTL file
verifyModel :: --Opts.Options -- ^ Options
               -- String -- ^ Name of the GTL file without extension
                GTLSpec String -- ^ The GTL file contents
               -> IO ()
verifyModel spec = do
  let modules = translateSpec spec
  --traceFiles <- runVerification opts name pr
  --parseTraces opts name traceFiles (traceToAtoms model)
  --putStrLn $ show ltlSpec
  (exitCode,out,err) <- readProcessWithExitCode "NuSMV" [] (show $ prettyProgram modules) 
  putStrLn $ show $ prettyProgram modules
  putStrLn $ show exitCode
  putStrLn out
  putStrLn err

translateSpec :: GTLSpec String -> [S.Module]
translateSpec spec = [
  S.Module {
     moduleName = mname
   , moduleParameter = [ 
       "param_"++inp
     | (inp,_) <- Map.toList $ gtlModelInput m
     ]
   , moduleBody = translateModel m
  }
 | (name, inst) <- Map.toList $ gtlSpecInstances spec
 , let mname = gtlInstanceModel inst 
       m = (gtlSpecModels spec)!mname
 ]++
 [buildMainModule spec]

translateModel :: GTLModel String -> [ModuleElement]
translateModel m = [VarDeclaration $ 
 [
   (name, translateVarType tp)
 | (name, tp) <- Map.toList $ gtlModelInput m
 ]
 ++
 [
   (name, translateVarType tp)
 | (name, tp) <- Map.toList $ gtlModelOutput m
 ]
 ++[(genBAEnum $ gtlModelContract m)]
 ]
 ++[AssignConstraint ([
     (InitAssign,ComplexId {
       idBase=Nothing
       ,idNavigation=[Left name]
      }
      ,ConstExpr $ (case val of
                     Just (Fix v) -> translateValue v
                     _ -> error "should not happen")
     )
     | (name,val) <- Map.toList $ gtlModelDefaults m
     , isJust val
    ]
    ++
    [(NextAssign, ComplexId {
                    idBase=Nothing
                    , idNavigation=[Left name]
                  },
                  ConstExpr $ ConstId ("param_"++name)) 
    | (name, _) <- Map.toList $ gtlModelInput m
    ])
 ]
 ++[TransConstraint $ translateContract $ gtlModelContract m]--[TransConstraint]

genBAEnum :: [GTLContract String] -> (String, TypeSpecifier)
genBAEnum contr = ("st", S.SimpleType $ S.TypeEnum [
                                           Right st
                                          | (st,_) <- Map.toList $ baTransitions buchi
                                          ]
                  )
  where 
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl

translateContract :: [GTLContract String] -> BasicExpr
--translateContract [] = ConstExpr $ ConstId ""
translateContract contr = head [
    BinExpr OpImpl 
      (BinExpr OpEq 
         (genIDExpr Nothing "st") 
         (ConstExpr $ ConstInteger st))
      (transT trans)
      -- genIDExpr Nothing (
      --                 (concat $ List.intersperse " \\or " [
      --                  createTrans trg cond
      --                 | (cond,trg) <- trans])))
  | (st, trans) <- Map.toList $ baTransitions buchi
 ] 
 where 
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl
    --[(String, TypedExpr String)] -> BasicExpr
    transT ((cond,trg):[]) = createTrans trg cond
    transT ((cond,trg):trans) = BinExpr S.OpOr (createTrans trg cond) (transT trans)

createTrans:: Integer -> [TypedExpr String] -> BasicExpr
createTrans trg cond = (cT cond (BinExpr S.OpEq (UnExpr S.OpNext (ConstExpr $ ConstId "st")) (ConstExpr $ ConstInteger trg) ))
 where
    cT (x:expr) nex = BinExpr S.OpAnd (transExpr x) (cT expr nex)
    cT ([]) nex = nex
    transExpr ex =(case getValue $ unfix ex of 
                     BinRelExpr rel l r -> BinExpr ((case rel of
                                                      BinLT -> S.OpLT
                                                      BinLTEq -> S.OpLTE
                                                      BinGT -> S.OpGT
                                                      BinGTEq -> S.OpGTE
                                                      BinEq -> S.OpEq
                                                      BinNEq -> S.OpNeq))
                                                   (transExpr l) 
                                                   (transExpr r)
                     BinBoolExpr rel l r -> BinExpr ((case rel of
                                                        E.And -> S.OpAnd
                                                        E.Or -> S.OpOr
                                                        E.Implies -> S.OpImpl
                                                        _ -> error "not supported"))
                                                    (transExpr l) 
                                                    (transExpr r)
                     Var v h _ -> genIDExpr Nothing (v++(if h==0 then "" else "["++show h++"]"))
                     Value v -> ConstExpr (case v of
		                                       GTLIntVal x -> ConstInteger x
		                                       GTLBoolVal x -> ConstBool x
		                                       GTLEnumVal x -> ConstId x)
                     BinIntExpr rel lhs rhs -> BinExpr ( (case rel of
								                                    E.OpPlus -> S.OpPlus
								                                    E.OpMinus -> S.OpMinus
								                                    _ -> error "not supported"))
							                                  (transExpr lhs)
							                                  (transExpr rhs)
                     UnBoolExpr op p -> UnExpr (case op of
                                                  E.Not -> S.OpNot
                                                  E.Always -> S.LTLO
                                                  E.Next ts -> S.LTLX
                                                  E.Finally ts -> S.LTLF)
                                               (transExpr p)
                     _ -> error "not supported"
--                     IndexExpr expr idx -> (transExpr expr)++ ("_{"++show idx++"}")
--                     Automaton buchi -> "autom"
--                     ClockReset x y -> "clock reset"
--                     ClockRef x -> "clockref"
--                     BuiltIn _ args -> "builtin"
                  )

{-where 
    stClause st trans = BinExpr OpImpl (genIDExpr Nothing st) (genTransProp trans)
    genTransProp trans = genIDExpr Nothing ""
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl
{--translateContract (x:xs) = ConstExpr $ ConstId $ transExpr $ gtlContractFormula x
--}
-}

translateValue :: GTLValue a -> Constant
translateValue (GTLIntVal x) = ConstInteger x
translateValue (GTLByteVal x) = ConstWord $ S.WordConstant {
   wcSigned=Just False
   ,wcBits=Just 8
   ,wcValue=fromIntegral x
 }
translateValue (GTLBoolVal x) = ConstBool x
--translateValue (GTLFloatVal x) = ConstWord $ WordConstant
translateValue (GTLEnumVal x) = ConstId x
--translateValue (GTLArrayVal xs) = GTLArrayVal (fmap mu xs)
--translateValue (GTLTupleVal xs) = GTLTupleVal (fmap mu xs)


translateVarType :: GTLType -> TypeSpecifier
translateVarType (Fix (GTLInt bits)) = SimpleType $
  TypeWord {
    typeWordSigned=Nothing
    ,typeWordBits=ConstExpr $ ConstInteger $ gtlTypeBits (Fix (GTLInt bits))
  }
translateVarType (Fix GTLBool) = SimpleType $ TypeBool

buildMainModule :: GTLSpec String -> S.Module
buildMainModule spec = S.Module {
   moduleName = "main"
 , moduleParameter = []
 , moduleBody = [VarDeclaration $ Prelude.concat [
   (fmap (\j -> case j of {Just a -> a}) 
         (Prelude.filter (\i -> case i of 
                                  Just _ -> True
                                  Nothing -> False
                         ) $ snd parm))
   ++[(name, ProcessType mname (fst parm))]
 | (name, inst) <- Map.toList $ gtlSpecInstances spec
 , let mname = gtlInstanceModel inst
       m = (gtlSpecModels spec)!mname
       conn = gtlSpecConnections spec
       parm = buildProcessParam name m conn
 ]]
 ++[LTLSpec $ buildLTLSpec (gtlToLTL Nothing (gtlSpecVerify spec)) 
 (\ (i, j) -> IdExpr ComplexId {idBase=Just i,idNavigation=[Left j]})]
}

buildLTLSpec :: (Show a) => LTL.LTL (TypedExpr a) -> (a -> BasicExpr) -> BasicExpr
buildLTLSpec (Atom e) f = case getValue $ unfix e of 
                           Var n _ _ -> f n
buildLTLSpec (Bin op (e1) (e2)) f = 
  BinExpr (case op of
             LTL.And -> S.OpAnd 
             LTL.Or -> S.OpOr 
             LTL.Until -> S.LTLU 
             LTL.UntilOp -> S.LTLV)
          (buildLTLSpec e1 f) (buildLTLSpec e2 f)
buildLTLSpec (Un op (e)) f = case op of
  LTL.Not -> UnExpr S.OpNot (buildLTLSpec e f)
buildLTLSpec (Ground b) f = ConstExpr $ ConstBool b

buildProcessParam :: String 
                     -> GTLModel String
                     -> [(GTLConnectionPoint String,GTLConnectionPoint String)] 
                     -> ([BasicExpr],[Maybe (String, TypeSpecifier)])
buildProcessParam instName m conns = (leftS glist,rightS glist)
  where 
      glist = [
        genNewArg
       | (vn,tp) <- Map.toList $ gtlModelInput m
       , let conArg = getConnectedProcess instName vn conns
             genNewArg = (if Prelude.null conArg then
                           (genIDExpr Nothing ("_"++vn), 
                            Just $ ("_"++vn, translateVarType tp))
                          else
                           (head conArg,Nothing))
       ]
      leftS (x:xs) = (fst x):(leftS xs)
      leftS [] = []
      rightS (x:xs) = (snd x):(rightS xs)
      rightS [] = []

getConnectedProcess :: String 
                  -> String
                  -> [(GTLConnectionPoint String,GTLConnectionPoint String)] 
                  -> [BasicExpr]
getConnectedProcess instName var conns = [
    genIDExpr (Just f) fv
    | ((GTLConnPt f fv fi), (GTLConnPt t tv _)) <- conns
    , instName == t
    , var == tv
  ]

genIDExpr :: Maybe String -> String -> BasicExpr
genIDExpr b v = case b of 
                  (Just e) -> IdExpr ComplexId {
                                 idBase = b
                                 , idNavigation = [Left v] 
                              }
                  Nothing -> ConstExpr $ ConstId v


{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
{-| Implements the native Promela target. -}
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

import Data.Map as Map hiding (foldl)
import Data.List as List
import Data.Maybe
import Prelude hiding (foldl,foldl1,mapM)

-- | Do a comp lete verification of a given GTL file
verifyModel :: --Opts.Options -- ^ Options
               -- -> String -- ^ Name of the GTL file without extension
               GTLSpec String -- ^ The GTL file contents
               -> IO ()
verifyModel spec = do
  let modules = translateSpec spec
  --traceFiles <- runVerification opts name pr
  --parseTraces opts name traceFiles (traceToAtoms model)
  --putStrLn $ show ltlSpec
  putStrLn $ show $ prettyProgram modules

translateSpec :: GTLSpec String -> [S.Module]
translateSpec spec = [
  S.Module {
     moduleName = mname
   , moduleParameter = [ 
       inp
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
translateModel m = [VarDeclaration $ [
   (name, translateVarType tp)
 | (name, tp) <- Map.toList $ gtlModelInput m
 ]
 ++[
   (name, translateVarType tp)
 | (name, tp) <- Map.toList $ gtlModelOutput m
 ]]
 ++[AssignConstraint [
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
 ]]
 ++[TransConstraint $ translateContract $ gtlModelContract m]--[TransConstraint]

translateContract :: [GTLContract String] -> BasicExpr
--translateContract [] = ConstExpr $ ConstId ""
translateContract contr = head [
    BinExpr OpImpl 
      (BinExpr OpEq 
         (genIDExpr Nothing "st") 
         (ConstExpr $ ConstInteger st))
      (genIDExpr Nothing (
                       (concat $ List.intersperse " \\or " [
                        createTrans trg cond
                       | (cond,trg) <- trans])))
  | (st, trans) <- Map.toList $ baTransitions buchi
 ] 
 where 
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl

createTrans:: Integer -> [TypedExpr String] -> String
createTrans trg cond = 
                          (((concat [
                            (transExpr n)++" \\land "
                            | (n) <- cond
                            ])
                          )++" next(st)="++(show trg))
 where
    transExpr ex = case getValue $ unfix ex of 
                     BinRelExpr rel l r -> (transExpr l) ++ 
						                         ((case rel of
                                               BinLT -> "<"
                                               BinLTEq -> "\\leq "
                                               BinGT -> ">"
                                               BinGTEq -> "\\geq "
                                               BinEq -> "="
                                               BinNEq -> "\neq "))++
                                           (transExpr r)
                     BinBoolExpr rel l r -> (transExpr l) ++
                                            (show rel) ++
                                            (transExpr r) 
                     Var v h _ -> (v++(if h==0 then "" else "["++show h++"]"))
                     Value v -> (case v of
		                             GTLIntVal x -> show x
		                             GTLBoolVal x -> show x
		                             GTLEnumVal x -> "\\textrm{"++x++"}")
                     BinIntExpr rel lhs rhs -> (transExpr lhs)++
							                          ( (case rel of
								                           E.OpPlus -> "+"
								                           E.OpMinus -> "-"
								                           E.OpMult -> "\\cdot "
								                           E.OpDiv -> "/"))
							                          ++(transExpr rhs)
                     UnBoolExpr op p -> (case op of
                                          E.Not -> "" 
                                          E.Always -> ""
                                          E.Next ts -> ""
                                          E.Finally ts -> "")++
                                        (transExpr p)
                     IndexExpr expr idx -> (transExpr expr)++ ("_{"++show idx++"}")
                     Automaton buchi -> "autom"
                     ClockReset x y -> "clock reset"
                     ClockRef x -> "clockref"
                     BuiltIn _ args -> "builtin"

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
 ++[LTLSpec $ buildLTLSpec $ gtlToLTL Nothing (gtlSpecVerify spec)]
}

buildLTLSpec :: (Show a) => LTL.LTL (TypedExpr a) -> BasicExpr
buildLTLSpec (Atom e) = ConstExpr $ ConstId $ show e
buildLTLSpec (Bin op (e1) (e2)) = case op of
  LTL.And -> BinExpr OpAnd (buildLTLSpec e1) (buildLTLSpec e2)
  LTL.Or -> BinExpr OpOr (buildLTLSpec e1) (buildLTLSpec e2)
  LTL.Until -> BinExpr LTLU (buildLTLSpec e1) (buildLTLSpec e2)
  LTL.UntilOp -> BinExpr LTLV (buildLTLSpec e1) (buildLTLSpec e2)
buildLTLSpec (Un op (e)) = case op of
  LTL.Not -> UnExpr OpNot (buildLTLSpec e)
buildLTLSpec (Ground b) = ConstExpr $ ConstBool b

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
genIDExpr b v = IdExpr ComplexId {
    idBase = b
    , idNavigation = [Left v] 
  }


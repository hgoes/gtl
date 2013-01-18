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
  let modules = transSpec spec
  (exitCode,out,err) <- readProcessWithExitCode "NuSMV" [] (show $ prettyProgram modules) 
  putStrLn $ show $ prettyProgram modules
  putStrLn $ show exitCode
  putStrLn out
  putStrLn err

transSpec :: GTLSpec String -> [S.Module]
transSpec spec = [
  S.Module {
     moduleName = mname
   , moduleParameter = []
   , moduleBody = transModel m
  }
 | (name, inst) <- Map.toList $ gtlSpecInstances spec
 , let mname = gtlInstanceModel inst 
       m = (gtlSpecModels spec)!mname
 ]++
 [buildMainModule spec]


transModel :: GTLModel String -> [ModuleElement]
transModel m = [VarDeclaration $ 
 [
   (name, transVarType tp)
 | (name, tp) <- Map.toList $ gtlModelInput m
 ]
 ++
 [
   (name, transVarType tp)
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
                     Just (Fix v) -> transValue v (Just vartp)
                     _ -> error "should not happen")
     )
     | (name,val) <- Map.toList $ gtlModelDefaults m
     , isJust val
     , let vartp = (gtlModelInput m)!name
    ]
    )
 ]
 ++[TransConstraint $ transContract $ gtlModelContract m]--[TransConstraint]

genBAEnum :: [GTLContract String] -> (String, TypeSpecifier)
genBAEnum contr = ("st", S.SimpleType $ S.TypeEnum [
                                           Right st
                                          | (st,_) <- Map.toList $ baTransitions buchi
                                          ]
                  )
  where 
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl

transContract :: [GTLContract String] -> BasicExpr
transContract contr = head [
    BinExpr OpImpl 
      (BinExpr OpEq 
         (ConstExpr $ ConstId "st")
         (ConstExpr $ ConstInteger st))
      (transT trans)
  | (st, trans) <- Map.toList $ baTransitions buchi
 ] 
 where 
    ltl = gtlToLTL Nothing (gtlContractExpression contr)
    buchi = ltl2ba ltl
    transT ((cond,trg):[]) = createTrans trg cond
    transT ((cond,trg):trans) = BinExpr S.OpOr (createTrans trg cond) (transT trans)

createTrans:: Integer -> [TypedExpr String] -> BasicExpr
createTrans trg cond = (cT cond (BinExpr S.OpEq (UnExpr S.OpNext (ConstExpr $ ConstId "st")) (ConstExpr $ ConstInteger trg) ))
 where
    cT (x:expr) nex = BinExpr S.OpAnd (transExpr x (\i -> ConstExpr $ ConstId i)) (cT expr nex)
    cT ([]) nex = nex

transExpr :: TypedExpr a -> (a -> BasicExpr) -> BasicExpr
transExpr ex f = (case getValue $ unfix ex of 
                   BinRelExpr rel l r -> BinExpr (transRel rel)
                                                 (transExpr l f) 
                                                 (transExpr r f)
                   BinBoolExpr rel l r -> BinExpr (transBoolOp rel)
                                                  (transExpr l f) 
                                                  (transExpr r f)
                   Var v h _ -> f v
                   Value v -> ConstExpr (case v of
		                                     GTLIntVal x -> transIntValue x ex
		                                     GTLBoolVal x -> ConstBool x
		                                     GTLEnumVal x -> ConstId x)
                   BinIntExpr rel lhs rhs -> BinExpr (transIntOp rel)
					                                      (transExpr lhs f)
					                                      (transExpr rhs f)
                   UnBoolExpr op p -> UnExpr (transUnOp op)
                                             (transExpr p f)
                   IndexExpr r i -> error "IndexExpr"
                   Automaton ba -> error "ba"
                   ClockReset ci cj -> error "ClockReset"
                   ClockRef i -> error "ClockRef"
                   _ -> error "not supported (transExpr)"
              )

transIntValue :: Integer -> TypedExpr a -> Constant
transIntValue v ex = ConstWord $ WordConstant {
                                   wcSigned=Just False
                                   ,wcBits=Just bits
                                   ,wcValue=fromIntegral v
                                 }
 where 
   bits = gtlTypeBits (getType $ unfix ex)

transIntOp :: E.IntOp -> S.BinOp
transIntOp op = case op of
                  E.OpPlus -> S.OpPlus
                  E.OpMinus -> S.OpMinus
                  _ -> error "not supported (transIntOp)"
                  

transBoolOp :: E.BoolOp -> S.BinOp
transBoolOp op = case op of
                   E.And -> S.OpAnd
                   E.Or -> S.OpOr
                   E.Implies -> S.OpImpl
                   _ -> error "not supported (transBoolOp)"

transUnOp :: E.UnBoolOp -> S.UnOp
transUnOp op = case op of
                    E.Not -> S.OpNot
                    E.Always -> S.LTLO
                    E.Next ts -> S.LTLX
                    E.Finally ts -> S.LTLF

transRel :: E.Relation -> S.BinOp
transRel rel = case rel of
                 BinLT -> S.OpLT
                 BinLTEq -> S.OpLTE
                 BinGT -> S.OpGT
                 BinGTEq -> S.OpGTE
                 BinEq -> S.OpEq
                 BinNEq -> S.OpNeq

transValue :: GTLValue a -> Maybe GTLType -> Constant
transValue (GTLIntVal x) (Just t) = ConstWord $ S.WordConstant {
   wcSigned=Just False
   ,wcBits=Just $ gtlTypeBits t
   ,wcValue=fromIntegral x
}
transValue (GTLByteVal x) _ = ConstWord $ S.WordConstant {
   wcSigned=Just False
   ,wcBits=Just 8
   ,wcValue=fromIntegral x
 }
transValue (GTLBoolVal x) _ = ConstBool x
transValue (GTLEnumVal x) _ = ConstId x


transVarType :: GTLType -> TypeSpecifier
transVarType (Fix (GTLInt bits)) = SimpleType $
  TypeWord {
    typeWordSigned=Nothing
    ,typeWordBits=ConstExpr $ ConstInteger $ gtlTypeBits (Fix (GTLInt bits))
  }
transVarType (Fix GTLBool) = SimpleType $ TypeBool

buildMainModule :: GTLSpec String -> S.Module
buildMainModule spec = S.Module {
   moduleName = "main"
 , moduleParameter = []
 , moduleBody = [
   VarDeclaration $ Prelude.concat [
     [
      fromJust v
     | v <- varDecl
     , isJust v
     ]
     ++[(name, ProcessType mname [])
        | (name, inst) <- Map.toList $ gtlSpecInstances spec
        , let mname = gtlInstanceModel inst]
   ]]
 ++[AssignConstraint assignDecl]
 ++[LTLSpec $ buildLTLSpec (gtlToLTL Nothing (gtlSpecVerify spec)) 
 (\ (i, j) -> IdExpr ComplexId {idBase=Just i,idNavigation=[Left j]})]
 }
 where
   varList = buildMainVar spec
   varDecl = fst varList
   assignDecl = snd varList


buildLTLSpec :: (Show a) => LTL.LTL (TypedExpr a) -> (a -> BasicExpr) -> BasicExpr
buildLTLSpec (Atom e) f = transExpr e f 
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
buildLTLSpec l _ = error $ "Error: " ++ (show l)

buildMainVar :: GTLSpec String
                -> ([Maybe (String, TypeSpecifier)],[(AssignType, ComplexIdentifier, BasicExpr)])
buildMainVar spec = con $ unzip [  
       buildInputParam name m conn
 | (name, inst) <- Map.toList $ gtlSpecInstances spec
 , let mname = gtlInstanceModel inst
       m = (gtlSpecModels spec)!mname
       conn = gtlSpecConnections spec
 ]
 where 
   con (x,y) = (concat x, concat y)

buildInputParam :: String 
                     -> GTLModel String
                     -> [(GTLConnectionPoint String,GTLConnectionPoint String)] 
                     -> ([Maybe (String, TypeSpecifier)],[(AssignType, ComplexIdentifier, BasicExpr)])
buildInputParam instName m conns = (leftS glist,rightS glist)
  where 
    glist = [
              genNewArg
             | (vn,tp) <- Map.toList $ gtlModelInput m
             , let conArg = getConnectedProcess instName vn conns
                   genNewArg = (if Prelude.null conArg then
                                  (Just ("_"++vn, transVarType tp)
                                   ,(NextAssign
                                     ,ComplexId {
                                        idBase=Just instName
                                        ,idNavigation=[Left vn]
                                      }
                                     ,ConstExpr $ ConstId ("_"++vn)
                                    )
                                  )
                                else
                                  (Nothing
                                   ,(NextAssign
                                     ,ComplexId {
                                        idBase=Just instName
                                        ,idNavigation=[Left vn]
                                      }
                                     ,head conArg
                                    )
                                  )
                               )
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
     IdExpr ComplexId {
       idBase = Just f
       , idNavigation = [Left fv] 
     }
    | ((GTLConnPt f fv fi), (GTLConnPt t tv _)) <- conns
    , instName == t
    , var == tv
  ]

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
import System.Exit

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
  putStrLn ""
  putStrLn ">>>>>>>>>>>>>>>>>>>Stdout<<<<<<<<<<<<<<<<<<<"
  putStrLn ""
  putStrLn out
  putStrLn ""
  case exitCode of
    ExitFailure i -> do
      putStrLn $ ">>>>>>>>>>>>>>>>>>>ERROR ("++
         (show exitCode)++")<<<<<<<<<<<<<<<<<<<"
      putStrLn err
      putStrLn ""
    ExitSuccess -> do 
      putStr  ""
  putStrLn ">>>>>>>>>>>>>>>>>>>Debug: SMV-Model<<<<<<<<<<<<<<<<<<<"
  putStrLn ""
  putStrLn $ show $ prettyProgram modules
      
transSpec :: GTLSpec String -> [S.Module]
transSpec spec = [
  S.Module {
     moduleName = name
   , moduleParameter = []
   , moduleBody = transModel m
  }
 | (name, m) <- Map.toList $ gtlSpecModels spec
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
        ,idNavigation=[Left n]
       }
       ,bexpr
      )
     | (name,val) <- Map.toList $ gtlModelDefaults m
     , (bexpr,n) <- let vartp = (Map.union (gtlModelInput m) (gtlModelOutput m))!name
                    in (transAssign name vartp val)
     , isJust val
    ]
    )
 ]
 ++[TransConstraint $ transContract $ gtlModelContract m]

transAssign :: String -> GTLType -> Maybe GTLConstant -> [(BasicExpr,String)]
transAssign trg tp val = case val of
   Just exp -> case unfix exp of 
                 GTLArrayVal x -> rollAr x (\i -> ConstExpr $ ConstId $ i) 0
                 _ -> [(transConst tp exp (\i -> ConstExpr $ ConstId i), trg)]
   _ -> error "should not happen"
 where
   rollAr :: [GTLConstant] 
             -> (a -> BasicExpr) -> Integer 
             -> [(BasicExpr,String)]
   rollAr ([]) f idx = []
   rollAr (x:xs) f idx = (
      transConst tp x f,
      trg++"["++(show idx)++"]"
    ):(rollAr xs f (idx+1))

transConst:: GTLType -> GTLConstant -> 
             (a -> BasicExpr) -> BasicExpr
transConst tp c f = case unfix c of
    GTLIntVal x -> ConstExpr $ transIntValue x tp
    GTLByteVal x -> word 8 (fromIntegral x)
    GTLBoolVal x -> ConstExpr $ ConstBool x
    GTLFloatVal x -> error "no float type in smv"
    GTLEnumVal x ->  ConstExpr $ ConstId x
    GTLArrayVal x -> SetExpr $ handle x f
    GTLTupleVal x -> SetExpr $ handle x f
 where
    handle :: [GTLConstant] -> (a -> BasicExpr) -> [BasicExpr]
    handle ([]) f = []
    handle (x:xs) f = (transConst tp x f):(handle xs f)
    word b x = ConstExpr $ ConstWord $ WordConstant {
      wcSigned=Nothing
      ,wcBits=Just b
      ,wcValue=x
     }

genBAEnum :: [GTLContract String] -> (String, TypeSpecifier)
genBAEnum contr = ("smv_st", S.SimpleType $ S.TypeEnum [
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
         (ConstExpr $ ConstId "smv_st")
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
createTrans trg cond = (cT (cTT cond) (BinExpr S.OpEq (UnExpr S.OpNext (ConstExpr $ ConstId "smv_st")) (ConstExpr $ ConstInteger trg) ))
 where
    cTT ([]) = []
    cTT (x:[]) = case getValue $ unfix x of
                   ClockReset _ _ -> []
                   ClockRef _ -> []
                   _ -> (transExpr x (\i -> ConstExpr $ ConstId i)):[]
                 
    cTT (x:y:expr) = (genBinExpr S.OpAnd x y (\i -> ConstExpr $ ConstId i)):(cTT expr)
    cT (x:expr) nex = BinExpr S.OpAnd x (cT expr nex)
    cT ([]) nex = nex

transExpr :: TypedExpr a -> (a -> BasicExpr) -> BasicExpr
transExpr ex f = (case getValue $ unfix ex of 
                   BinRelExpr rel l r -> 
                     genBinExpr (transRel rel) l r f
                   BinBoolExpr op l r -> 
                     genBinExpr (transBoolOp op) l r f
                   Var v h _ -> f v
                   Value v -> case getConstant ex of
                     Just c -> transConst (getType $ unfix ex) c f
                     Nothing -> error "must be a constant"
                   BinIntExpr op l r -> 
                     genBinExpr (transIntOp op) l r f
                   UnBoolExpr op p -> UnExpr (transUnOp op)
                                             (transExpr p f)
                   --FIXME index access???
                   IndexExpr v i -> 
                     transExpr v (\j -> case f j of
                                          ConstExpr (ConstId x) -> ConstExpr $ ConstId (x++("[" ++ (show i) ++ "]")))
                   Automaton ba -> error "ba"
                   ClockReset ci cj -> ConstExpr $ ConstId "ClockReset"
                   ClockRef i -> ConstExpr $ ConstId "ClockRef"
                   _ -> error "not supported (transExpr)"
              )

genBinExpr :: S.BinOp ->
              TypedExpr a -> 
              TypedExpr a -> 
              (a -> BasicExpr) ->
              BasicExpr
genBinExpr op l r f = case getValue $ unfix r of
                       ClockReset _ _ -> transExpr l f
                       ClockRef _ -> transExpr l f
                       _ -> case getValue $ unfix l of
                         ClockReset _ _ -> transExpr r f
                         ClockRef _ -> transExpr r f 
                         _ -> BinExpr op
                                    (transExpr l f) 
                                    (transExpr r f)

transIntValue :: Integer -> GTLType -> Constant
transIntValue v tp = ConstWord $ WordConstant {
                                   wcSigned=Just False
                                   ,wcBits=Just $ gtlTypeBits tp
                                   ,wcValue=fromIntegral v
                                 }
 where 
   bits = gtlTypeBits tp

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

transVarType :: GTLType -> TypeSpecifier
transVarType tp = SimpleType $ transSimpleType tp
 where
  transSimpleType (Fix (GTLInt bits)) = TypeWord {
    typeWordSigned=Nothing
    ,typeWordBits=ConstExpr $ ConstInteger $ gtlTypeBits (Fix (GTLInt bits))
  }
  transSimpleType (Fix GTLBool) = TypeBool
  transSimpleType (Fix GTLByte) = TypeWord {
   typeWordSigned=Nothing
   ,typeWordBits=ConstExpr $ ConstInteger $ gtlTypeBits (Fix GTLByte)
  }
  transSimpleType (Fix (GTLEnum enums)) = TypeEnum (enumList enums)
  transSimpleType (Fix (GTLArray i tp)) = TypeArray 
   (ConstExpr $ ConstInteger 0) (ConstExpr $ ConstInteger i)
   (transSimpleType tp)
  enumList (x:xs) = (Left x):(enumList xs)
  enumList [] = []

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
             ,    genNewArg <- (if Prelude.null conArg then
                                  [(Just ("_"++vn, transVarType tp)
                                   ,(NextAssign
                                     ,ComplexId {
                                        idBase=Just instName
                                        ,idNavigation=[Left vn]
                                      }
                                     ,ConstExpr $ ConstId ("_"++vn)
                                    )
                                  )]
                                else
                                  [(Nothing
                                   ,(NextAssign
                                     ,y
                                     ,IdExpr x
                                    )
                                  )
                                  | (x,y) <- conArg
                                  ]
                               )
            ]
    leftS (x:xs) = (fst x):(leftS xs)
    leftS [] = []
    rightS (x:xs) = (snd x):(rightS xs)
    rightS [] = []

getConnectedProcess :: String
                  -> String
                  -> [(GTLConnectionPoint String,GTLConnectionPoint String)] 
                  -> [(ComplexIdentifier, ComplexIdentifier)]
getConnectedProcess instName var conns = [
    (ComplexId {
       idBase = Just f
       , idNavigation = [Left (fv ++ (extfi fi))] 
     },
     ComplexId {
       idBase = Just t
       , idNavigation = [Left (tv ++ (extfi ti))] 
     })
    | ((GTLConnPt f fv fi), (GTLConnPt t tv ti)) <- conns
    , instName == t
    , var == tv
  ]
 where
   extfi ([]) = ""
   extfi (x:xs) = "["++(show x)++"]"

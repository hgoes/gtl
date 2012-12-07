{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
{-| Implements the native Promela target. -}
module Language.GTL.Target.NuSMV 
       (verifyModel) where

import Language.GTL.Model
import Language.GTL.LTL as LTL
import Language.GTL.Expression
import Language.NuSMV.Syntax as S
import Language.NuSMV.Pretty as S
import Language.GTL.Translation

import Data.Map as Map hiding (foldl)
import Prelude hiding (foldl,concat,foldl1,mapM)

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

translateModel :: GTLModel a -> [ModuleElement]
translateModel m = []--VarDeclaration [
{--  (outp
   , SimpleType $ TypeWord {typeWordSigned = False, typeWordBits = ConstExpr $ ConstId "?"}
| (outp, tp) <- Map.toList $ gtlModelOutput m
]++
[
 InitConstraint (BasicExpr inp v)
| (inp, v) <- Map.toList $ gtlModelDefaults m
]--}

buildMainModule :: GTLSpec String -> S.Module
buildMainModule spec = S.Module {
   moduleName = "main"
 , moduleParameter = []
 , moduleBody = [VarDeclaration [
   (name, ProcessType mname (buildProcessParam name conn))
 | (name, inst) <- Map.toList $ gtlSpecInstances spec
 , let mname = gtlInstanceModel inst
       m = (gtlSpecModels spec)!mname
       conn = gtlSpecConnections spec
 ]]++[LTLSpec $ buildLTLSpec $ gtlToLTL Nothing (gtlSpecVerify spec)]
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
                     -> [(GTLConnectionPoint String,GTLConnectionPoint String)] 
                     -> [BasicExpr] 
{--buildProcessParam n (((GTLConnPt f fv fi), _):xs) = ( -- nur links weil p.x -> c.ix also p schreibt in ix aber nicht ix in p.x somit nur left betrachten
 ):(buildProcessParam n xs)
buildProcessParam n [] = []--}
buildProcessParam n conns = [
  IdExpr ComplexId {
    idBase = Just f
    , idNavigation = [Left fv] -- TODO fv into String
  }
 | ((GTLConnPt f fv fi), (GTLConnPt t _ _)) <- conns
 , n == t
 ]


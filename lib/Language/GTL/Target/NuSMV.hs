{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
{-| Implements the native Promela target. -}
module Language.GTL.Target.NuSMV 
       (verifyModel) where

import Language.GTL.Model
import Language.NuSMV.Syntax as S
import Language.NuSMV.Pretty as S
import Language.GTL.Target.Common
import Language.GTL.Translation

import Data.Set as Set hiding (foldl)
import Data.Map as Map hiding (foldl)
import Data.List (elemIndex,genericLength,genericIndex)
import Data.Foldable
import Prelude hiding (foldl,concat,foldl1,mapM)
import Data.Maybe
import Data.Int

import Misc.ProgramOptions as Opts
import Misc.VerificationEnvironment

-- | Do a complete verification of a given GTL file
verifyModel :: --Opts.Options -- ^ Options
               -- -> String -- ^ Name of the GTL file without extension
               GTLSpec String -- ^ The GTL file contents
               -> IO ()
verifyModel spec = do
  let modules = translateSpec spec
      ltlSpec = gtlToLTL Nothing (gtlSpecVerify spec)
  --traceFiles <- runVerification opts name pr
  --parseTraces opts name traceFiles (traceToAtoms model)
  putStrLn $ show ltlSpec
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
translateModel m = []

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
 ]]
}

buildProcessParam :: String 
                     -> [(GTLConnectionPoint a,GTLConnectionPoint a)] 
                     -> [BasicExpr] 
buildProcessParam n (((GTLConnPt f fv fi), (GTLConnPt t tv ti)):xs) = (IdExpr ComplexId {
  idBase = Just f
  , idNavigation = [Left "fv"] -- TODO fv into String
 }):[]
buildProcessParam n [] = []


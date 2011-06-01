{-# LANGUAGE GADTs #-}
{-| Verifies a GTL specification by converting the components to C-code and
    simulating all possible runs.
 -}
module Language.GTL.Target.PromelaKCG where

import Language.GTL.Expression as GTL
import Language.GTL.Model
import Language.GTL.Backend
import Language.GTL.Backend.All
import Language.GTL.ErrorRefiner
import Language.GTL.Translation
import Language.GTL.LTL

import qualified Language.Promela.Syntax as Pr
import qualified Language.Scade.Syntax as Sc
import Language.Promela.Pretty

import Data.Map (Map,(!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (mapMaybe)
import Data.Bits

-- | Compile a GTL declaration into a promela module simulating the specified model.
--   Optionally takes a trace that is used to restrict the execution.
--   Outputs promela code.
translateGTL :: Maybe FilePath -- ^ An optional path to a trace file
                -> GTLSpec String -- ^ The GTL code
                -> IO String
translateGTL traces gtlcode
  = do
    rtr <- case traces of
      Nothing -> return []
      Just tr -> readBDDTraces tr
    let claims = [neverClaim (case rtr of
                                 [] -> []
                                 x:_ -> x) (gtlSpecVerify gtlcode) (gtlSpecModels gtlcode)]
    return $ show $ prettyPromela $ (generatePromelaCode gtlcode (maximumHistory (gtlSpecVerify gtlcode)))++claims

-- | Convert a GTL name into a C-name.
varName :: CInterface
           -> String -- ^ The component name
           -> String -- ^ The variable name
           -> Integer -- ^ The history level of the variable
           -> String
varName iface q v lvl = if lvl==0
                        then cIFaceGetOutputVar iface (stateVars q iface) v
                        else "now.history_"++q++"_"++v++"_"++show lvl

stateVars :: String
             -> CInterface
             -> [String]
stateVars mdl iface = zipWith (\i _ -> "now.state_"++mdl++show i) [0..] (cIFaceStateType iface)

inputVars :: String
             -> CInterface
             -> [String]
inputVars mdl iface = zipWith (\i _ -> "input_"++mdl++show i) [0..] (cIFaceInputType iface)

-- | Convert a trace and a verify expression into a promela never claim.
--   If you don't want to include a trace, give an empty one `[]'.
neverClaim :: Trace -- ^ The trace
              -> TypedExpr (String,String) -- ^ The verify expression
              -> Map String (GTLModel String) -- ^ All models
              -> Pr.Module
neverClaim trace f mdls
  = let traceAut = traceToBuchi (\q v l -> let iface = allCInterface $ gtlModelBackend (mdls!q)
                                           in varName iface q v l) trace
        states = Map.toList $ translateGBA $ buchiProduct (ltlToBuchi distributeNot $ gtlToLTL $ gnot f) traceAut
        showSt ((i,j),k) = show i++ "_"++show j++"_"++show k
        init = Pr.prIf [ [Pr.StmtGoto $ "st"++showSt i]  | (i,st) <- states, isStart st ]
        steps = [ Pr.StmtLabel ("st"++showSt i)
                  (let cexprr = case snd (vars st) of
                         Nothing -> []
                         Just e -> [e]
                       inner = case cexprl ++ cexprr of
                         [] -> jump
                         cexprs -> Pr.prSequence
                                   [Pr.StmtCExpr Nothing $ foldl1 (\x y -> x++"&&"++y) cexprs
                                   ,jump]
                       jump = Pr.prIf
                              [ [Pr.StmtGoto $ "st"++showSt j]
                              | j <- Set.toList (successors st)]
                              
                       cexprl = [ atomToC (\q v l -> let iface = allCInterface $ gtlModelBackend (mdls!q)
                                                     in varName iface q v l) ratom
                                | (atom,en) <- Set.toList $ fst $ vars st,
                                  let ratom = if en then atom else distributeNot atom ]
                   in if finalSets st
                      then Pr.StmtLabel ("accept"++showSt i) inner
                      else inner)
                | (i,st) <- states ]
    in Pr.prNever $ [init]++steps


-- | Create promela processes for each component in a GTL specification.
generatePromelaCode :: GTLSpec String -> Map (String,String) Integer -> [Pr.Module]
generatePromelaCode spec history
  = let procs = fmap (\(name,mdl) -> let iface = allCInterface (gtlModelBackend mdl)
                                         steps = [Pr.StepStmt (Pr.prDo [[Pr.StmtCCode $ unlines $
                                                                         [ varName iface name v lvl++" = "++
                                                                           varName iface name v (lvl-1)++";"
                                                                         | ((q,v),mlvl) <- Map.toList history
                                                                         , q == name
                                                                         , lvl <- reverse [1..mlvl]
                                                                         ]++
                                                                         [ cIFaceGetInputVar iface (inputVars name iface) tvar ++ " = " ++
                                                                           source ++ ";"
                                                                         | (GTLConnPt fmod fvar [],GTLConnPt tmod tvar []) <- gtlSpecConnections spec
                                                                         , tmod == name
                                                                         , let siface = allCInterface $ gtlModelBackend $ (gtlSpecModels spec)!fmod
                                                                               source = cIFaceGetOutputVar siface (stateVars fmod siface) fvar
                                                                         ]++
                                                                         [ cIFaceIterate iface (stateVars name iface) (inputVars name iface) ++ ";"
                                                                         ]
                                                                        ]
                                                                       ]) Nothing
                                                 ]
                                     in Pr.ProcType { Pr.proctypeActive = Nothing
                                                    , Pr.proctypeName = name
                                                    , Pr.proctypeArguments = []
                                                    , Pr.proctypePriority = Nothing
                                                    , Pr.proctypeProvided = Nothing
                                                    , Pr.proctypeSteps = steps
                                                    }
                     ) (Map.toList (gtlSpecModels spec))
        states = [ Pr.CState (tp++" state_"++name++show i) "Global" Nothing
                 | (name,mdl) <- Map.toList (gtlSpecModels spec) 
                 , (i,tp) <- zip [0..] $ cIFaceStateType (allCInterface $ gtlModelBackend mdl) ] ++
                 [ Pr.CState (tp++" history_"++q++"_"++n++"_"++show clvl) "Global" (Just "0")
                 | ((q,n),lvl) <- Map.toList history
                 , let mdl = (gtlSpecModels spec)!q
                       dtp = case Map.lookup n (gtlModelInput mdl) of
                         Nothing -> (gtlModelOutput mdl)!n
                         Just t -> t
                       tp = cIFaceTranslateType (allCInterface $ gtlModelBackend mdl) dtp
                 , clvl <- [1..lvl]
                 ]
        inp_decls = [Pr.CDecl $ unlines $
                     ["\\#include <"++incl++">"
                     | mdl <- Map.elems (gtlSpecModels spec)
                     , incl <- cIFaceIncludes (allCInterface $ gtlModelBackend mdl)
                     ] ++
                     [ tp++" input_"++name++show i++";"
                     | (name,mdl) <- Map.toList (gtlSpecModels spec)
                     , (i,tp) <- zip [0..] (cIFaceInputType (allCInterface $ gtlModelBackend mdl))
                     ]
                    ]
        init = [Pr.prInit ([Pr.StmtCCode $ unlines $
                            [ cIFaceStateInit iface (stateVars name iface) ++ ";"
                            | (name,mdl) <- Map.toList (gtlSpecModels spec)
                            , let iface = allCInterface $ gtlModelBackend mdl
                            ]++
                            [ cIFaceGetInputVar iface (stateVars name iface) var ++ "=" ++ cIFaceTranslateValue iface val++";"
                            | (name,mdl) <- Map.toList (gtlSpecModels spec)
                            , let iface = allCInterface $ gtlModelBackend mdl
                            , (var,Just val) <- Map.toList (gtlModelDefaults mdl)
                            ]
                           ,Pr.prAtomic
                            [Pr.StmtExpr $ Pr.ExprAny $ Pr.RunExpr name [] Nothing
                            | name <- Map.keys $ gtlSpecModels spec]
                           ])]
    in inp_decls ++ states ++ procs ++ init

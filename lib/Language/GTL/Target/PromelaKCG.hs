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
import Language.GTL.Buchi
import Language.GTL.LTL

import qualified Language.Promela.Syntax as Pr
import Language.Promela.Pretty

import Data.Map (Map,(!))
import qualified Data.Map as Map
import qualified Data.Set as Set

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
                                 x:_ -> x) gtlcode]
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
              -> GTLSpec String
              -> Pr.Module
neverClaim trace spec
  = let cname q v l = let Just inst = Map.lookup q (gtlSpecInstances spec)
                          Just mdl = Map.lookup (gtlInstanceModel inst) (gtlSpecModels spec)
                          iface = allCInterface (gtlModelBackend mdl)
                      in varName iface q v l
        traceAut = traceToBuchi trace
        allAut = baMapAlphabet (\exprs -> case fmap (atomToC cname) exprs of
                                   [] -> Nothing
                                   cs -> Just $ Pr.StmtCExpr Nothing $ foldl1 (\x y -> x++"&&"++y) cs
                               ) $ renameStates $ baProduct (gtl2ba Nothing (gnot $ gtlSpecVerify spec)) traceAut
        
        init = Pr.prIf [ [ Pr.prAtomic $ (case cond of
                                             Nothing -> []
                                             Just p -> [p])++[Pr.StmtGoto ("st"++show trg)] ]
                       | st <- Set.toList (baInits allAut),
                         let ts = (baTransitions allAut)!st,
                         (cond,trg) <- ts
                       ]
        sts = [ Pr.StmtLabel ("st"++show st) $ (\x -> if Set.member st (baFinals allAut)
                                                      then Pr.StmtLabel ("accept"++show st) x
                                                      else x) $
                Pr.prIf [ [ Pr.prAtomic $ (case cond of
                                              Nothing -> []
                                              Just p -> [p]) ++ [Pr.StmtGoto ("st"++show trg)] ]
                        | (cond,trg) <- ts ]
              | (st,ts) <- Map.toList (baTransitions allAut)]
    in Pr.prNever $ init:sts


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
                         Nothing -> let Just t = Map.lookup n (gtlModelOutput mdl) in t
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

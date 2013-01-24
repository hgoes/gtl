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
import Language.GTL.Types

import qualified Language.Promela.Syntax as Pr
import Language.Promela.Pretty

import Data.Map (Map,(!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Data.List (nub)

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
                                 x:_ -> x) False gtlcode]
    return $ show $ prettyPromela $ (generatePromelaCode gtlcode (maximumHistory (gtlSpecVerify gtlcode)))++claims

-- | Convert a GTL name into a C-name.
varName :: CInterface
           -> String -- ^ The component name
           -> String -- ^ The variable name
           -> [Integer] -- ^ The indices of the variable
           -> Integer -- ^ The history level of the variable
           -> String
varName iface q v idx lvl = if lvl==0
                            then (case cIFaceGetOutputVar iface (fmap fst $ stateVars q iface) v idx of
                                     Nothing -> let Just res = cIFaceGetInputVar iface (fmap fst $ inputVars q iface) v idx
                                                in res
                                     Just res -> res)
                            else "now.history_"++q++"_"++v++"_"++show lvl++(case idx of
                                                                               [] -> ""
                                                                               _ -> concat $ fmap (\x -> "["++show x++"]") idx)

stateVars :: String
             -> CInterface
             -> [(String,Bool)]
stateVars mdl iface = zipWith (\i (_,_,ref) -> ("now.state_"++mdl++show i,ref)) [0..] (cIFaceStateType iface)

inputVars :: String
             -> CInterface
             -> [(String,Bool)]
inputVars mdl iface = zipWith (\i (_,(_,_,ref)) -> ("input_"++mdl++show i,ref)) [0..] (cIFaceInputType iface)

nondetAssign :: String -> GTLType -> Pr.Step
nondetAssign var tp = case unfix tp of
  GTLInt -> nondetAssignRange var (-9223372036854775808) 9223372036854775807
  GTLByte -> nondetAssignRange var (-128) 127
  GTLBool -> nondetAssignList var ["0","1"]
  GTLEnum vals -> nondetAssignList var vals
  GTLNamed _ r -> nondetAssign var r

nondetAssignRange :: String -> Integer -> Integer -> Pr.Step
nondetAssignRange var from to 
  = Pr.StepStmt
    (Pr.prSequence [Pr.StmtCCode (var++"="++show from++";")
                   ,Pr.prDo [[Pr.StmtCExpr Nothing (var++"<"++show to)
                             ,Pr.StmtCCode (var++"++;")
                             ]
                            ,[Pr.StmtBreak]
                            ]
                   ])
    Nothing

nondetAssignList :: String -> [String] -> Pr.Step
nondetAssignList var consts
  = Pr.StepStmt
    (Pr.prIf [ [Pr.StmtCCode (var++"="++c++";")]
             | c <- consts ])
    Nothing

-- | Convert a trace and a verify expression into a promela never claim.
--   If you don't want to include a trace, give an empty one `[]'.
neverClaim :: Trace -- ^ The trace
              -> Bool -- ^ Include the verification goal?
              -> GTLSpec String
              -> Pr.Module
neverClaim trace inc_ver spec
  = let origin = transOrigins spec
        cname q v i l = case Map.lookup (v,i) ((inputOrigins origin)!q) of
          Just o -> case o of
            Unconnected _ (_,_,indir) -> "now."++unconnectedInputName q v i
            Connected str -> "now."++str
            ConstantInput (CValue s) -> s
          Nothing -> let mdl = (gtlSpecModels spec)!(gtlInstanceModel $ (gtlSpecInstances spec)!q)
                         iface = allCInterface $ gtlModelBackend mdl
                     in if Map.member v (gtlModelOutput mdl)
                        then case cIFaceGetOutputVar iface (fmap ("now."++) $ stateVarNames q (cIFaceStateType iface)) v i of
                          Just res -> res
                        else error ("Instance "++q++" has no output variable called "++v++" ("++show i++")")
        traceAut = traceToBuchi trace
        verAut = gtl2ba Nothing (gnot $ gtlSpecVerify spec)
        
        allAut = baMapAlphabet (\exprs -> case fmap (atomToC cname [] . flattenExpr (\(q,n) idx -> (q,n,idx)) []) exprs of
                                   [] -> Nothing
                                   cs -> Just $ Pr.StmtCExpr Nothing $ foldl1 (\x y -> x++"&&"++y) cs
                               ) $
                 if inc_ver
                 then renameStates $ baProduct traceAut verAut
                 else traceAut
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

data TransOrigins = TransOrigins
                    { inputOrigins :: Map String (Map (String,[Integer]) InputOrigin)
                    }

data InputOrigin = Unconnected GTLType (String,String,Bool)
                 | Connected String
                 | ConstantInput CExpr

transOrigins :: GTLSpec String -> TransOrigins
transOrigins spec = TransOrigins
                    { inputOrigins = foldl add_conn empty_cons (gtlSpecConnections spec)
                    }
  where
    add_conn mp (GTLConnPt om ov oi,GTLConnPt im iv ii) 
      = let tp = getInstanceVariableType spec False om ov
        in case resolveIndices tp oi of
          Left err -> error err
          Right rtp -> foldl add_conn' mp (fmap (\(tp',idx) -> (om,ov,oi++idx,im,iv,ii++idx,tp')) $ allPossibleIdx rtp)
    add_conn' mp (om,ov,oi,im,iv,ii,tp) = let tinst = (gtlSpecInstances spec)!om
                                              tmdl = (gtlSpecModels spec)!(gtlInstanceModel tinst)
                                              tiface = allCInterface $ gtlModelBackend tmdl
                                              Just ostr = cIFaceGetOutputVar tiface (stateVarNames om (cIFaceStateType tiface)) ov oi
                                          in Map.adjust (Map.insert (iv,ii) (Connected ostr)) im mp
    empty_cons = Map.fromList [ (iname,Map.fromList [ ((vname,idx),case Map.lookup vname (gtlModelConstantInputs mdl) of
                                                          Nothing -> Unconnected tp' (cIFaceTranslateType iface tp')
                                                          Just (_,c) -> ConstantInput $ cIFaceTranslateValue iface c
                                                      )
                                                    | (vname,tp) <- Map.toList (gtlModelInput mdl)
                                                    , (tp',idx) <- allPossibleIdx tp ])
                              | (iname,inst) <- Map.toList (gtlSpecInstances spec)
                              , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                    iface = allCInterface $ gtlModelBackend mdl
                              ]

unconnectedInputName :: String -> String -> [Integer] -> String
unconnectedInputName inst var idx = "input_"++inst++"_"++var++concat (fmap (\i -> "_"++show i) idx)

stateVarNames :: String -> [(String,String,Bool)] -> [String]
stateVarNames name tps = zipWith (\tp i -> "state_"++name++"_"++show i) tps [0..]

stateArgs :: String -> CInterface -> [String]
stateArgs name iface = zipWith (\name' (_,_,indir) -> (if indir
                                                       then "&"
                                                       else "")++"now."++name') 
                       (stateVarNames name (cIFaceStateType iface))
                       (cIFaceStateType iface)

declareVar :: String -> (String,String,Bool) -> String
declareVar name (pre,post,indir) = pre++" "++name++post

declareUnconnectedInputs :: TransOrigins -> [Pr.Module]
declareUnconnectedInputs inps = [Pr.CState (pre++" "++unconnectedInputName inst var idx++post) "Global" Nothing
                                | (inst,vars) <- Map.toList (inputOrigins inps)
                                , ((var,idx),Unconnected _ (pre,post,indir)) <- Map.toList vars ]

declareStates :: GTLSpec String -> [Pr.Module]
declareStates spec = [Pr.CState decl "Global" Nothing
                     | (iname,inst) <- Map.toList (gtlSpecInstances spec)
                     , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                           tps = cIFaceStateType $ allCInterface $ gtlModelBackend mdl
                     , decl <- zipWith declareVar (stateVarNames iname tps) tps
                     ]

initializeStates :: GTLSpec String -> Pr.Step
initializeStates spec = Pr.StepStmt (Pr.StmtCCode $ unlines $
                        [ cIFaceStateInit iface (fmap ("now."++) (stateVarNames name $ cIFaceStateType iface)) ++ ";"
                        | (name,inst) <- Map.toList (gtlSpecInstances spec)
                        , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                              iface = allCInterface $ gtlModelBackend mdl
                        ]) Nothing

assignUnconnected :: String -> Map (String,[Integer]) InputOrigin -> [Pr.Step]
assignUnconnected iname inps 
  = [ nondetAssign ("now."++unconnectedInputName iname vname idx) tp
    | ((vname,idx),Unconnected tp _) <- Map.toList inps ]

stepInstance :: String -> GTLModel String -> Map (String,[Integer]) InputOrigin -> Pr.Step
stepInstance iname mdl inps
  = Pr.StepStmt (Pr.StmtCCode $ unlines $
                 [ pre++" local_"++vname++post++";"
                 | (vname,(pre,post,indir)) <- cIFaceInputType iface ] ++
                 [ case inp of
                      Unconnected _ _ -> tname ++ " = now." ++ unconnectedInputName iname vname idx ++ ";"
                      ConstantInput val -> mkAssign tname val
                      Connected ostr -> tname ++ " = now." ++ ostr ++ ";"
                 | ((vname,idx),inp) <- Map.toList inps
                 , let tname = "local_"++vname++
                               concat (fmap (\i -> "["++show i++"]") idx)
                 ]++
                 [ (cIFaceIterate iface
                    (zipWith (\name (_,_,indir) -> (if indir 
                                                    then "&"
                                                    else "")++"now."++name) 
                     (stateVarNames iname (cIFaceStateType iface))
                     (cIFaceStateType iface))
                    [ (if indir then "&" else "")++"local_"++vname 
                    | (vname,(_,_,indir)) <- cIFaceInputType iface ]
                   )++";" ]) Nothing
  where
    iface = allCInterface $ gtlModelBackend mdl

includeHeaders :: GTLSpec String -> Pr.Module
includeHeaders spec = Pr.CDecl $ unlines $ fmap (\inc -> "\\#include <"++inc++">") $ nub
                      [ inc
                      | (iname,inst) <- Map.toList (gtlSpecInstances spec) 
                      , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                            iface = allCInterface $ gtlModelBackend mdl
                      , inc <- cIFaceIncludes iface
                      ]

-- | Create promela processes for each component in a GTL specification.
generatePromelaCode :: GTLSpec String -> Map (String,String) Integer -> [Pr.Module]
generatePromelaCode spec _
  = [includeHeaders spec] ++
    declareUnconnectedInputs origins ++
    declareStates spec ++
    init_blk++
    step_blk
  where
    origins = transOrigins spec
    init_blk = [Pr.Init Nothing $ 
                [Pr.StepStmt (Pr.prAtomic $
                              [initializeStates spec] ++
                              [Pr.StepStmt (Pr.StmtRun ("proc_"++iname) []) Nothing
                              | iname <- Map.keys (gtlSpecInstances spec) ]) Nothing
                ]
               ]
    step_blk = [ Pr.ProcType { Pr.proctypeActive = Nothing
                             , Pr.proctypeName = "proc_"++iname
                             , Pr.proctypeArguments = []
                             , Pr.proctypePriority = Nothing
                             , Pr.proctypeProvided = Nothing
                             , Pr.proctypeSteps = [Pr.StepStmt (Pr.prDo [[Pr.prAtomic $ 
                                                                          (assignUnconnected iname orig)++
                                                                          [stepInstance iname mdl orig]]]) Nothing]
                             }
               | (iname,(inst,orig)) <- Map.toList (Map.intersectionWith (\x y -> (x,y)) (gtlSpecInstances spec) (inputOrigins origins))
               , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
               ]

mkAssign :: String -> CExpr -> String
mkAssign expr val = unlines (mkAssign' expr val)
  where
    mkAssign' :: String -> CExpr -> [String]
    mkAssign' expr (CValue x) = [expr++"="++x++";"]
    mkAssign' expr (CArray xs) = concat [ mkAssign' (expr++"["++show i++"]") x | (i,x) <- zip [0..] xs]
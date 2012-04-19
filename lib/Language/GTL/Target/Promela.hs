{- Miserere mei Deus
   secundum magnam
   misericordiam tuam
 -}
{-# LANGUAGE GADTs,ScopedTypeVariables #-}
{-| Implements the native Promela target. -}
module Language.GTL.Target.Promela 
       (verifyModel) where

import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.Promela.Syntax as Pr
import Language.GTL.Buchi
import Language.GTL.Types
import Language.GTL.Target.Common
import Language.GTL.ErrorRefiner
import Language.GTL.Restriction

import Control.Monad.Identity

import Data.Set as Set
import Data.Map as Map
import Data.List (elemIndex,genericLength,genericIndex)
import Data.Foldable
import Prelude hiding (foldl,concat,foldl1,mapM)
import Data.Maybe
import Data.Int

import Misc.ProgramOptions as Opts
import Misc.VerificationEnvironment

-- | Do a complete verification of a given GTL file
verifyModel :: Opts.Options -- ^ Options
               -> String -- ^ Name of the GTL file without extension
               -> GTLSpec String -- ^ The GTL file contents
               -> IO ()
verifyModel opts name spec = do
  let pr = translateSpec spec
      model = buildTargetModel spec
  traceFiles <- runVerification opts name pr
  parseTraces opts name traceFiles (traceToAtoms model)

-- | Given a list of transitions, give a list of atoms that have to hold for each transition.
traceToAtoms :: TargetModel -- ^ The program to work on
                -> [(String,Integer,Integer)] -- ^ The transitions, given in the form (model,state,transition-number)
                -> Trace
traceToAtoms model trace = fmap transitionToAtoms trace
  where
    transitionToAtoms :: (String,Integer,Integer) -> [TypedExpr (String, String)]
    transitionToAtoms (mdl,st,t) =
      let stateMachine = tprocAutomaton $ (tmodelProcs model)!mdl
          trans = (baTransitions stateMachine)!st
          (ats,_) = trans `genericIndex` t
      in tcOriginal ats

translateTarget :: Bool -> TargetModel -> [Pr.Module]
translateTarget use_ltl tm = var_decls ++ procs ++ init ++ verify
  where
    allP = Map.keys (tmodelProcs tm)
    var_decls = [ Pr.Decl $ Pr.Declaration Nothing (convertType tp) [(varString mdl var idx l,Nothing,case inits of
                                                                         Nothing -> Nothing
                                                                         Just dset -> Just $ translateConstant tp (unfix $ head $ Set.toList dset)
                                                                     )]
                | ((mdl,var,idx),lvl,tp,inits) <- tmodelVars tm,
                  l <- [0..lvl]
                ] ++
                (if Set.null clocks
                 then []
                 else [Pr.Decl $ Pr.Declaration Nothing TypeInt [ ("timer"++show clk,Nothing,Just $ Pr.ConstExpr $ Pr.ConstInt (-1)) | clk <- Set.toList clocks ]]) ++
                [ Pr.Decl $ Pr.Declaration Nothing TypeInt [ ("_count_"++mdl,Nothing,Nothing) | mdl <- allP ]
                , Pr.Decl $ Pr.Declaration (Just False) TypeInt [ ("_minimum",Nothing,Nothing) ]
                ]
    procs = [ Pr.ProcType { proctypeActive = Nothing
                          , proctypeName = pname
                          , proctypeArguments = []
                          , proctypePriority = Nothing
                          , proctypeProvided = Nothing
                          , proctypeSteps = fmap Pr.toStep $ 
                                            [ prIf [ [ translateTransition allP (Set.toList clocks) pname cycle_time ist n trg cond ]
                                                   | ist <- Set.toList $ baInits buchi,
                                                     ((cond,trg),n) <- zip ((baTransitions buchi)!ist) [0..]
                                                   ]
                                            ] ++
                                            [ Pr.StmtLabel ("st"++show st) $ if Prelude.null trans
                                                                             then Pr.StmtExpr $ ExprAny $ Pr.ConstExpr $ ConstBool False
                                                                             else prIf [ [ translateTransition allP (Set.toList clocks) pname cycle_time st n trg cond ]
                                                                                       | ((cond,trg),n) <- zip trans [0..]
                                                                                       ]
                                            | (st,trans) <- Map.toList (baTransitions buchi)
                                            ]
                          }
            | (pname,TargetProc buchi cycle_time) <- Map.toList $ tmodelProcs tm ]
    init = [Pr.Init Nothing
            [Pr.toStep $ prAtomic $ [Pr.StmtSkip] ++
             {-concat [ case def of
                         Nothing -> [] -- XXX
                         Just (Fix p) -> outputTAssign [(tvar,lvl)] (translateConstant tp p)
                    | (tvar,lvl,tp,def) <- tmodelInits tm
                    ] ++-}
             [ Pr.StmtRun iname []
             | iname <- Map.keys (tmodelProcs tm)
             ]]
           ]
    clocks = Set.fromList $ automatonClocks id ltl_aut
    ltl_aut = getVerifyAutomaton tm
    verify = if use_ltl 
             then [Pr.LTL Nothing (translateVerify (tmodelVerify tm))]
             else [translateVerifyAutomaton ltl_aut]

translateTransition :: [String] -> [Integer] -> String -> Integer -> Integer -> Integer -> Integer -> TransitionConditions -> Pr.Statement
translateTransition (y:ys) clks pname cy st n trg cond 
  = prAtomic $ [Pr.StmtExpr $ Pr.ExprAny $ (case translateTExprs (tcAtoms cond) of
                                               (Nothing,[]) -> cond0
                                               (Just r,[]) -> BinExpr Pr.BinAnd cond0 r
                                                 ) ]++
    (catMaybes [ translateTRestr tvars restr
               | (tvars,restr) <- tcOutputs cond ])++
    [Pr.StmtPrintf ("TRANSITION "++pname++" "++show st++" "++show n++"\n") []
    ,prDStep ([ StmtAssign (VarRef ("_count_"++pname) Nothing Nothing) (BinExpr Pr.BinPlus (RefExpr (VarRef ("_count_"++pname) Nothing Nothing)) (ConstExpr (ConstInt cy)))
              , StmtAssign (VarRef "_minimum" Nothing Nothing) (RefExpr (VarRef ("_count_"++y) Nothing Nothing))
              ] ++
              [ prIf [ [ StmtExpr $ ExprAny $ BinExpr Pr.BinLT (RefExpr (VarRef ("_count_"++v) Nothing Nothing)) (RefExpr (VarRef "_minimum" Nothing Nothing)) 
                       , StmtAssign (VarRef "_minimum" Nothing Nothing) (RefExpr (VarRef ("_count_"++v) Nothing Nothing))
                       ]
                     , [ StmtElse ]
                     ] 
              | v <- ys ] ++
              [ StmtAssign (VarRef ("_count_"++v) Nothing Nothing) (BinExpr Pr.BinMinus (RefExpr (VarRef ("_count_"++v) Nothing Nothing)) (RefExpr (VarRef "_minimum" Nothing Nothing)))
              | v <- y:ys
              ] ++
              [ prIf [ [ StmtExpr $ ExprAny $ BinExpr Pr.BinGTE (RefExpr clk_var) (RefExpr (VarRef "_minimum" Nothing Nothing)),
                         StmtAssign clk_var (BinExpr Pr.BinMinus (RefExpr clk_var) (RefExpr (VarRef "_minimum" Nothing Nothing)))
                       ],
                       [ StmtElse,
                         StmtAssign clk_var (ConstExpr (ConstInt (-1)))
                       ]
                     ]
              | clk <- clks, 
                let clk_var = VarRef ("timer"++show clk) Nothing Nothing ]
             )
    ,Pr.StmtGoto ("st"++show trg)]
    where
      cond0 = BinExpr Pr.BinEquals (RefExpr (VarRef ("_count_"++pname) Nothing Nothing)) (ConstExpr (ConstInt 0))

translateVerify :: TypedExpr TargetVar -> LTLExpr
translateVerify e = case getValue $ unfix e of
  BinBoolExpr op lhs rhs -> LTLBin (case op of
                                       And -> LTLAnd
                                       Or -> LTLOr
                                       Implies -> LTLImplication
                                       Until NoTime -> LTLUntil
                                       UntilOp NoTime -> LTLUntilOp) (translateVerify lhs) (translateVerify rhs)
  UnBoolExpr op ne -> LTLUn (case op of
                                Not -> LTLNot
                                Always -> LTLAlways
                                Next NoTime -> LTLNext
                                Finally NoTime -> LTLEventually) (translateVerify ne)
  _ -> let (Just re,[]) = translateTExpr e
       in LTLNormalExpr re

translateVerifyAutomaton :: BA [TypedExpr TargetVar] Integer -> Pr.Module
translateVerifyAutomaton buchi = prNever $
                              [prIf [ buildTrans mcond resets trg
                                    | ist <- Set.toList $ baInits buchi,
                                      (cond,trg) <- (baTransitions buchi)!ist,
                                      let (mcond,resets) = translateTExprs cond
                                    ] 
                              ] ++
                              [ (if Set.member st (baFinals buchi)
                                 then Pr.StmtLabel ("accept"++show st)
                                 else id) $ 
                                Pr.StmtLabel ("st"++show st) $
                                prIf [ buildTrans mcond resets trg
                                     | (cond,trg) <- trans,
                                       let (mcond,resets) = translateTExprs cond
                                     ]
                              | (st,trans) <- Map.toList $ baTransitions buchi ]
                                where
                                  buildTrans mcond resets trg = [ prAtomic $ (case mcond of
                                                                                 Nothing -> []
                                                                                 Just rcond -> [Pr.StmtExpr $ Pr.ExprAny rcond]) ++
                                                                  [ Pr.StmtAssign (Pr.VarRef ("timer"++show clk) Nothing Nothing) (Pr.ConstExpr $ Pr.ConstInt val)
                                                                  | (clk,val) <- resets ] ++
                                                                  [Pr.StmtGoto ("st"++show trg)]
                                                                ]

translateTExprs :: [TypedExpr TargetVar] -> (Maybe Pr.AnyExpression,[(Integer,Integer)])
translateTExprs [] = (Nothing,[])
translateTExprs xs = foldl1 (\(ce,cc) (ce',cc') -> (case ce of
                                                       Nothing -> ce'
                                                       Just rce -> case ce' of
                                                         Nothing -> Just rce
                                                         Just rce' -> Just $ Pr.BinExpr Pr.BinAnd rce rce',cc++cc')) (fmap translateTExpr xs)

translateConstant :: GTLType -> GTLValue r -> Pr.AnyExpression
translateConstant _ (GTLIntVal x) = Pr.ConstExpr $ Pr.ConstInt x
translateConstant _ (GTLByteVal x) = Pr.ConstExpr $ Pr.ConstInt (fromIntegral x)
translateConstant _ (GTLBoolVal x) = Pr.ConstExpr $ Pr.ConstBool x
translateConstant (Fix (GTLEnum xs)) (GTLEnumVal x)
  = let Just i = elemIndex x xs
    in Pr.ConstExpr $ Pr.ConstInt $ fromIntegral i

translateTExpr :: TypedExpr TargetVar -> (Maybe Pr.AnyExpression,[(Integer,Integer)])
translateTExpr e = case getValue $ unfix e of
  Var (mdl,var,i) lvl _ -> (Just $ Pr.RefExpr (varName mdl var i lvl),[])
  Value val -> (Just $ translateConstant (getType $ unfix e) val,[])
  BinBoolExpr op lhs rhs -> let (l,cl) = translateTExpr lhs
                                (r,cr) = translateTExpr rhs
                            in (case op of
                                   And -> case l of
                                     Nothing -> case r of
                                       Nothing -> Nothing
                                       Just rr -> Just rr
                                     Just rl -> case r of
                                       Nothing -> Just rl
                                       Just rr -> Just $ Pr.BinExpr Pr.BinAnd rl rr
                                   Or -> case l of
                                     Nothing -> Nothing
                                     Just rl -> case r of
                                       Nothing -> Nothing
                                       Just rr -> Just $ Pr.BinExpr Pr.BinOr rl rr
                                   Implies -> case l of
                                     Nothing -> r
                                     Just rl -> case r of
                                       Nothing -> Nothing
                                       Just rr -> Just $ Pr.BinExpr Pr.BinOr (Pr.UnExpr Pr.UnLNot rl) rr,cl++cr)
  BinRelExpr op lhs rhs -> let (Just l,[]) = translateTExpr lhs
                               (Just r,[]) = translateTExpr rhs
                           in (Just $ Pr.BinExpr (case op of
                                                     GTL.BinLT -> Pr.BinLT
                                                     GTL.BinLTEq -> Pr.BinLTE
                                                     GTL.BinGT -> Pr.BinGT
                                                     GTL.BinGTEq -> Pr.BinGTE
                                                     GTL.BinEq -> Pr.BinEquals
                                                     GTL.BinNEq -> Pr.BinNotEquals) l r,[])
  BinIntExpr op lhs rhs -> let (Just l,[]) = translateTExpr lhs
                               (Just r,[]) = translateTExpr rhs
                           in (Just $ Pr.BinExpr (case op of
                                                     OpPlus -> Pr.BinPlus
                                                     OpMinus -> Pr.BinMinus
                                                     OpMult -> Pr.BinMult
                                                     OpDiv -> Pr.BinDiv) l r,[])
  UnBoolExpr op ne -> let (e,c) = translateTExpr ne
                      in case e of
                        Nothing -> (Nothing,c)
                        Just re -> (Just $ Pr.UnExpr (case op of
                                                         Not -> Pr.UnLNot) re,c)
  ClockReset clk val -> (Nothing,[(clk,val)])
  ClockRef clk -> (Just $ Pr.BinExpr Pr.BinGTE (Pr.RefExpr $ Pr.VarRef ("timer"++show clk) Nothing Nothing) (Pr.ConstExpr (Pr.ConstInt 0)),[])
  
-- | Assigns variables including changing their respective history.
outputTAssign :: [(TargetVar,Integer)] -> Pr.AnyExpression -> [Pr.Statement]
outputTAssign [] _ = []
outputTAssign (((inst,var,idx),lvl):rest) expr
  = (assign inst var idx lvl expr) ++
    (outputTAssign rest (Pr.RefExpr (varName inst var idx 0)))

-- | Does only do assignments to variables at time 0.
outputTAssignNow :: [(TargetVar,Integer)] -> Pr.AnyExpression -> [Pr.Statement]
outputTAssignNow [] _ = []
outputTAssignNow (((inst,var,idx),lvl):rest) expr
  = (assignNow inst var idx lvl expr) ++
    (outputTAssign rest (Pr.RefExpr (varName inst var idx 0)))


translateTRestr :: [(TargetVar,Integer)] -> Restriction TargetVar -> Maybe Pr.Statement
translateTRestr tvars restr
  = let checkNEquals to = case unequals restr of
          [] -> Nothing
          xs -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\x -> let (Just p,[]) = translateTExpr x
                                                                  in Pr.BinExpr Pr.BinNotEquals to p) xs)
        checkEquals to = case equals restr of
          [] -> Nothing
          xs -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\x -> let (Just p,[]) = translateTExpr x
                                                                  in Pr.BinExpr Pr.BinEquals to p) xs)
        checkAllowed to = case allowedValues restr of
          Nothing -> Nothing
          Just s -> Just $ if Set.null s
                           then Pr.ConstExpr $ Pr.ConstBool False
                           else foldl1 (Pr.BinExpr Pr.BinOr) (fmap (\i -> Pr.BinExpr Pr.BinEquals to (translateConstant (restrictionType restr) i)
                                                                   ) (Set.toList s)
                                                             )
        checkNAllowed to = if Set.null (forbiddenValues restr)
                           then Nothing
                           else Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\i -> Pr.BinExpr Pr.BinNotEquals to
                                                                                  (translateConstant (restrictionType restr) i)
                                                                           ) (Set.toList $ forbiddenValues restr))
        checkUppers to = case upperLimits restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\(incl,expr) -> let (Just p,[]) = translateTExpr expr
                                                                           in Pr.BinExpr (if incl
                                                                                          then Pr.BinLTE
                                                                                          else Pr.BinLT) to p)
                                                     (upperLimits restr))
        checkLowers to = case lowerLimits restr of
          [] -> Nothing
          _ -> Just $ foldl1 (Pr.BinExpr Pr.BinAnd) (fmap (\(incl,expr) -> let (Just p,[]) = translateTExpr expr
                                                                           in Pr.BinExpr (if incl
                                                                                          then Pr.BinGTE
                                                                                          else Pr.BinGT) to p)
                                                     (lowerLimits restr))
        build f = foldl (\cur el -> case el of
                            Nothing -> cur
                            Just rel -> case cur of
                              Nothing -> Just rel
                              Just rcur -> Just (f rel rcur)) Nothing
    in case equals restr of
      [] -> case allowedValues restr of
        Just r -> let rr = Set.difference r (forbiddenValues restr)
                      check v = build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f (translateConstant (restrictionType restr) v)) [checkNEquals,checkUppers,checkLowers])
                  in case catMaybes [ case ((case check v of
                                                Nothing -> []
                                                Just chk -> [ Pr.StmtExpr $ Pr.ExprAny chk ])++
                                            (outputTAssign tvars (translateConstant (restrictionType restr) v))) of
                                        [] -> Nothing
                                        p -> Just p
                                    | v <- Set.toList rr ] of
                       [] -> Nothing
                       p -> Just $ prIf p
        Nothing -> case buildTGenerator (restrictionType restr)
                        (fmap (\(t,e) -> let (Just p,[]) = translateTExpr e in (t,p)) $ upperLimits restr)
                        (fmap (\(t,e) -> let (Just p,[]) = translateTExpr e in (t,p)) $ lowerLimits restr)
                        (\v -> build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f v) [checkNEquals,checkNAllowed])) tvars of
                     [] -> Nothing
                     [x] -> Just x
                     xs -> Just $ prSequence xs
      _ -> case catMaybes  [ case ((case build (Pr.BinExpr Pr.BinAnd) (fmap (\f -> f tv) [checkAllowed,checkNEquals,checkNAllowed,checkUppers,checkLowers]) of
                                       Nothing -> []
                                       Just chk -> [Pr.StmtExpr $ Pr.ExprAny chk])++
                                   (outputTAssign tvars tv)) of
                               [] -> Nothing
                               p -> Just p
                           | v <- equals restr
                           , let (Just tv,[]) = translateTExpr v ] of
                    [] -> Nothing
                    [[p]] -> Just p
                    p -> Just $ prIf p

buildTGenerator :: GTLType -> [(Bool,Pr.AnyExpression)] -> [(Bool,Pr.AnyExpression)] -> (Pr.AnyExpression -> Maybe Pr.AnyExpression) -> [(TargetVar,Integer)] -> [Pr.Statement]
buildTGenerator tp upper lower check to
  = let rupper e = case upper of
          [] -> Pr.BinExpr Pr.BinLT e (Pr.ConstExpr $ Pr.ConstInt (case baseType tp of
                                                                      Fix (GTLEnum xs) -> (genericLength xs)-1
                                                                      Fix (GTLInt n) -> fromIntegral (maxBound::Int32)
                                                                      Fix GTLBool -> 1
                                                                  ))
          _ -> foldl1 (Pr.BinExpr Pr.BinAnd) $
               fmap (\(inc,expr) -> Pr.BinExpr Pr.BinLT e (if inc
                                                           then expr
                                                           else Pr.BinExpr Pr.BinMinus expr (Pr.ConstExpr $ Pr.ConstInt 1))
                    ) upper
        rlower = fmap (\(inc,expr) -> if inc
                                      then expr
                                      else Pr.BinExpr Pr.BinPlus expr (Pr.ConstExpr $ Pr.ConstInt 1)) lower
    in case to of
      [] -> []
      ((inst,var,idx),lvl):fs
        -> let trg = Pr.RefExpr (varName inst var idx 0)
           in [minimumAssignment (Pr.ConstExpr $ Pr.ConstInt (case baseType tp of
                                                                 Fix (GTLEnum _) -> 0
                                                                 Fix (GTLInt n) -> fromIntegral (minBound::Int32)
                                                                 Fix GTLBool -> 0
                                                             )
                                 )
               (\x -> case assign inst var idx lvl x of
                   [stp] -> stp
                   stps -> prSequence stps)
               rlower]++
               [prDo $ [[Pr.StmtExpr $ Pr.ExprAny $ rupper trg]++
                        (outputTAssignNow to (Pr.BinExpr Pr.BinPlus trg (Pr.ConstExpr $ Pr.ConstInt 1)))
                       ]++(case check trg of
                              Nothing -> [[Pr.StmtBreak]]
                              Just rcheck -> [[Pr.StmtExpr $ Pr.ExprAny rcheck
                                              ,Pr.StmtBreak]
                                             ,[Pr.StmtElse,Pr.StmtSkip]
                                             ])
               ]


translateSpec :: GTLSpec String -> [Pr.Module]
translateSpec spec = translateTarget False (buildTargetModel spec)

convertType :: GTLType -> Pr.Typename
convertType (Fix (GTLInt n)) = Pr.TypeInt
convertType (Fix GTLBool) = Pr.TypeBool
convertType (Fix (GTLEnum _)) = Pr.TypeInt
convertType (Fix (GTLNamed _ tp)) = convertType tp
convertType tp = error $ "Promela target can't use type "++show tp++" yet."

varName :: String -> String -> [Integer] -> Integer -> Pr.VarRef
varName mdl var idx lvl = VarRef (varString mdl var idx lvl) Nothing Nothing

varString :: String -> String -> [Integer] -> Integer -> String
varString mdl var idx lvl = mdl ++ "_" ++ var ++ concat [ "_"++show i | i <- idx] ++ "_"++show lvl

-- | Does an assignemnt to a variable including updating its history.
assign :: String -> String -> [Integer] -> Integer -> Pr.AnyExpression -> [Pr.Statement]
assign mdl var idx lvl expr
  = foldl (\stmts cl -> Pr.StmtAssign (varName mdl var idx cl) (if cl==0
                                                                then expr
                                                                else RefExpr (varName mdl var idx (cl-1))):stmts)
    []
    [0..lvl]

-- | Does only do an assignment for the actual moment
assignNow :: String -> String -> [Integer] -> Integer -> Pr.AnyExpression -> [Pr.Statement]
assignNow mdl var idx lvl expr
  = [Pr.StmtAssign (varName mdl var idx 0) expr]

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

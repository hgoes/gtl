{-# LANGUAGE RankNTypes,DeriveDataTypeable #-}
module Language.GTL.Target.SMT where

import Data.Typeable
import Language.GTL.Model
import Language.GTL.Expression as GTL
import Language.GTL.Types
import Language.GTL.Buchi
import Language.GTL.Translation
import Language.SMTLib2
import Language.SMTLib2.Solver
import Language.SMTLib2.Internals as SMT
import Data.Text as T
import Data.Map as Map
import Data.Set as Set
import Data.AttoLisp as L

verifyModel :: GTLSpec String -> IO ()
verifyModel spec = withZ3 $ do
  let enummp = enumMap spec
  declareEnums enummp
  buildTransitionFunctions T.pack enummp spec
  buildConnectionFun enummp spec

data EnumVal = EnumVal [String] Integer String deriving Typeable

instance SMTType EnumVal where
  getSort (EnumVal _ nr _) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType (EnumVal vals nr _) = [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],declareDatatypes [] [(T.pack $ "Enum"++show nr,[(T.pack val,[]) | val <- vals])])]

instance SMTValue EnumVal where
  mangle (EnumVal _ _ v) = L.Symbol (T.pack v)

buildConnectionFun :: Map [String] Integer -> GTLSpec String -> SMT ()
buildConnectionFun enums spec
  = defineFun (T.pack "__conn")
    [ getUndefined enums t $ \u -> (varName (T.pack $ i++"_"++v) usage 0 idx,getSort u) 
    | (i,v,idx,usage,t) <- (allVars spec Input)++(allVars spec Output) ]
    (getSort (undefined::Bool))
    (toLisp $ and' [ getUndefined enums tp' $ \u -> (assertEq u (SMT.Var (varName (T.pack $ i1++"_"++v1) Output 0 (idx'++idx1)))) .==.
                                                    (SMT.Var (varName (T.pack $ i2++"_"++v2) Input 0 (idx'++idx2)))
          | (GTLConnPt i1 v1 idx1,GTLConnPt i2 v2 idx2) <- gtlSpecConnections spec, 
            let tp = getInstanceVariableType spec False i1 v1,
            (tp',idx') <- allPossibleIdx tp
            ])

allVars :: GTLSpec String -> VarUsage -> [(String,String,[Integer],VarUsage,GTLType)]
allVars spec usage 
  = Prelude.concat
    [ [ (iname,v,i,usage,t') 
      | (v,t) <- Map.toList (case usage of
                                Input -> gtlModelInput mdl
                                Output -> gtlModelOutput mdl
                                _ -> gtlModelLocals mdl
                            ), 
        (t',i) <- allPossibleIdx t
      ]
    | (iname,inst) <- Map.toList $ gtlSpecInstances spec,
      let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
    ]

getUndefined :: Map [String] Integer -> GTLType -> (forall a. (Typeable a,SMTType a) => a -> b) -> b
getUndefined mp rep f = case rep of
  GTLInt -> f (undefined::Integer)
  GTLBool -> f (undefined::Bool)
  GTLEnum enums -> f (EnumVal enums (mp!enums) undefined)
  _ -> error $ "Please implement getUndefined for "++show rep++" you lazy fuck"

getUndefinedNumeric :: GTLType -> (forall a. (Typeable a,SMTType a,Num a) => a -> b) -> b
getUndefinedNumeric rep f
  | rep == GTLInt = f (undefined::Integer)

isNumeric :: GTLType -> Bool
isNumeric GTLInt = True
isNumeric GTLByte = True
isNumeric GTLFloat = True
isNumeric _ = False

assertEq :: a -> b a -> b a
assertEq _ = id

buildTransitionFunctions :: (Ord v,Show v) => (v -> Text) -> Map [String] Integer -> GTLSpec v -> SMT ()
buildTransitionFunctions f enums spec
  = mapM_ (\(name,inp,outp,loc,ba) -> buildTransitionFunction name f enums (fmap (\tp -> (0,tp)) inp) (fmap (\tp -> (0,tp)) outp) (fmap (\tp -> (0,tp)) loc) ba)
    [ (T.pack iname,gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl,gtl2ba (Just (gtlModelCycleTime mdl)) formula)
    | (iname,inst) <- Map.toList (gtlSpecInstances spec), 
      let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst),
      let formula = case gtlInstanceContract inst of
            Nothing -> gtlModelContract mdl
            Just con -> gand con (gtlModelContract mdl)
    ]

buildTransitionFunction :: Ord v => Text -> (v -> Text) -> 
                           Map [String] Integer ->
                           Map v (Integer,GTLType) ->
                           Map v (Integer,GTLType) ->
                           Map v (Integer,GTLType) ->
                           BA [TypedExpr v] Integer -> SMT ()
buildTransitionFunction name f enums inp outp loc ba
  = defineFun ((T.pack "__trans_") `T.append` name) 
    ([ (T.pack "__st",getSort (undefined::Integer)),
       (T.pack "__st'",getSort (undefined::Integer)) ]++
     [ (varName (f var) Input lvl idx,getUndefined enums tp' getSort)
     | (var,(lvls,tp)) <- Map.toList inp
     , lvl <- [0..lvls]
     , (tp',idx) <- allPossibleIdx tp ] ++
     [ (varName (f var) StateIn lvl idx,getUndefined enums tp' getSort)
     | (var,(lvls,tp)) <- Map.toList loc
     , lvl <- [0..lvls]
     , (tp',idx) <- allPossibleIdx tp ] ++
     [ (varName (f var) StateOut lvl idx,getUndefined enums tp' getSort)
     | (var,(lvls,tp)) <- Map.toList loc
     , lvl <- [0..lvls]
     , (tp',idx) <- allPossibleIdx tp ] ++
     [ (varName (f var) Output lvl idx,getUndefined enums tp' getSort)
     | (var,(lvls,tp)) <- Map.toList outp
     , lvl <- [0..lvls]
     , (tp',idx) <- allPossibleIdx tp ]) (getSort (undefined::Bool))
    (toLisp (and' [ (var_st .==. (SMT.constant st)) .=>. 
                    (or' [ and' $ (fmap (toSMTExpr f enums) cond) ++ [var_st' .==. (SMT.constant st')]
                         | (cond,st') <- Set.toList trans
                         ])
                  | (st,trans) <- Map.toList (baTransitions ba)
                  ]))
    where
      var_st,var_st' :: SMTExpr Integer
      var_st = SMT.Var $ T.pack "__st"
      var_st' = SMT.Var $ T.pack "__st'"

enumMap :: Ord v => GTLSpec v -> Map [String] Integer
enumMap spec = let enums = getEnums (Map.unions [ Map.unions [gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl]
                                                | (iname,inst) <- Map.toList (gtlSpecInstances spec),
                                                  let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                                ])
               in Map.fromList (Prelude.zip (Set.toList enums) [0..])

declareEnums :: Map [String] Integer -> SMT ()
declareEnums mp = declareDatatypes [] 
                  [ (T.pack $ "Enum"++show n,[ (T.pack val,[]) | val <- vals ])
                  | (vals,n) <- Map.toList mp ]

varName :: Text -> VarUsage -> Integer -> [Integer] -> Text
varName var u history idx = let base = case history of
                                  0 -> var
                                  lvl -> var `T.append` (T.pack $ "_"++show lvl)
                                base' = case u of
                                             Input -> base
                                             Output -> base
                                             StateIn -> base `T.append` (T.pack "_in")
                                             StateOut -> base `T.append` (T.pack "_out")
                          in if Prelude.null idx
                             then base'
                             else Prelude.foldl (\cur i -> cur `T.append` (T.pack $ "_"++show i)) (base'`T.snoc` '_') idx

toSMTExpr :: (Typeable b,Ord v) => (v -> Text) -> Map [String] Integer -> TypedExpr v -> SMTExpr b
toSMTExpr f enums expr = toSMTExpr' f enums (\e -> case gcast e of
                                                Nothing -> error "internal type error in toSMTExpr"
                                                Just r -> r) (flattenExpr (\v idx -> (v,idx)) [] expr)

toSMTExpr' :: (v -> Text) -> Map [String] Integer -> (forall t. Typeable t => SMTExpr t -> b) -> TypedExpr (v,[Integer]) -> b
toSMTExpr' f enums g expr 
  = case GTL.getValue expr of
    GTL.Var (n,idx) i u -> let idx' = Prelude.reverse idx
                               rtp = getType expr
                           in getUndefined enums rtp
                              (\un -> g $ assertEq un (SMT.Var (varName (f n) u i idx')))
    GTL.Value val -> case val of
      GTLIntVal i -> g (SMT.constant i)
      GTLByteVal w -> g (SMT.constant w)
      GTLBoolVal b -> g (SMT.constant b)
      GTLEnumVal v -> g (SMT.constant (EnumVal undefined undefined v))
    GTL.BinRelExpr rel (Fix l) (Fix r)
      | isNumeric (getType l) -> getUndefinedNumeric (getType l) 
                                 $ \u -> g ((case rel of
                                                BinLT -> Lt
                                                BinLTEq -> Le
                                                BinGT -> Gt
                                                BinGTEq -> Ge
                                                BinEq -> Eq
                                                BinNEq -> \x y -> SMT.Not (Eq x y)
                                            ) 
                                            (toSMTExpr' f enums
                                             (\cl -> assertEq u (case gcast cl of
                                                                    Nothing -> error "internal type error in toSMTExpr'"
                                                                    Just res -> res)) l)
                                            (toSMTExpr' f enums
                                             (\cr -> assertEq u (case gcast cr of
                                                                    Nothing -> error "internal type error in toSMTExpr'"
                                                                    Just res -> res)) r)
                                           )
      | otherwise -> getUndefined enums (getType l)
                     $ \u -> g ((case rel of
                                    BinEq -> Eq
                                    BinNEq -> \x y -> SMT.Not (Eq x y)
                                ) 
                                (toSMTExpr' f enums
                                 (\cl -> assertEq u (case gcast cl of
                                                        Nothing -> error "internal type error in toSMTExpr'"
                                                        Just res -> res)) l)
                                (toSMTExpr' f enums
                                 (\cr -> assertEq u (case gcast cr of
                                                        Nothing -> error "internal type error in toSMTExpr'"
                                                        Just res -> res)) r)
                               )
    GTL.BinIntExpr op (Fix l) (Fix r) 
      | getType l == GTLInt -> g ((case op of
                                      OpPlus -> \x y -> Plus [x,y]
                                      OpMinus -> Minus
                                      OpMult -> \x y -> Mult [x,y]
                                      OpDiv -> Div)
                                  (toSMTExpr' f enums
                                   (\cl -> case gcast cl of
                                       Nothing -> error "internal type error in toSMTExpr'"
                                       Just res -> res) l)
                                  (toSMTExpr' f enums 
                                   (\cr -> case gcast cr of
                                       Nothing -> error "internal type error in toSMTExpr'"
                                       Just res -> res) r))
    GTL.UnBoolExpr GTL.Not (Fix arg) -> g (SMT.Not (toSMTExpr' f enums (\cl -> case gcast cl of
                                                                           Nothing -> error "internal type error in toSMTExpr'"
                                                                           Just res -> res) arg))

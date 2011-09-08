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
import Data.Maybe (catMaybes)

verifyModel :: GTLSpec String -> IO ()
verifyModel spec = do
  res <- withZ3 $ do
    let enummp = enumMap spec
    if Map.null enummp
      then return ()
      else declareEnums enummp
    declareVars enummp spec
    buildTransitionFunctions T.pack enummp spec
    buildConnectionFun enummp spec
    buildEqFun spec
    makeInit 0 spec
    findDiameter spec 0
  print res

data EnumVal = EnumVal [String] Integer String deriving Typeable

instance SMTType EnumVal where
  getSort (EnumVal _ nr _) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType (EnumVal vals nr _) = [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],declareDatatypes [] [(T.pack $ "Enum"++show nr,[(T.pack val,[]) | val <- vals])])]

instance SMTValue EnumVal where
  mangle (EnumVal _ _ v) = L.Symbol (T.pack v)

makeInit :: Integer -> GTLSpec String -> SMT ()
makeInit l spec 
  = sequence_ [ assert $ App (Fun $ T.pack $ "__init_"++iname) (SMT.constant l)
              | iname <- Map.keys (gtlSpecInstances spec) ]

findDiameter :: GTLSpec String -> Integer -> SMT Integer
findDiameter spec n = do
  res <- checkSat
  if res
    then (do
             makeAllTrans spec n (n+1)
             makeConn (n+1) (n+1)
             mapM_ (\i -> makeUnEq (n+1) i) [0..n]
             findDiameter spec (n+1))
    else return n

makeAllTrans :: GTLSpec String -> Integer -> Integer -> SMT ()
makeAllTrans spec i j = mapM_ (\iname -> makeTrans iname i j) (Map.keys $ gtlSpecInstances spec)

makeTrans :: String -> Integer -> Integer -> SMT ()
makeTrans name i j
  = assert $ App (Fun $ T.pack $ "__trans_"++name) (SMT.constant i,SMT.constant j)

makeConn :: Integer -> Integer -> SMT ()
makeConn i j = assert $ App (Fun $ T.pack "__conn") (SMT.constant i,SMT.constant j)

makeUnEq :: Integer -> Integer -> SMT ()
makeUnEq i j = assert $ not' $ App (Fun $ T.pack "__eq") (SMT.constant i,SMT.constant j)

declareVars :: Map [String] Integer -> GTLSpec String -> SMT ()
declareVars enums spec
  = sequence_ $ Prelude.concat
    [ [ declareFun (T.pack $ "__st_"++iname) [] (L.List [L.Symbol $ T.pack "Array"
                                                        ,getSort (undefined::Integer)
                                                        ,getSort (undefined::Integer)])]++
      [ getUndefined enums tp' $ \u -> declareFun (varName (T.pack $ iname++"_"++var) Input 0 idx) [] (L.List [ L.Symbol (T.pack "Array")
                                                                                                              , getSort (undefined::Integer)
                                                                                                              , getSort u ])
      | (var,tp) <- Map.toList (gtlModelInput mdl),
        (tp',idx) <- allPossibleIdx tp
      ] ++
      [ getUndefined enums tp' $ \u -> declareFun (varName (T.pack $ iname++"_"++var) Output 0 idx) [] (L.List [ L.Symbol (T.pack "Array")
                                                                                                               , getSort (undefined::Integer)
                                                                                                               , getSort u ])
      | (var,tp) <- Map.toList (gtlModelOutput mdl),
        (tp',idx) <- allPossibleIdx tp
      ] ++
      [ getUndefined enums tp' $ \u -> declareFun (varName (T.pack $ iname++"_"++var) StateIn 0 idx) [] (L.List [ L.Symbol (T.pack "Array")
                                                                                                                , getSort (undefined::Integer)
                                                                                                                , getSort u ])
      | (var,tp) <- Map.toList (gtlModelLocals mdl),
        (tp',idx) <- allPossibleIdx tp
      ]
    | (iname,inst) <- Map.toList $ gtlSpecInstances spec,
      let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
    ]

buildConnectionFun :: Map [String] Integer -> GTLSpec String -> SMT ()
buildConnectionFun enums spec
  = defineFun (T.pack "__conn")
    [ (vi,getSort (undefined::Integer)) 
    , (vj,getSort (undefined::Integer)) ] (getSort (undefined::Bool))
    (toLisp $ and' [ getUndefined enums tp' $ \u -> (assertEq u 
                                                     (Select (SMT.Var (varName (T.pack $ i1++"_"++v1) Output 0 (idx'++idx1))) vi')) .==.
                                                    (Select (SMT.Var (varName (T.pack $ i2++"_"++v2) Input 0 (idx'++idx2))) vj')
                   | (GTLConnPt i1 v1 idx1,GTLConnPt i2 v2 idx2) <- gtlSpecConnections spec, 
                     let tp = getInstanceVariableType spec False i1 v1,
                     let Right rtp = resolveIndices tp idx1,
                     (tp',idx') <- allPossibleIdx rtp
                   ])
    where
      vi,vj :: Text
      vi = T.pack "__i"
      vj = T.pack "__j"
      vi',vj' :: SMTExpr Integer
      vi' = SMT.Var vi
      vj' = SMT.Var vj

    {-
  = defineFun (T.pack "__conn")
    [ getUndefined enums t $ \u -> (varName (T.pack $ i++"_"++v) usage 0 idx,getSort u) 
    | (i,v,idx,usage,t) <- (allVars spec Input)++(allVars spec Output) ]
    (getSort (undefined::Bool))
    (toLisp $ and' [ getUndefined enums tp' $ \u -> (assertEq u (SMT.Var (varName (T.pack $ i1++"_"++v1) Output 0 (idx'++idx1)))) .==.
                                                    (SMT.Var (varName (T.pack $ i2++"_"++v2) Input 0 (idx'++idx2)))
          | (GTLConnPt i1 v1 idx1,GTLConnPt i2 v2 idx2) <- gtlSpecConnections spec, 
            let tp = getInstanceVariableType spec False i1 v1,
            let Right rtp = resolveIndices tp idx1,
            (tp',idx') <- allPossibleIdx rtp
            ])-}

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

buildEqFun :: GTLSpec v -> SMT ()
buildEqFun spec
  = defineFun (T.pack "__eq") 
    ([ (T.pack "__i",getSort (undefined::Integer)) 
     , (T.pack "__j",getSort (undefined::Integer)) ]) (getSort (undefined::Bool))
    (toLisp $ and' [ App (Fun $ T.pack $ "__eq_"++iname) (SMT.Var (T.pack "__i")::SMTExpr Integer,SMT.Var (T.pack "__j")::SMTExpr Integer) 
                   | iname <- Map.keys $ gtlSpecInstances spec ])
    
buildTransitionFunctions :: (Ord v,Show v) => (v -> Text) -> Map [String] Integer -> GTLSpec v -> SMT ()
buildTransitionFunctions f enums spec
  = mapM_ (\(name,inp,outp,loc,def,ba) -> buildTransitionFunction name f enums (fmap (\tp -> (0,tp)) inp) (fmap (\tp -> (0,tp)) outp) (fmap (\tp -> (0,tp)) loc) def ba)
    [ (T.pack iname,gtlModelInput mdl,gtlModelOutput mdl,gtlModelLocals mdl,gtlModelDefaults mdl,gtl2ba (Just (gtlModelCycleTime mdl)) formula)
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
                           Map v (Maybe GTLConstant) ->
                           BA [TypedExpr v] Integer -> SMT ()
buildTransitionFunction name f enums inp outp loc inits ba
  = do
    let f' n u idx h = varName (T.append (T.snoc name '_') (f n)) u h idx
    defineFun ((T.pack "__trans_") `T.append` name) 
      ([ (vi,getSort (undefined::Integer)) 
       , (vj,getSort (undefined::Integer)) ]) (getSort (undefined::Bool))
      (toLisp (and' [ (var_st .==. (SMT.constant st)) .=>. 
                      (or' [ and' $ (fmap (toSMTExpr f' vi' vj' enums) cond) ++ [var_st' .==. (SMT.constant st')]
                           | (cond,st') <- Set.toList trans
                           ])
                    | (st,trans) <- Map.toList (baTransitions ba)
                    ]))
    defineFun ((T.pack "__eq_") `T.append` name)
      ([ (vi,getSort (undefined::Integer)) 
       , (vj,getSort (undefined::Integer)) ]) (getSort (undefined::Bool))
      (toLisp $ and' $ [ var_st .==. var_st' ]++
       [ getUndefined enums tp' $ \u -> (assertEq u $ SMT.Select (SMT.Var $ f' var Input idx 0) vi') .==.
                                        (SMT.Select (SMT.Var $ f' var Input idx 0) vj')
       | (var,(h,tp)) <- Map.toList inp, 
         (tp',idx) <- allPossibleIdx tp ])
    defineFun ((T.pack "__init_") `T.append` name)
      ([ (vi,getSort (undefined::Integer)) ]) (getSort (undefined::Bool))
      (toLisp $ and' $ 
       [or' [ var_st .==. SMT.constant c
            | c <- Set.toList $ baInits ba ]] ++
       (catMaybes [ case Map.lookup var inits of
                       Nothing -> Just $ toSMTExpr f' vi' vj' enums (geq (Typed tp $ GTL.Var var 0 Input) (constantToExpr (Map.keysSet enums) $ defaultValue tp))
                       Just Nothing -> Nothing
                       Just (Just val) -> Just $ toSMTExpr f' vi' vj' enums (geq (Typed tp $ GTL.Var var 0 Input) (constantToExpr (Map.keysSet enums) val))
                  | (var,(h,tp)) <- Map.toList inp ])
      )

    where
      var_st,var_st' :: SMTExpr Integer
      var_st = SMT.Select (SMT.Var $ T.append (T.pack "__st_") name) vi'
      var_st' = SMT.Select (SMT.Var $ T.append (T.pack "__st_") name) vj'
      vi,vj :: Text
      vi = T.pack "__i"
      vj = T.pack "__j"
      vi',vj' :: SMTExpr Integer
      vi' = SMT.Var vi
      vj' = SMT.Var vj

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
                             else Prelude.foldl (\cur i -> cur `T.append` (T.pack $ "_"++show i)) (base' `T.snoc` '_') idx

toSMTExpr :: (Typeable b,Ord v) => (v -> VarUsage -> [Integer] -> Integer -> Text) -> 
             SMTExpr Integer -> SMTExpr Integer ->
             Map [String] Integer -> TypedExpr v -> SMTExpr b
toSMTExpr f vi vj enums expr = toSMTExpr' f vi vj enums (\e -> case gcast e of
                                                            Nothing -> error "internal type error in toSMTExpr"
                                                            Just r -> r) (flattenExpr (\v idx -> (v,idx)) [] expr)

toSMTExpr' :: (v -> VarUsage -> [Integer] -> Integer -> Text) -> 
              SMTExpr Integer -> SMTExpr Integer ->
              Map [String] Integer -> (forall t. Typeable t => SMTExpr t -> b) -> TypedExpr (v,[Integer]) -> b
toSMTExpr' f vi vj enums g expr 
  = case GTL.getValue expr of
    GTL.Var (n,idx) i u -> let idx' = Prelude.reverse idx
                               rtp = getType expr
                           in getUndefined enums rtp
                              (\un -> g $ assertEq un (SMT.Select (SMT.Var (f n u idx' i)) (case u of
                                                                                               Input -> vi
                                                                                               StateIn -> vi
                                                                                               _ -> vj)))
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
                                            (toSMTExpr' f vi vj enums
                                             (\cl -> assertEq u (case gcast cl of
                                                                    Nothing -> error "internal type error in toSMTExpr'"
                                                                    Just res -> res)) l)
                                            (toSMTExpr' f vi vj enums
                                             (\cr -> assertEq u (case gcast cr of
                                                                    Nothing -> error "internal type error in toSMTExpr'"
                                                                    Just res -> res)) r)
                                           )
      | otherwise -> getUndefined enums (getType l)
                     $ \u -> g ((case rel of
                                    BinEq -> Eq
                                    BinNEq -> \x y -> SMT.Not (Eq x y)
                                ) 
                                (toSMTExpr' f vi vj enums
                                 (\cl -> assertEq u (case gcast cl of
                                                        Nothing -> error "internal type error in toSMTExpr'"
                                                        Just res -> res)) l)
                                (toSMTExpr' f vi vj enums
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
                                  (toSMTExpr' f vi vj enums
                                   (\cl -> case gcast cl of
                                       Nothing -> error "internal type error in toSMTExpr'"
                                       Just res -> res) l)
                                  (toSMTExpr' f vi vj enums 
                                   (\cr -> case gcast cr of
                                       Nothing -> error "internal type error in toSMTExpr'"
                                       Just res -> res) r))
    GTL.UnBoolExpr GTL.Not (Fix arg) -> g (SMT.Not (toSMTExpr' f vi vj enums (\cl -> case gcast cl of
                                                                                 Nothing -> error "internal type error in toSMTExpr'"
                                                                                 Just res -> res) arg))
    GTL.IndexExpr _ _ -> error "Index expressions shouldn't appear here in toSMTExpr'"
    GTL.BinBoolExpr GTL.And (Fix l) (Fix r) -> g $ and' [toSMTExpr' f vi vj enums (\cl -> case gcast cl of
                                                                                      Nothing -> error "internal type error in toSMTExpr'"
                                                                                      Just res -> res) l
                                                        ,toSMTExpr' f vi vj enums (\cr -> case gcast cr of
                                                                                      Nothing -> error "internal type error in toSMTExpr'"
                                                                                      Just res -> res) r]
    --GTL.BinBoolExpr op _ _ -> error $ "Binary boolean expressions ("++show op++") shouldn't appear here in toSMTExpr'"
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
import Data.Array (Array)
import Control.Monad.Trans

verifyModel :: GTLSpec String -> IO ()
verifyModel spec = do
  res <- withZ3 $ do
    let enummp = enumMap spec
    if Map.null enummp
      then return ()
      else declareEnums enummp
    l <- SMT.varNamed $ T.pack "__l"
    inloop <- SMT.varNamed $ T.pack "__inloop"
    loop_exists <- SMT.varNamed $ T.pack "__loop_exists"
    declareVars enummp spec
    buildTransitionFunctions T.pack enummp spec
    buildConnectionFun enummp spec
    buildEqFun spec
    let name_gen = \(m,v) u idx h -> varName (T.pack $ m ++ "_"++v) u h idx
        name_gen' = \((m,v),idx') u idx h -> name_gen (m,v) u (idx'++idx) h
    let ver = GTL.flattenExpr (\x i -> (x,i)) [] $ GTL.distributeNot (gtlSpecVerify spec)
    temp_arrs <- mkTemporalArrays name_gen ver
    findLoop name_gen' enummp spec l inloop loop_exists temp_arrs ver 0
  mapM_ print res

findLoop gen_name enums spec l inloop loop_exists temp_arrays ver i = do
  res <- solve gen_name enums spec l inloop loop_exists temp_arrays ver i 
         (do
             solvable <- checkSat
             if solvable
               then (do
                        tr <- getTrace enums spec i
                        return $ Just tr)
               else return Nothing)
  case res of
    Just (Just tr) -> return tr
    Just Nothing -> findLoop gen_name enums spec l inloop loop_exists temp_arrays ver (i+1)
    Nothing -> return []

type NameGenerator v = v -> VarUsage -> [Integer] -> Integer -> Text

type TimeOpMap v = Map (TypedExpr (v,[Integer])) (SMTExpr Bool)

type TimeOpMap2 v = Map (TypedExpr (v,[Integer]),TypedExpr (v,[Integer])) (SMTExpr Bool)

type GenVarState v = (TimeOpMap v,TimeOpMap2 v,TimeOpMap2 v)

data TemporalArrays v = TemporalArrays { formulaEncoding :: Map (TypedExpr (v,[Integer])) (SMTExpr (Array Integer Bool),Bool)
                                       , auxFEncoding :: Map (TypedExpr (v,[Integer])) (SMTExpr (Array Integer Bool))
                                       , auxGEncoding :: Map (TypedExpr (v,[Integer])) (SMTExpr (Array Integer Bool))
                                       }

mkTemporalArrays :: Ord v => NameGenerator v -> TypedExpr (v,[Integer]) -> SMT (TemporalArrays v)
mkTemporalArrays f expr = do
  (arr,_) <- mkTemporalArrays' f (TemporalArrays Map.empty Map.empty Map.empty) 0 expr
  return arr
        
mkTemporalArrays' :: Ord v => NameGenerator v
                     -> TemporalArrays v
                     -> Integer -> TypedExpr (v,[Integer]) 
                     -> SMT (TemporalArrays v,Integer)
mkTemporalArrays' f p n expr
  | Map.member expr (formulaEncoding p) = return (p,n)
  | otherwise = case GTL.getValue expr of
    GTL.Var (name,idx) h u -> return (p { formulaEncoding = Map.insert expr (SMT.Var $ f name u idx h,False) (formulaEncoding p) 
                                        },n)
    GTL.BinRelExpr _ _ _ -> do
      arr <- varNamed $ T.pack $ "__prop"++show n
      return (p { formulaEncoding = Map.insert expr (arr,False) (formulaEncoding p)
                },n+1)
    GTL.BinBoolExpr op (Fix lhs) (Fix rhs) -> do
      (p1,n1) <- mkTemporalArrays' f p n lhs
      (p2,n2) <- mkTemporalArrays' f p1 n1 rhs
      arr <- varNamed $ T.pack $ "__"++(case op of
                                           GTL.And -> "and"
                                           GTL.Or -> "or"
                                           GTL.Until NoTime -> "until"
                                           GTL.UntilOp NoTime -> "until_op")++show n2
      let p2' = p2 { formulaEncoding = Map.insert expr (arr,False) (formulaEncoding p2)
                   }
      case op of
        GTL.Until NoTime 
          | Map.member rhs (auxFEncoding p2') -> return (p2',n2+1)
          | otherwise -> do
            arr' <- varNamed $ T.pack $ "__finals"++show n2
            return (p2' { auxFEncoding = Map.insert rhs arr' (auxFEncoding p2') },n2+1)
        GTL.UntilOp NoTime
          | Map.member rhs (auxGEncoding p2') -> return (p2',n2+1)
          | otherwise -> do
            arr' <- varNamed $ T.pack $ "__finals"++show n2
            return (p2' { auxGEncoding = Map.insert rhs arr' (auxGEncoding p2') },n2+1)
        _ -> return (p2',n2+1)
    GTL.UnBoolExpr GTL.Not (Fix (Typed _ (GTL.Var (name,idx) h u))) -> return (p { formulaEncoding = Map.insert expr (SMT.Var $ f name u idx h,True) (formulaEncoding p)
                                                                                 },n)
    GTL.UnBoolExpr op (Fix e) -> do
      (p1,n1) <- mkTemporalArrays' f p n e
      case op of
        GTL.Always -> do
          arr <- varNamed $ T.pack $ "__until_op"++show n1
          aux' <- if Map.member e (auxGEncoding p1)
                  then return $ auxGEncoding p1
                  else (do
                        arr' <- varNamed $ T.pack $ "__finals"++show n1
                        return $ Map.insert e arr' (auxGEncoding p1))
          return (p1 { formulaEncoding = Map.insert expr (arr,False) (formulaEncoding p1)
                     , auxGEncoding = aux'
                     },n1+1)
        GTL.Finally NoTime -> do
          arr <- varNamed $ T.pack $ "__until"++show n1
          aux' <- if Map.member e (auxFEncoding p1)
                  then return $ auxFEncoding p1
                  else (do
                        arr' <- varNamed $ T.pack $ "__finals"++show n1
                        return $ Map.insert e arr' (auxFEncoding p1))
          return (p1 { formulaEncoding = Map.insert expr (arr,False) (formulaEncoding p1)
                     , auxFEncoding = aux'
                     },n1+1)
        _ -> return (p1,n1)
    _ -> return (p,n)

getTemporalVar :: Ord v => TemporalArrays v
                  -> TypedExpr (v,[Integer])
                  -> Integer
                  -> SMTExpr Bool
getTemporalVar mp expr i = case GTL.getValue expr of
  GTL.Value (GTLBoolVal x) -> SMT.constant x
  _ -> let Just (arr,neg) = Map.lookup expr (formulaEncoding mp)
       in select arr (SMT.constant i)

generateDependencies :: Ord v => NameGenerator (v,[Integer])
                        -> Map [String] Integer
                        -> TemporalArrays v
                        -> TypedExpr (v,[Integer])
                        -> Integer
                        -> SMT (SMTExpr Bool)
generateDependencies f enums mp expr i
  = case GTL.getValue expr of
    GTL.Value (GTLBoolVal x) -> return $ SMT.constant x
    GTL.BinBoolExpr op (Fix lhs) (Fix rhs) -> do
      l <- generateDependencies f enums mp lhs i
      r <- generateDependencies f enums mp rhs i
      case op of
        GTL.And -> assert $ self .==. and' [l,r]
        GTL.Or -> assert $ self .==. or' [l,r]
        GTL.Until NoTime -> assert $ self .==. or' [r,and' [l,select arr (SMT.constant (i+1))]]
        GTL.UntilOp NoTime -> assert $ self .==. and' [r,or' [l,select arr (SMT.constant (i+1))]]
      return self
    GTL.UnBoolExpr op (Fix e) -> do
      e' <- generateDependencies f enums mp e i
      case op of
        GTL.Always -> assert $ self .==. and' [e',select arr (SMT.constant (i+1))]
        GTL.Finally NoTime -> assert $ self .==. or' [e',select arr (SMT.constant (i+1))]
        _ -> return ()
      return self
    GTL.BinRelExpr _ _ _ -> do
      assert $ self .==. toSMTExpr f (SMT.constant i) (SMT.constant i) enums expr
      return self
    _ -> return self
  where
    Just (arr,neg) = Map.lookup expr (formulaEncoding mp)
    self = if neg 
           then not' $ select arr (SMT.constant i)
           else select arr (SMT.constant i)

solve :: NameGenerator ((String,String),[Integer]) ->
         Map [String] Integer ->
         GTLSpec String -> 
         SMTExpr (Array Integer Bool) ->
         SMTExpr (Array Integer Bool) ->
         SMTExpr Bool ->
         TemporalArrays (String,String) ->
         TypedExpr ((String,String),[Integer]) ->
         Integer ->
         SMT r -> SMT (Maybe r)
solve gen_name enums spec l inloop loop_exists tarrs ver 0 f = do
  makeInit 0 spec
  makeConn 0 0
  -- Base case for LoopConstraints:
  assert $ not' (select l 0)
  assert $ not' (select inloop 0)
  
  -- Base case for LastStateFormula
  mvar <- generateDependencies gen_name enums tarrs ver 0
  mapM_ (\(expr,(arr,neg)) -> do
            assert $ (not' loop_exists) .=>. ((if neg then id
                                               else not')
                                              $ select arr (SMT.constant (-2)))
            -- Base case for IncPLTL:
            case GTL.getValue expr of
              GTL.UnBoolExpr GTL.Not (Fix e) -> assert $ (not' loop_exists) .=>. ((if neg then not'
                                                                                   else id)
                                                                                  $ select arr (SMT.constant (-2)))
              GTL.UnBoolExpr (Finally NoTime) (Fix e) -> let Just r = Map.lookup e (auxFEncoding tarrs)
                                                         in do
                                                           assert $ loop_exists .=>. ((select arr (SMT.constant (-1))) .=>. (select r (SMT.constant (-1))))
                                                           assert $ not' (select r (SMT.constant 0))
              GTL.UnBoolExpr Always (Fix e) -> let Just r = Map.lookup e (auxGEncoding tarrs)
                                               in do
                                                  assert $ loop_exists .=>. ((select r (SMT.constant (-1))) .=>. (select arr (SMT.constant (-1))))
                                                  assert $ select r (SMT.constant 0)
              GTL.BinBoolExpr (Until NoTime) (Fix lhs) (Fix rhs) -> let Just r = Map.lookup rhs (auxFEncoding tarrs)
                                                                    in do
                                                                       assert $ loop_exists .=>. ((select arr (SMT.constant (-1))) .=>. (select r (SMT.constant (-1))))
                                                                       assert $ not' (select r (SMT.constant 0))
              GTL.BinBoolExpr (UntilOp NoTime) (Fix lhs) (Fix rhs) -> let Just r = Map.lookup rhs (auxGEncoding tarrs)
                                                                      in do
                                                                         assert $ loop_exists .=>. ((select r (SMT.constant (-1))) .=>. (select arr (SMT.constant (-1))))
                                                                         assert $ select r (SMT.constant 0)
              _ -> return ()
        ) (Map.toList $ formulaEncoding tarrs)
  
  assert mvar
  
  stack $ do
    -- k-variant case for LoopConstraints
    assert $ eqst 0 (-1)
    assert $ not' loop_exists
    -- k-variant case for LastStateFormula
    mapM_ (\(expr,(arr,neg)) -> do
              assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant 0))
              assert $ (select arr (SMT.constant 1)) .==. (select arr (SMT.constant (-2)))
          ) (Map.toList $ formulaEncoding tarrs)
    -- k-variant case for IncPLTL
    mapM_ (\arr -> assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant 0))) (Map.elems $ auxFEncoding tarrs)
    mapM_ (\arr -> assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant 0))) (Map.elems $ auxGEncoding tarrs)
    res <- f
    return $ Just res
solve gen_name enums spec l inloop loop_exists tarrs ver i f = do
  makeAllTrans spec (i-1) i 
  makeConn i i

  -- k-invariant case for LoopConstraints:
  assert $ (select l (SMT.constant i)) .=>. (eqst (SMT.constant (i-1)) (-1))
  assert $ (select inloop (SMT.constant i)) .==. (or' [select inloop (SMT.constant $ i-1)
                                                      ,select l (SMT.constant i)])
  assert $ (select inloop (SMT.constant $ i - 1)) .=>. (not' (select l (SMT.constant i)))
  
  -- k-invariant case for LastStateFormula
  mvar <- generateDependencies gen_name enums tarrs ver i
  mapM_ (\(expr,(arr,neg)) -> do
            assert $ (select l (SMT.constant i)) .=>. (select arr (SMT.constant (-2)) .==. (select arr (SMT.constant i)))) (Map.toList $ formulaEncoding tarrs)
  
  -- k-invariant case for IncPLTL
  
  mapM_ (\(expr,arr) -> let Just (fe,neg) = Map.lookup expr (formulaEncoding tarrs)
                            fe' = select fe (SMT.constant i)
                            fe'' = if neg then not' fe' else fe'
                        in assert $ (select arr (SMT.constant i)) .==. or' [select arr (SMT.constant (i-1))
                                                                           ,and' [select inloop (SMT.constant i)
                                                                                 ,fe''
                                                                                 ]]) (Map.toList $ auxFEncoding tarrs)
  mapM_ (\(expr,arr) -> let Just (fe,neg) = Map.lookup expr (formulaEncoding tarrs)
                            fe' = select fe (SMT.constant i)
                            fe'' = if neg then not' fe' else fe'
                        in assert $ (select arr (SMT.constant i)) .==. and' [select arr (SMT.constant (i-1))
                                                                            ,or' [not' $ select inloop (SMT.constant i)
                                                                                 ,fe''
                                                                                 ]]) (Map.toList $ auxGEncoding tarrs)


  -- Simple-Path constraints doesn't work yet
  {-
  mapM_ (\j -> assert $ or' [not' $ eqst (SMT.constant i) (SMT.constant j)
                            ,not' $ select inloop (SMT.constant i) .==. select inloop (SMT.constant j)
                            ,not' $ (getTemporalVar tarrs ver i) .==. (getTemporalVar tarrs ver j)
                            ]
        ) [0..(i-1)]-}
  r <- checkSat
  if r
     then (stack $ do
              -- k-variant case for LoopConstraints
              assert $ loop_exists .==. (select inloop (SMT.constant i))
              assert $ eqst (SMT.constant i) (-1)
              -- k-variant case for LastStateFormula
              mapM_ (\(expr,(arr,neg)) -> do
                        assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant i))
                        assert $ (select arr (SMT.constant (i+1))) .==. (select arr (SMT.constant (-2)))
                    ) (Map.toList $ formulaEncoding tarrs)
              -- k-variant case for IncPLTL
              mapM_ (\arr -> assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant i))) (Map.elems $ auxFEncoding tarrs)
              mapM_ (\arr -> assert $ (select arr (SMT.constant (-1))) .==. (select arr (SMT.constant i))) (Map.elems $ auxGEncoding tarrs)
              res <- f
              return $ Just res)
    else return Nothing



data EnumVal = EnumVal [String] Integer String deriving Typeable

instance SMTType EnumVal where
  getSort (EnumVal _ nr _) = L.Symbol (T.pack $ "Enum"++show nr)
  declareType (EnumVal vals nr _) = [(mkTyConApp (mkTyCon $ "Enum"++show nr) [],declareDatatypes [] [(T.pack $ "Enum"++show nr,[(T.pack val,[]) | val <- vals])])]

instance SMTValue EnumVal where
  mangle (EnumVal _ _ v) = L.Symbol (T.pack v)
  unmangle (L.Symbol v) = EnumVal undefined undefined (T.unpack v)

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

eqst :: SMTExpr Integer -> SMTExpr Integer -> SMTExpr Bool
eqst i j = App (Fun $ T.pack "__eq") (i,j)

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
       | (var,(h,tp)) <- (Map.toList inp) ++ (Map.toList outp), 
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
                  | (var,(h,tp)) <- (Map.toList inp) ++ (Map.toList outp) ])
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

extractValue :: Map [String] Integer -> String -> String -> GTLType -> [Integer] -> Integer -> SMT GTLConstant
extractValue enums iname var tp idx i = case tp of
  GTLInt -> do
    r <- SMT.getValue $ select (SMT.Var rname) (SMT.constant i)
    return $ Fix $ GTLIntVal r
  GTLBool -> do
    r <- SMT.getValue $ select (SMT.Var rname) (SMT.constant i)
    return $ Fix $ GTLBoolVal r
  GTLEnum enums -> do
    EnumVal _ _ x <- SMT.getValue $ select (SMT.Var rname) (SMT.constant i)
    return $ Fix $ GTLEnumVal x
  GTLArray sz tp' -> do
    vs <- mapM (\x -> extractValue enums iname var tp' (x:idx) i) [0..(sz-1)]
    return $ Fix $ GTLArrayVal vs
  where
    rname = varName (T.pack $ iname++"_"++var) Input 0 idx

getTrace :: Map [String] Integer -> GTLSpec String -> Integer -> SMT [Map (String,String) GTLConstant]
getTrace enums spec k = do
  sequence [ do
                lst <- sequence [ do 
                                     v <- extractValue enums iname var tp [] i
                                     return ((iname,var),v)
                                | (iname,inst) <- Map.toList $ gtlSpecInstances spec
                                , let mdl = (gtlSpecModels spec)!(gtlInstanceModel inst)
                                , (var,tp) <- Map.toList (gtlModelInput mdl) ++ Map.toList (gtlModelOutput mdl)
                                ]
                return $ Map.fromList lst
           | i <- [0..k] ]

toSMTExpr :: (Typeable b,Ord v) => (v -> VarUsage -> [Integer] -> Integer -> Text) -> 
             SMTExpr Integer -> SMTExpr Integer ->
             Map [String] Integer -> TypedExpr v -> SMTExpr b
toSMTExpr f vi vj enums expr = toSMTExpr' f vi vj enums (\e -> case gcast e of
                                                            Nothing -> error "internal type error in toSMTExpr"
                                                            Just r -> r) (flattenExpr (\v idx -> (v,idx)) [] expr)

toSMTExpr' :: NameGenerator v -> 
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
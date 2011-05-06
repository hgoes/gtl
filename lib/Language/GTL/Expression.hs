{-# LANGUAGE ScopedTypeVariables,GADTs,DeriveDataTypeable,FlexibleInstances,
  ExistentialQuantification, StandaloneDeriving, TypeSynonymInstances #-}
{-| Provides the expression data type as well as the type-checking algorithm.
 -}
module Language.GTL.Expression where

import Language.GTL.Parser.Syntax
import Language.GTL.Parser.Token

import Data.Binary
import Data.Typeable
import Data.Array
import Data.Dynamic
import System.IO.Unsafe
import Data.Maybe
import Data.Map as Map
import Unsafe.Coerce
import Control.Exception
import Control.Monad (foldM)

instance Ord TypeRep where
    compare t1 t2 =
        compare
            (unsafePerformIO $ typeRepKey t1)
            (unsafePerformIO $ typeRepKey t2)

class (Show v, Ord v, Eq v) => VarType v where
instance VarType String where
instance VarType (String, String) where
instance VarType (Maybe String, String)

class (Show a, Typeable a, Binary a) => BaseType a where
instance BaseType Bool where
instance BaseType Int where
instance BaseType (Array Integer Integer) where

intRep = typeOf (undefined :: Int)
boolRep = typeOf (undefined :: Bool)

-- | Constructs a value of type b by appliying the constructor
-- to the value castet from type a into its correct type.
construct :: BaseType a => a -> (Map TypeRep (Dynamic -> b)) -> Maybe b
construct x constructors =
  let c' = Map.lookup (typeOf x) constructors
  in case c' of
    Nothing -> Nothing
    Just c -> Just (c (toDyn x))

unsafeFromDyn :: Typeable a => Dynamic -> a
unsafeFromDyn = fromJust . fromDynamic

-- | A type-safe expression type.
--   /v/ is the type of variables description (for example `String' or `(String, String)'
--  for unqualified or qualified names) and /a/ is the type of the expression.
data Expr v a where
  ExprVar :: BaseType a => v -> Integer -> Expr v a -- A variable. Can have any type.
  ExprConst :: BaseType a => a -> Expr v a -- A constant. Has the type of the constant.
  ExprBinInt :: IntOp -> Expr v Int -> Expr v Int -> Expr v Int -- A binary integer operation that takes two integer expressions and returns an integer expression.
  ExprBinBool :: BoolOp -> Expr v Bool -> Expr v Bool -> Expr v Bool -- A binary boolean operation.
  ExprRel ::
    BaseType t => Relation -> EqualExpr v t -> Expr v Bool -- A relation between expressions of an arbitrary type.
  ExprElem :: v -> [Integer] -> Bool -> Expr v Bool -- `ExprElem' /x/ /xs/ `True' means: "/x/ is element of the list /xs/".
  ExprNot :: Expr v Bool -> Expr v Bool
  ExprAlways :: Expr v Bool -> Expr v Bool
  ExprNext :: Expr v Bool -> Expr v Bool
  deriving Typeable

data EqualExpr v b
  = (Eq v, Eq b, Ord b, BaseType b) =>
    EqualExpr (Expr v b) (Expr v b)
  deriving Typeable
--deriving instance Eq v =>  Eq (EqualExpr v b)
--deriving instance Ord v =>  Ord (EqualExpr v b)

--castEqual :: (Eq v, Eq a1, BaseType a1, Eq a2, BaseType a2) => (EqualExpr v a1) -> (EqualExpr v a2) -> Bool
castEqual (EqualExpr lhs1 rhs1) (EqualExpr lhs2 rhs2) =
  let testCasted p v = maybe False p (gcast v) -- testCasted :: (Typeable a, Typeable b) => ((Expr v a) -> Bool) -> (Expr v b) -> Bool
  in  (testCasted ((==) lhs1) lhs2) && (testCasted ((==) rhs1) rhs2)

castCompare (EqualExpr lhs1 rhs1) (EqualExpr lhs2 rhs2) =
  let testCasted p v = maybe LT p (gcast v)
  in
    case (testCasted (compare lhs1) lhs2) of
      EQ -> (testCasted (compare rhs1) rhs2)
      r -> r

data TypeErasedExpr v = forall t. BaseType t => TypeErasedExpr TypeRep (Expr v t)

exprType :: VarType v => TypeErasedExpr v -> TypeRep
exprType (TypeErasedExpr t e) = t

castExpr :: (VarType v, BaseType t) => TypeErasedExpr v -> Maybe (Expr v t)
castExpr e = castExpr' e undefined
  where
    castExpr' :: (VarType v, BaseType t) => TypeErasedExpr v -> t -> Maybe (Expr v t)
    castExpr' (TypeErasedExpr t expr) t' =
      if t == typeOf t' then
        Just (unsafeCoerce expr)
      else
        Nothing

comp2 :: (c -> d) -> (a -> b -> c) -> a -> b -> d
--comp2 g f a b = g(f a b)
comp2 = (.).(.)

comp22 :: (c -> d -> e) -> (a -> b -> c) -> a -> b -> d -> e
comp22 g f a b d = g (f a b) d

-- Factory functions

makeExprVar :: VarType v => v -> Integer -> TypeRep -> Maybe (TypeErasedExpr v)
makeExprVar name time t =
  let
    varConstructors :: Map TypeRep (v -> Integer -> TypeErasedExpr v)
    varConstructors = Map.fromList [
        (intRep, TypeErasedExpr intRep `comp2` (ExprVar :: v -> Integer -> Expr v Int))
        , (boolRep, TypeErasedExpr boolRep `comp2` (ExprVar :: v -> Integer -> Expr v Bool))]
    c' = Map.lookup t varConstructors
  in case c' of
    Nothing -> Nothing
    Just c -> Just (c name time)

makeExprConst :: (BaseType t, VarType v) => t -> (TypeErasedExpr v)
makeExprConst v = TypeErasedExpr (typeOf v) (ExprConst v)

makeExprBinInt :: VarType v => IntOp -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprBinInt op (TypeErasedExpr tl lhs) (TypeErasedExpr tr rhs) =
  if tr == tl then
    if tr == intRep then
      Right (TypeErasedExpr tl (ExprBinInt op (unsafeCoerce lhs) (unsafeCoerce rhs)))
    else
      Left $ "Expected type int for operator " ++ show op ++  " but got type " ++ show tl ++ "."
  else
    error "Types in makeExprBinInt not equal or not int"

makeExprRel :: VarType v => Relation -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprRel op (lhs :: (TypeErasedExpr v)) (rhs :: (TypeErasedExpr v)) =
  let
    tl = exprType lhs
    tr = exprType rhs

    makeEqualExpr :: (VarType v, BaseType t, Ord t) => (TypeErasedExpr v) -> (TypeErasedExpr v) -> EqualExpr v t
    makeEqualExpr (TypeErasedExpr tl lhs) (TypeErasedExpr tr rhs)
      = EqualExpr (unsafeCoerce lhs) (unsafeCoerce rhs)

    makeExprRelInt :: VarType v => Relation -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> (TypeErasedExpr v)
    makeExprRelInt op lhs rhs
      = TypeErasedExpr intRep (ExprRel op ((makeEqualExpr lhs rhs) :: EqualExpr v Int))

    makeExprRelBool :: VarType v => Relation -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> (TypeErasedExpr v)
    makeExprRelBool op (TypeErasedExpr tl lhs) (TypeErasedExpr tr rhs)
      = TypeErasedExpr boolRep (ExprRel op ((EqualExpr (unsafeCoerce lhs) (unsafeCoerce rhs)) :: EqualExpr v Bool))

    constructors :: VarType v => Map TypeRep (Relation -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> (TypeErasedExpr v))
    constructors = Map.fromList [
        (intRep, makeExprRelInt)
        , (boolRep, makeExprRelBool)]

  in if tl == tr then
    case Map.lookup tl constructors of
      Nothing -> Left $ "Relation " ++ show op ++ " not defined on type " ++ show tl ++ "."
      Just c -> Right (c op lhs rhs)
  else
    error "Types in makeExprRel not equal!"

makeExprBinBool :: VarType v => BoolOp -> (TypeErasedExpr v) -> (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprBinBool op (TypeErasedExpr tl lhs) (TypeErasedExpr tr rhs) =
  if tr == tl then
    if tr == boolRep then
      Right (TypeErasedExpr tl (ExprBinBool op (unsafeCoerce lhs) (unsafeCoerce rhs)))
    else
      Left $ "Expected type Bool for operator " ++ show op ++  " but got type " ++ show tl ++ "."
  else
    error "Types in makeExprBinBool not equal!"

makeExprNot :: VarType v => (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprNot (TypeErasedExpr tl lhs) =
  if tl == boolRep then
    Right (TypeErasedExpr tl (ExprNot (unsafeCoerce lhs)))
  else
    Left $ "Expected type Bool for operator not but got type " ++ show tl ++ "."

makeExprAlways :: VarType v => (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprAlways (TypeErasedExpr tl lhs) =
  if tl == boolRep then
    Right (TypeErasedExpr tl (ExprAlways (unsafeCoerce lhs)))
  else
    Left $ "Expected type Bool for operator always but got type " ++ show tl ++ "."

makeExprNext :: VarType v => (TypeErasedExpr v) -> Either String (TypeErasedExpr v)
makeExprNext (TypeErasedExpr tl lhs) =
  if tl == boolRep then
    Right (TypeErasedExpr tl (ExprNext (unsafeCoerce lhs)))
  else
    Left $ "Expected type Bool for operator next but got type " ++ show tl ++ "."

{-
instance (Eq v, Binary v, Binary t, Typeable t) => Binary (EqualExpr v t) where
  put (EqualExpr lhs rhs) = put lhs >> put rhs
  get = do
    lhs <- get
    rhs <- get
    castSer (EqualExpr lhs rhs)
-}

-- | Typecheck an untyped expression. Converts it into the `Expr' type which is strongly typed.
--   Returns either an error message or the resulting expression of type `Bool'.
typeCheck :: (VarType a, BaseType t)
             => Map a TypeRep -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> GExpr -- ^ The expression to convert
             -> Either String (Expr a t)
typeCheck tp f bind expr = typeCheck' tp f bind expr undefined
  where
  typeCheck' :: (VarType a, BaseType t)
               => Map a TypeRep -- ^ Type mapping
               -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
               -> ExistsBinding a
               -> GExpr -- ^ The expression to convert
               -> t
               -> Either String (Expr a t)
  typeCheck' tp f bind expr t =
    case inferType tp f bind expr of
      Left e -> Left e
      Right expr -> case castExpr expr of
        Nothing -> Left $ "Expected expression of type " ++ (show $ typeOf t) ++ " but got type " ++ show (exprType expr)
        Just expr' -> Right expr'

inferType :: VarType a
             => Map a TypeRep
             -> (Maybe String -> String -> Either String a)
             -> ExistsBinding a
             -> GExpr
             -> Either String (TypeErasedExpr a)
inferType tp f bind (GVar q n) = do
  let nl = do
        v <- f q n
        return (v,0)
  (rv,lvl) <- case q of
    Nothing -> case Map.lookup n bind of
      Just (v,lvl) -> return (v,lvl)
      Nothing -> nl
    _ -> nl
  case Map.lookup rv tp of
    Nothing -> Left $ "Unknown variable " ++ show rv
    Just t ->
      let v' = makeExprVar rv lvl t
      in case v' of
        Just v -> Right v
        Nothing -> Left $ "Type error for variable " ++ show rv ++ ": unknown type " ++ show t
inferType _ _ _ (GConst c) = Right (makeExprConst c)
inferType _ _ _ (GConstBool c) = Right (makeExprConst c)
inferType _ _ _ (GSet c) = Left $ "Type error for set constant " ++ show c ++ ": unknown type." -- Right (TypeErasedExpr (ExprConst c))
inferType tp f bind (GBin op l r) = inferTypeBinary tp f bind op l r
inferType tp f bind (GUn op expr) = inferTypeUnary tp f bind op expr
inferType tp f bind (GExists v q n expr) = do
  r <- f q n
  inferType tp f (Map.insert v (r,0) bind) expr

inferTypeBinary :: VarType a
             => Map a TypeRep -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> BinOp -- ^ The operator to type check
             -> GExpr -- ^ The left hand side of the operator
             -> GExpr -- ^ The right hand side of the operator
             -> Either String (TypeErasedExpr a)
inferTypeBinary tp f bind op lhs rhs = do
  le <- inferType tp f bind lhs
  re <- inferType tp f bind rhs
  let tl = exprType le
  let tr = exprType re
  if not (tl == tr) then
      Left $ "Type " ++ show tl ++ " of lhs not equal to type " ++ show tr ++ " of rhs"
    else case toBoolOp op of
      Nothing -> case toRelOp op of
        Nothing -> case toIntOp op of
          Nothing -> Left $ "Unknown operator type: " ++ show op ++ "."
          Just intOp -> makeExprBinInt intOp le re
        Just relOp -> makeExprRel relOp le re
      Just boolOp -> makeExprBinBool boolOp le re

inferTypeUnary :: VarType a
             => Map a TypeRep -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> UnOp -- ^ The operator to type check
             -> GExpr -- ^ The left hand side of the operator
             -> Either String (TypeErasedExpr a)
inferTypeUnary tp f bind op expr =
  case op of
    GOpAlways -> do
      rexpr <- inferType tp f bind expr
      makeExprAlways rexpr
    GOpNext -> do
      rexpr <- inferType tp f (fmap (\(v,lvl) -> (v,lvl+1)) bind) expr
      makeExprNext rexpr
    GOpNot -> do
      rexpr <- inferType tp f bind expr
      makeExprNot rexpr
    GOpFinally Nothing -> Left "Unbounded finally not allowed"
    GOpFinally (Just n) -> do
      res <- Prelude.mapM (\i -> inferType tp f (fmap (\(v,lvl) -> (v,lvl+i)) bind) expr) [0..n]
      let t = exprType (head res)
      if t == boolRep then do
          first <- makeExprNext (head res)
          foldM (\x y -> do { eNext <- (makeExprNext y); makeExprBinBool Or x eNext }) first (tail res)
        else
          Left $ "Expected type Bool for operator finally but got type " ++ show t ++ "."

{-
-- | A GTL type can provide means to parse unary and binary operators of its type.
--   The default is to fail the parsing.
class Typeable t => GTLType t where
  -- | Type checks a binary operator of the given type.
  typeCheckBin :: (Ord a,Show a,GTLType t)
                 => Map a TypeRep -- ^ The type mapping
                 -> (Maybe String -> String -> Either String a) -- ^ A function to convert variable names
                 -> ExistsBinding a -- ^ All existentially bound variables
                 -> t -- ^ An instance of the type (can be `undefined')
                 -> BinOp -- ^ The operator to type check
                 -> GExpr -- ^ The left hand side of the operator
                 -> GExpr -- ^ The right hand side of the operator
                 -> Either String (Expr a t)
  typeCheckBin _ _ _ u op _ _ = Left $ "Operator "++show op++" is not of type "++show (typeOf u)
  typeCheckUn :: (Ord a,Show a,GTLType t)
                 => Map a TypeRep
                 -> (Maybe String -> String -> Either String a)
                 -> ExistsBinding a
                 -> t
                 -> UnOp -> GExpr -> Either String (Expr a t)
  typeCheckUn _ _ _ u op _ = Left $ "Operator "++show op++" is not of type "++show (typeOf u)

instance GTLType Bool where
  typeCheckBin tp f bind u op lhs rhs = case toBoolOp op of
    Nothing -> case toRelOp op of
      Nothing -> Left $ show op ++ " is not a boolean operator"
      Just rel -> do
        rl :: (Expr v Int) <- error "not implemented" -- <- typeCheck tp f bind lhs FIXME: get type from somewhere
        rr :: (Expr v Int) <- typeCheck tp f bind rhs
        return $ ExprRel rel (EqualExpr rl rr)
    Just rop -> do
      rl <- typeCheck tp f bind lhs
      rr <- typeCheck tp f bind rhs
      return $ ExprBinBool rop rl rr
  typeCheckUn tp f bind u op expr = do
    case op of
      GOpAlways -> do
        rexpr <- typeCheck tp f bind expr
        return $ ExprAlways rexpr
      GOpNext -> do
        rexpr <- typeCheck tp f (fmap (\(v,lvl) -> (v,lvl+1)) bind) expr
        return $ ExprNext rexpr
      GOpNot -> do
        rexpr <- typeCheck tp f bind expr
        return $ ExprNot rexpr
      GOpFinally Nothing -> Left "Unbounded finally not allowed"
      GOpFinally (Just n) -> do
        res <- mapM (\i -> typeCheck tp f (fmap (\(v,lvl) -> (v,lvl+i)) bind) expr) [0..n]
        return $ foldl1 (\x y -> ExprBinBool Or x (ExprNext y)) res

instance GTLType Int where
  typeCheckBin tp f bind u op lhs rhs = case toIntOp op of
    Nothing -> Left $ show op ++ " is not an integer operator"
    Just rop -> do
      rl <- typeCheck tp f bind lhs
      rr <- typeCheck tp f bind rhs
      return $ ExprBinInt rop rl rr
  typeCheckUn tp f bind u op expr = Left $ show op ++ " is not an integer operator"

-}

instance (Eq a,Eq v) => Eq (Expr v a) where
  (ExprVar n1 lvl1) == (ExprVar n2 lvl2) = n1 == n2 && lvl1 == lvl2
  (ExprConst i1) == (ExprConst i2) = i1 == i2
  (ExprBinInt op1 l1 r1) == (ExprBinInt op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprBinBool op1 l1 r1) == (ExprBinBool op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprRel rel1 args1) == (ExprRel rel2 args2) = rel1==rel2 && (castEqual args1 args2)
  (ExprElem n1 s1 p1) == (ExprElem n2 s2 p2) = n1==n2 && s1==s2 && p1==p2
  (ExprNot e1) == (ExprNot e2) = e1==e2
  (ExprAlways e1) == (ExprAlways e2) = e1==e2
  (ExprNext e1) == (ExprNext e2) = e1==e2
  _ == _ = False

instance (Ord a,Ord v) => Ord (Expr v a) where
  compare (ExprVar n1 lvl1) (ExprVar n2 lvl2) = case compare n1 n2 of
    EQ -> compare lvl1 lvl2
    r -> r
  compare (ExprVar _ _) _ = LT
  compare (ExprConst i1) (ExprConst i2) = compare i1 i2
  compare (ExprConst _) _ = LT
  compare (ExprBinInt op1 l1 r1) (ExprBinInt op2 l2 r2) = case compare op1 op2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprBinInt _ _ _) _ = LT
  compare (ExprBinBool op1 l1 r1) (ExprBinBool op2 l2 r2) = case compare op1 op2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprBinBool _ _ _) _ = LT
  compare (ExprRel rel1 args1) (ExprRel rel2 args2) = case compare rel1 rel2 of
    EQ -> castCompare args1 args2
    r -> r
  compare (ExprRel _ _) _ = LT
  compare (ExprElem n1 s1 p1) (ExprElem n2 s2 p2) = case compare (ExprVar n1 0:: Expr v Int) (ExprVar n2 0) of
    EQ -> case compare s1 s2 of
      EQ -> compare p1 p2
      r -> r
    r -> r
  compare (ExprElem _ _ _) _ = LT
  compare (ExprNot e1) (ExprNot e2) = compare e1 e2
  compare (ExprNot _) _ = LT
  compare (ExprAlways e1) (ExprAlways e2) = compare e1 e2
  compare (ExprAlways _) _ = LT
  compare (ExprNext e1) (ExprNext e2) = compare e1 e2
  compare (ExprNext _) _ = LT

instance (Show a,Show v) => Show (Expr v a) where
  show (ExprVar q lvl) = let suff = case lvl of
                               0 -> ""
                               _ -> "#"++show lvl
                         in show q++suff
  show (ExprConst i) = show i
  show (ExprBinInt op lhs rhs) = "(" ++ show lhs ++ ")" ++
                                 (case op of
                                     OpPlus -> "+"
                                     OpMinus -> "-"
                                     OpMult -> "*"
                                     OpDiv -> "/") ++
                                 "(" ++ show rhs ++ ")"
  show (ExprBinBool op lhs rhs) = "(" ++ show lhs ++ ") " ++
                                  (case op of
                                      And -> "and"
                                      Or -> "or"
                                      Implies -> "implies") ++
                                  " ("++show rhs++")"
  show (ExprRel rel (EqualExpr lhs rhs)) = "(" ++ show lhs ++ ") " ++
                               show rel ++
                               " (" ++ show rhs ++ ")"
  show (ExprElem q ints pos) = show (ExprVar q 0::Expr v Int) ++
                               (if pos then " in "
                                else " not in ") ++
                               show ints
  show (ExprNot e) = "not ("++show e++")"
  show (ExprAlways e) = "always ("++show e++")"
  show (ExprNext e) = "next ("++show e++")"

instance (VarType v, Binary a, Binary v, Typeable a, Ord a, BaseType a) => Binary (Expr v a) where
  put (ExprVar n hist) = put (0::Word8) >> put n >> put hist
  put (ExprConst c) = put (1::Word8) >> put c
  put (ExprBinInt op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprBinBool op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprRel rel (EqualExpr lhs rhs)) = put (3::Word8) >> put rel >> put lhs >> put rhs
  put (ExprElem n vals b) = put (4::Word8) >> put n >> put vals >> put b
  put (ExprNot e) = put (5::Word8) >> put e
  put (ExprAlways e) = put (6::Word8) >> put e
  put (ExprNext e) = put (7::Word8) >> put e
  get = do
    i <- get :: Get Word8
    case i of
      0 -> do
        n <- get
        hist <- get
        return (ExprVar n hist)
      1 -> do
        c <- get
        return (ExprConst c)
      2 -> case gcast (ExprBinInt undefined undefined undefined) of
        Nothing -> do
          op <- get
          lhs <- get
          rhs <- get
          castSer (ExprBinBool op lhs rhs)
        Just (_::Expr v a) -> do
          op <- get
          lhs <- get
          rhs <- get
          castSer (ExprBinInt op lhs rhs)
      3 -> do
        rel <- get
        lhs :: (Expr v a) <- error "not implemented" -- get -- TODO: hier muss der Typ genommen werden, der serialisiert wurde. a ist aber Bool!
        rhs :: (Expr v a) <- get
        castSer (ExprRel rel (EqualExpr lhs rhs))
      4 -> do
        n <- get
        vals <- get
        b <- get
        castSer (ExprElem n vals b)
      5 -> do
        e <- get
        castSer (ExprNot e)
      6 -> do
        e <- get
        castSer (ExprAlways e)
      7 -> do
        e <- get
        castSer (ExprNext e)

-- | Pushes a negation as far into the formula as possible by applying simplification rules.
pushNot :: Expr v Bool -> Expr v Bool
pushNot (ExprNot x) = pushNot' x
  where
    pushNot' :: Expr v Bool -> Expr v Bool
    pushNot' (ExprRel rel (EqualExpr x y))
      = ExprRel (case rel of
                    BinLT -> BinGTEq
                    BinLTEq -> BinGT
                    BinGT -> BinLTEq
                    BinGTEq -> BinLT
                    BinEq -> BinNEq
                    BinNEq -> BinEq) (EqualExpr x y)
    pushNot' (ExprNot x) = x
    pushNot' (ExprBinBool op x y) = case op of
      And -> ExprBinBool Or (pushNot' x) (pushNot' y)
      Or -> ExprBinBool And (pushNot' x) (pushNot' y)
      Implies -> ExprBinBool And (pushNot x) (pushNot' y)
    pushNot' (ExprAlways x) = error "always operator must not be negated"
    pushNot' (ExprNext x) = ExprNext (pushNot' x)
    pushNot' (ExprElem n lst neg) = ExprElem n lst (not neg)
pushNot (ExprBinBool op x y) = ExprBinBool op (pushNot x) (pushNot y)
pushNot (ExprAlways x) = ExprAlways (pushNot x)
pushNot (ExprNext x) = ExprNext (pushNot x)
pushNot expr = expr

-- | Extracts all variables with their level of history from an expression.
getVars :: Expr v a -> [(v,Integer)]
getVars (ExprVar n lvl) = [(n,lvl)]
getVars (ExprConst _) = []
getVars (ExprBinInt _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprBinBool _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprRel _ (EqualExpr lhs rhs)) = getVars lhs ++ getVars rhs
getVars (ExprElem n _ _) = [(n,0)]
getVars (ExprNot e) = getVars e
getVars (ExprAlways e) = getVars e
getVars (ExprNext e) = getVars e

-- | Extracts the maximum level of history for each variable in the expression.
maximumHistory :: Ord v => Expr v a -> Map v Integer
maximumHistory exprs = foldl (\mp (n,lvl) -> Map.insertWith max n lvl mp) Map.empty (getVars exprs)

-- | Change the type of the variables in an expression.
mapVars :: (VarType w, Binary w, Eq w) => (v -> w) -> Expr v a -> Expr w a
mapVars f (ExprVar n lvl) = ExprVar (f n) lvl
mapVars f (ExprConst c) = ExprConst c
mapVars f (ExprBinInt op lhs rhs) = ExprBinInt op (mapVars f lhs) (mapVars f rhs)
mapVars f (ExprBinBool op lhs rhs) = ExprBinBool op (mapVars f lhs) (mapVars f rhs)
mapVars f (ExprRel rel (EqualExpr lhs rhs)) = ExprRel rel (EqualExpr (mapVars f lhs) (mapVars f rhs))
mapVars f (ExprElem n vals b) = ExprElem (f n) vals b
mapVars f (ExprNot e) = ExprNot (mapVars f e)
mapVars f (ExprAlways e) = ExprAlways (mapVars f e)
mapVars f (ExprNext e) = ExprNext (mapVars f e)

-- | Binary boolean operators with the traditional semantics.
data BoolOp = And     -- ^ &#8896;
            | Or      -- ^ &#8897;
            | Implies -- ^ &#8658;
            deriving (Show,Eq,Ord,Enum)

instance Binary BoolOp where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> BoolOp) get

-- | Arithmetik binary operators.
data IntOp = OpPlus -- ^ +
           | OpMinus -- ^ \-
           | OpMult -- ^ \*
           | OpDiv -- ^ /
           deriving (Show,Eq,Ord,Enum)

instance Binary IntOp where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> IntOp) get

-- | Integer relations.
data Relation = BinLT -- ^ <
              | BinLTEq -- ^ <=
              | BinGT -- ^ \>
              | BinGTEq -- ^ \>=
              | BinEq -- ^ =
              | BinNEq -- ^ !=
              deriving (Eq,Ord,Enum)

instance Binary Relation where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> Relation) get

instance Show Relation where
  show BinLT = "<"
  show BinLTEq = "<="
  show BinGT = ">"
  show BinGTEq = ">="
  show BinEq = "="
  show BinNEq = "!="

-- | Convert a `String' into a type representation. Only covers types which are allowed in the GTL.
parseGTLType :: String -> Maybe TypeRep
parseGTLType "int" = Just (typeOf (undefined::Int))
parseGTLType "bool" = Just (typeOf (undefined::Bool))
parseGTLType _ = Nothing

-- | Lift `gcast' in a monad and fail with an error if the cast fails
castSer :: (Typeable a,Typeable b,Monad m) => c a -> m (c b)
castSer = maybe (error "Internal serialization error") return . gcast


-- | Cast a binary operator into a boolean operator. Returns `Nothing' if the cast fails.
toBoolOp :: BinOp -> Maybe BoolOp
toBoolOp GOpAnd = Just And
toBoolOp GOpOr = Just Or
toBoolOp GOpImplies = Just Implies
toBoolOp _ = Nothing

-- | Cast a binary operator into a relation. Returns `Nothing' if the cast fails.
toRelOp :: BinOp -> Maybe Relation
toRelOp GOpLessThan = Just BinLT
toRelOp GOpLessThanEqual = Just BinLTEq
toRelOp GOpGreaterThan = Just BinGT
toRelOp GOpGreaterThanEqual = Just BinGTEq
toRelOp GOpEqual = Just BinEq
toRelOp GOpNEqual = Just BinNEq
toRelOp _ = Nothing

-- | Cast a binary operator into an element operator. Returns `Nothing' if the cast fails.
toElemOp :: BinOp -> Maybe Bool
toElemOp GOpIn = Just True
toElemOp GOpNotIn = Just False
toElemOp _ = Nothing

-- | Binds variables to other variables from the past.
type ExistsBinding a = Map String (a,Integer)

-- | Cast a binary operator into an arithmetic operator. Returns `Nothing' if the cast fails.
toIntOp :: BinOp -> Maybe IntOp
toIntOp GOpPlus = Just OpPlus
toIntOp GOpMinus = Just OpMinus
toIntOp GOpMult = Just OpMult
toIntOp GOpDiv = Just OpDiv
toIntOp _ = Nothing

-- | Negates a relation
relNot :: Relation -> Relation
relNot rel = case rel of
  BinLT -> BinGTEq
  BinLTEq -> BinGT
  BinGT -> BinLTEq
  BinGTEq -> BinLT
  BinEq -> BinNEq
  BinNEq -> BinEq

-- | Switches the operands of a relation.
--   Turns x < y into y > x.
relTurn :: Relation -> Relation
relTurn rel = case rel of
  BinLT -> BinGT
  BinLTEq -> BinGTEq
  BinGT -> BinLT
  BinGTEq -> BinLTEq
  BinEq -> BinEq
  BinNEq -> BinNEq

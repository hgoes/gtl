{-# LANGUAGE GADTs,DeriveDataTypeable,ScopedTypeVariables #-}
module Language.GTL.Syntax where

import Language.GTL.Token (UnOp(..),BinOp(..))
import Control.Monad.Error
import Data.Map as Map
import Data.Binary
import Data.Word
import Data.Typeable

data Declaration = Model ModelDecl
                 | Connect ConnectDecl
                 | Verify VerifyDecl
                 deriving Show

data ModelDecl = ModelDecl
                 { modelName :: String
                 , modelType :: String
                 , modelArgs :: [String]
                 , modelContract :: [Formula]
                 , modelInits :: [(String,InitExpr)]
                 } deriving Show

data ConnectDecl = ConnectDecl
                   { connectFromModel :: String
                   , connectFromVariable :: String
                   , connectToModel :: String
                   , connectToVariable :: String
                   } deriving Show

data VerifyDecl = VerifyDecl
                  { verifyFormulas :: [Formula]
                  } deriving Show

type Formula = Expr Bool

data GExpr = GBin BinOp GExpr GExpr
           | GUn UnOp GExpr
           | GConst Int
           | GVar (Maybe String) String
           | GSet [Integer]
           | GExists String (Maybe String) String GExpr
           deriving (Show,Eq,Ord)

data Expr a where
  ExprVar :: Maybe String -> String -> Integer -> Expr a
  ExprConst :: a -> Expr a
  ExprBinInt :: IntOp -> Expr Int -> Expr Int -> Expr Int
  ExprBinBool :: BoolOp -> Expr Bool -> Expr Bool -> Expr Bool
  ExprRel :: Relation -> Expr Int -> Expr Int -> Expr Bool
  ExprElem :: Maybe String -> String -> [Integer] -> Bool -> Expr Bool
  ExprNot :: Expr Bool -> Expr Bool
  ExprAlways :: Expr Bool -> Expr Bool
  ExprNext :: Expr Bool -> Expr Bool
  deriving Typeable

castSer :: (Typeable a,Typeable b,Monad m) => a -> m b
castSer = maybe (error "Internal serialization error") return . cast

instance (Binary a,Typeable a) => Binary (Expr a) where
  put (ExprVar q n hist) = put (0::Word8) >> put q >> put n >> put hist
  put (ExprConst c) = put (1::Word8) >> put c
  put (ExprBinInt op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprBinBool op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprRel rel lhs rhs) = put (3::Word8) >> put rel >> put lhs >> put rhs
  put (ExprElem q n vals b) = put (4::Word8) >> put q >> put n >> put vals >> put b
  put (ExprNot e) = put (5::Word8) >> put e
  put (ExprAlways e) = put (6::Word8) >> put e
  put (ExprNext e) = put (7::Word8) >> put e
  get = do
    i <- get :: Get Word8
    case i of
      0 -> do
        q <- get
        n <- get
        hist <- get
        return (ExprVar q n hist)
      1 -> do
        c <- get
        return (ExprConst c)
      2 -> case cast (ExprBinInt undefined undefined undefined) of
        Nothing -> do
          op <- get
          lhs <- get
          rhs <- get
          castSer (ExprBinBool op lhs rhs)
        Just (_::Expr a) -> do
          op <- get
          lhs <- get
          rhs <- get
          castSer (ExprBinInt op lhs rhs)
      3 -> do
        rel <- get
        lhs <- get
        rhs <- get
        castSer (ExprRel rel lhs rhs)
      4 -> do
        q <- get
        n <- get
        vals <- get
        b <- get
        castSer (ExprElem q n vals b)
      5 -> do
        e <- get
        castSer (ExprNot e)
      6 -> do
        e <- get
        castSer (ExprAlways e)
      7 -> do
        e <- get
        castSer (ExprNext e)

toBoolOp :: BinOp -> Maybe BoolOp
toBoolOp GOpAnd = Just And
toBoolOp GOpOr = Just Or
toBoolOp GOpImplies = Just Implies
toBoolOp _ = Nothing

toRelOp :: BinOp -> Maybe Relation
toRelOp GOpLessThan = Just BinLT
toRelOp GOpLessThanEqual = Just BinLTEq
toRelOp GOpGreaterThan = Just BinGT
toRelOp GOpGreaterThanEqual = Just BinGTEq
toRelOp GOpEqual = Just BinEq
toRelOp GOpNEqual = Just BinNEq
toRelOp _ = Nothing

toElemOp :: BinOp -> Maybe Bool
toElemOp GOpIn = Just True
toElemOp GOpNotIn = Just False
toElemOp _ = Nothing

type ExistsBinding = Map String (Maybe String,String,Integer)

typeCheckBool :: ExistsBinding -> GExpr -> Either String (Expr Bool)
typeCheckBool bind (GVar q n) = case q of
  Just _ -> Right (ExprVar q n 0)
  Nothing -> case Map.lookup n bind of
    Nothing -> Right (ExprVar q n 0)
    Just (q',n',lvl) -> Right (ExprVar q' n' lvl)
typeCheckBool _ (GConst c) = Left $ "Expression "++show c++" has type int, expected bool"
typeCheckBool _ (GSet c) = Left $ "Expression "++show c++" has type {int}, expected bool"
typeCheckBool bind (GBin op l r) = case toBoolOp op of
  Just bop -> do
    res_l <- typeCheckBool bind l
    res_r <- typeCheckBool bind r
    return $ ExprBinBool bop res_l res_r
  Nothing -> case toRelOp op of
    Just rop -> do
      res_l <- typeCheckInt bind l
      res_r <- typeCheckInt bind r
      return $ ExprRel rop res_l res_r
    Nothing -> case toElemOp op of
      Just eop -> case l of
        GVar q n -> case r of
          GSet vs -> Right (ExprElem q n vs eop)
          _ -> Left "Wrong right hand side for in operator"
        _ -> Left "Wrong left hand side for in operator"
      Nothing -> error $ "Invalid operator: "++show op
typeCheckBool bind (GUn op expr) = case op of
  GOpNot -> do
    res <- typeCheckBool bind expr
    return $ ExprNot res
  GOpAlways -> do
    res <- typeCheckBool Map.empty expr  -- Maybe find a nicer solution, an error perhaps?
    return $ ExprAlways res
  GOpNext -> do
    res <- typeCheckBool (fmap (\(q,n,lvl) -> (q,n,lvl+1)) bind) expr
    return $ ExprNext res
  GOpFinally Nothing -> error "Unbounded finally not allowed"
  GOpFinally (Just n) -> do
    res <- mapM (\i -> typeCheckBool (fmap (\(q,n,lvl) -> (q,n,lvl+i)) bind) expr) [0..n]
    return $ foldl1 (\x y -> ExprBinBool Or x (ExprNext y)) res
typeCheckBool bind (GExists v q n expr) = typeCheckBool (Map.insert v (q,n,0) bind) expr

toIntOp :: BinOp -> Maybe IntOp
toIntOp GOpPlus = Just OpPlus
toIntOp GOpMinus = Just OpMinus
toIntOp GOpMult = Just OpMult
toIntOp GOpDiv = Just OpDiv
toIntOp _ = Nothing

typeCheckInt :: ExistsBinding -> GExpr -> Either String (Expr Int)
typeCheckInt bind (GVar q n) = case q of
  Just _ -> Right (ExprVar q n 0)
  Nothing -> case Map.lookup n bind of
    Nothing -> Right (ExprVar q n 0)
    Just (q',n',lvl) -> Right (ExprVar q' n' lvl)
typeCheckInt _ (GConst c) = Right (ExprConst c)
typeCheckInt bind (GBin op l r) = case toIntOp op of
  Just iop -> do
    res_l <- typeCheckInt bind l
    res_r <- typeCheckInt bind r
    return $ ExprBinInt iop res_l res_r
  Nothing -> Left $ "Operator "++show op++" has wrong type, expected: int"
typeCheckInt _ (GUn op _) = Left $ "Operator "++show op++" has wrong type, expected: int"
typeCheckInt _ (GSet vs) = Left $ "Expression "++show vs++" has type {int}, expected int"
      
instance Eq a => Eq (Expr a) where
  (ExprVar q1 n1 lvl1) == (ExprVar q2 n2 lvl2) = q1 == q2 && n1 == n2 && lvl1 == lvl2
  (ExprConst i1) == (ExprConst i2) = i1 == i2
  (ExprBinInt op1 l1 r1) == (ExprBinInt op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprBinBool op1 l1 r1) == (ExprBinBool op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprRel rel1 l1 r1) == (ExprRel rel2 l2 r2) = rel1==rel2 && l1==l2 && r1==r2
  (ExprElem q1 n1 s1 p1) == (ExprElem q2 n2 s2 p2) = q1==q2 && n1==n2 && s1==s2 && p1==p2
  (ExprNot e1) == (ExprNot e2) = e1==e2
  (ExprAlways e1) == (ExprAlways e2) = e1==e2
  (ExprNext e1) == (ExprNext e2) = e1==e2
  _ == _ = False

instance Ord a => Ord (Expr a) where
  compare (ExprVar q1 n1 lvl1) (ExprVar q2 n2 lvl2) = case compare q1 q2 of
    EQ -> case compare n1 n2 of
      EQ -> compare lvl1 lvl2
      r -> r
    r -> r
  compare (ExprVar _ _ _) _ = LT
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
  compare (ExprRel rel1 l1 r1) (ExprRel rel2 l2 r2) = case compare rel1 rel2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprRel _ _ _) _ = LT
  compare (ExprElem q1 n1 s1 p1) (ExprElem q2 n2 s2 p2) = case compare (ExprVar q1 n1 0::Expr Int) (ExprVar q2 n2 0) of
    EQ -> case compare s1 s2 of
      EQ -> compare p1 p2
      r -> r
    r -> r
  compare (ExprElem _ _ _ _) _ = LT
  compare (ExprNot e1) (ExprNot e2) = compare e1 e2
  compare (ExprNot _) _ = LT
  compare (ExprAlways e1) (ExprAlways e2) = compare e1 e2
  compare (ExprAlways _) _ = LT
  compare (ExprNext e1) (ExprNext e2) = compare e1 e2
  compare (ExprNext _) _ = LT

instance Show a => Show (Expr a) where
  show (ExprVar q name lvl) = let suff = case lvl of
                                    0 -> ""
                                    _ -> "#"++show lvl
                                  pref = case q of
                                    Nothing -> name
                                    Just rq -> rq ++ "." ++ name
                              in pref++suff
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
  show (ExprRel rel lhs rhs) = "(" ++ show lhs ++ ") " ++
                               (case rel of
                                   BinLT -> "<"
                                   BinLTEq -> "<="
                                   BinGT -> ">"
                                   BinGTEq -> ">="
                                   BinEq -> "="
                                   BinNEq -> "!=") ++
                               " (" ++ show rhs ++ ")"
  show (ExprElem q name ints pos) = show (ExprVar q name 0::Expr Int) ++
                                    (if pos then " in "
                                     else " not in ") ++
                                    show ints
  show (ExprNot e) = "not ("++show e++")"
  show (ExprAlways e) = "always ("++show e++")"
  show (ExprNext e) = "next ("++show e++")"

data BoolOp = And | Or | Implies deriving (Show,Eq,Ord,Enum)

instance Binary BoolOp where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> BoolOp) get

data IntOp = OpPlus | OpMinus | OpMult | OpDiv deriving (Show,Eq,Ord,Enum)

instance Binary IntOp where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> IntOp) get

data Relation = BinLT
              | BinLTEq
              | BinGT
              | BinGTEq
              | BinEq
              | BinNEq
              deriving (Show,Eq,Ord,Enum)

instance Binary Relation where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> Relation) get

data InitExpr = InitAll
              | InitOne Integer
              deriving (Show,Eq)

relNot :: Relation -> Relation
relNot rel = case rel of
  BinLT -> BinGTEq
  BinLTEq -> BinGT
  BinGT -> BinLTEq
  BinGTEq -> BinLT
  BinEq -> BinNEq
  BinNEq -> BinEq

relTurn :: Relation -> Relation
relTurn rel = case rel of
  BinLT -> BinGT
  BinLTEq -> BinGTEq
  BinGT -> BinLT
  BinGTEq -> BinLTEq
  BinEq -> BinEq
  BinNEq -> BinNEq

pushNot :: Formula -> Formula
pushNot (ExprNot x) = pushNot' x
pushNot (ExprBinBool op x y) = ExprBinBool op (pushNot x) (pushNot y)
pushNot (ExprAlways x) = ExprAlways (pushNot x)
pushNot (ExprNext x) = ExprNext (pushNot x)
pushNot expr = expr

pushNot' :: Formula -> Formula
pushNot' (ExprRel rel x y)
  = ExprRel (case rel of
                BinLT -> BinGTEq
                BinLTEq -> BinGT
                BinGT -> BinLTEq
                BinGTEq -> BinLT
                BinEq -> BinNEq
                BinNEq -> BinEq) x y
pushNot' (ExprNot x) = x
pushNot' (ExprBinBool op x y) = case op of
  And -> ExprBinBool Or (pushNot' x) (pushNot' y)
  Or -> ExprBinBool And (pushNot' x) (pushNot' y)
  Implies -> ExprBinBool And (pushNot x) (pushNot' y)
pushNot' (ExprAlways x) = error "always operator must not be negated"
pushNot' (ExprNext x) = ExprNext (pushNot' x)
pushNot' (ExprElem p n lst neg) = ExprElem p n lst (not neg)

getVars :: Expr a -> [(Maybe String,String,Integer)]
getVars (ExprVar q n lvl) = [(q,n,lvl)]
getVars (ExprConst _) = []
getVars (ExprBinInt _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprBinBool _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprRel _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprElem q n _ _) = [(q,n,0)]
getVars (ExprNot e) = getVars e
getVars (ExprAlways e) = getVars e
getVars (ExprNext e) = getVars e

maximumHistory :: [Expr a] -> Map (Maybe String,String) Integer
maximumHistory exprs = foldl (\mp (q,n,lvl) -> Map.insertWith max (q,n) lvl mp) Map.empty (concat $ fmap getVars exprs)
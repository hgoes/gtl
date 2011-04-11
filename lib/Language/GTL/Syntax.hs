{-# LANGUAGE GADTs,DeriveDataTypeable,ScopedTypeVariables,FlexibleInstances,TypeFamilies #-}
-- | Data types representing a parsed GTL file.
module Language.GTL.Syntax where

import Language.GTL.Token (UnOp(..),BinOp(..))
import Control.Monad.Error
import Data.Map as Map
import Data.Binary
import Data.Word
import Data.Typeable

-- | A GTL file is a list of declarations.
data Declaration = Model ModelDecl -- ^ Declares a model.
                 | Connect ConnectDecl -- ^ Declares a connection between two models.
                 | Verify VerifyDecl -- ^ Declares a property that needs to be verified.
                 deriving Show

-- | Declares a synchronous model.
data ModelDecl = ModelDecl
                 { modelName :: String -- ^ The name of the model in the GTL formalism.
                 , modelType :: String -- ^ The synchronous formalism the model is written in (for example /scade/)
                 , modelArgs :: [String] -- ^ Arguments specific to the synchronous formalism, for example in which file the model is specified etc.
                 , modelContract :: [GExpr] -- ^ A list of contracts that this model fulfills.
                 , modelInits :: [(String,InitExpr)] -- ^ A list of initializations for the variables of the model.
                 , modelInputs :: Map String TypeRep -- ^ Declared inputs of the model with their corresponding type
                 , modelOutputs :: Map String TypeRep -- ^ Declared outputs of a model
                 } deriving Show

-- | Declares a connection between two variables
data ConnectDecl = ConnectDecl
                   { connectFromModel :: String -- ^ Model of the source variable
                   , connectFromVariable :: String -- ^ Name of the source variable
                   , connectToModel :: String -- ^ Model of the target variable
                   , connectToVariable :: String -- ^ Name of the target variable
                   } deriving Show

-- | A list of formulas to verify.
data VerifyDecl = VerifyDecl
                  { verifyFormulas :: [GExpr] -- ^ The formulas to be verified.
                  } deriving Show

-- | An untyped expression type.
--   Used internally in the parser.
data GExpr = GBin BinOp GExpr GExpr
           | GUn UnOp GExpr
           | GConst Int
           | GConstBool Bool
           | GVar (Maybe String) String
           | GSet [Integer]
           | GExists String (Maybe String) String GExpr
           deriving (Show,Eq,Ord)

-- | A type-safe expression type.
--   /v/ is the type of variables (for example `String') and /a/ is the type of the expression.
data Expr v a where
  ExprVar :: v -> Integer -> Expr v a -- A variable. Can have any type.
  ExprConst :: a -> Expr v a -- A constant. Has the type of the constant.
  ExprBinInt :: IntOp -> Expr v Int -> Expr v Int -> Expr v Int -- A binary integer operation that takes two integer expressions and returns an integer expression.
  ExprBinBool :: BoolOp -> Expr v Bool -> Expr v Bool -> Expr v Bool -- A binary boolean operation.
  ExprRel :: Relation -> Expr v Int -> Expr v Int -> Expr v Bool -- An integer relation.
  ExprElem :: v -> [Integer] -> Bool -> Expr v Bool -- `ExprElem' /x/ /xs/ `True' means: "/x/ is element of the list /xs/".
  ExprNot :: Expr v Bool -> Expr v Bool
  ExprAlways :: Expr v Bool -> Expr v Bool
  ExprNext :: Expr v Bool -> Expr v Bool
  deriving Typeable

parseGTLType :: String -> Maybe TypeRep
parseGTLType "int" = Just (typeOf (undefined::Int))
parseGTLType "bool" = Just (typeOf (undefined::Bool))
parseGTLType _ = Nothing

-- | Lift `gcast' in a monad and fail with an error if the cast fails
castSer :: (Typeable a,Typeable b,Monad m) => c a -> m (c b)
castSer = maybe (error "Internal serialization error") return . gcast

instance (Binary a,Binary v,Typeable a) => Binary (Expr v a) where
  put (ExprVar n hist) = put (0::Word8) >> put n >> put hist
  put (ExprConst c) = put (1::Word8) >> put c
  put (ExprBinInt op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprBinBool op lhs rhs) = put (2::Word8) >> put op >> put lhs >> put rhs
  put (ExprRel rel lhs rhs) = put (3::Word8) >> put rel >> put lhs >> put rhs
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
        lhs <- get
        rhs <- get
        castSer (ExprRel rel lhs rhs)
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

typeCheckBool :: ExistsBinding (Maybe String,String) -> GExpr -> Either String (Expr (Maybe String,String) Bool)
typeCheckBool bind expr = typeCheck' Map.empty (\q n -> Right (q,n)) bind expr undefined

typeCheckInt :: ExistsBinding (Maybe String,String) -> GExpr -> Either String (Expr (Maybe String,String) Int)
typeCheckInt bind expr = typeCheck' Map.empty (\q n -> Right (q,n)) bind expr undefined

typeCheck :: (Ord a,Show a,GTLType t,Show t)
             => Map a TypeRep
             -> (Maybe String -> String -> Either String a)
             -> GExpr
             -> Either String (Expr a t)
typeCheck tp f expr = typeCheck' tp f Map.empty expr undefined

-- | Typecheck an untyped expression. Converts it into the `Expr' type which is strongly typed.
--   Returns either an error message or the resulting expression of type `Bool'.
typeCheck' :: (Ord a,Show a,GTLType t,Show t)
                 => Map a TypeRep -- ^ Type mapping
                 -> (Maybe String -> String -> Either String a)
                 -> ExistsBinding a -- ^ A map of bound variables
                 -> GExpr -- ^ The expression to convert
                 -> t -- ^ undefined
                 -> Either String (Expr a t)
typeCheck' tp f bind (GVar q n) u = do
  let nl = do
        v <- f q n
        return (v,0)
  (rv,lvl) <- case q of
    Nothing -> case Map.lookup n bind of 
      Just (v,lvl) -> return (v,lvl)
      Nothing -> nl
    _ -> nl
  let rvar = ExprVar rv lvl
  case Map.lookup rv tp of
    Nothing -> Left $ "Unknown variable "++show rvar
    Just t -> if typeOf u == t
              then Right rvar
              else Left $ "Type error for variable "++show rvar++": Expected to be "++show (typeOf u)++", but is "++show t
typeCheck' _ _ _ (GConst c) u = case cast c of 
  Nothing -> Left $ "Expression "++show c++" has type int, expected "++show (typeOf u)
  Just r -> return $ ExprConst r
typeCheck' _ _ _ (GConstBool c) u = case cast c of
  Nothing -> Left $ "Expression "++show c++" has type bool, expected "++show (typeOf u)
  Just r -> return $ ExprConst r
typeCheck' _ _ _ (GSet c) u = case cast c of
  Nothing -> Left $ "Expression "++show c++" has type {int}, expected "++show (typeOf u)
  Just r -> return $ ExprConst r
typeCheck' tp f bind (GBin op l r) u = typeCheckBin tp f bind u op l r
typeCheck' tp f bind (GUn op expr) u = typeCheckUn tp f bind u op expr
typeCheck' tp f bind (GExists v q n expr) u = do
  r <- f q n
  typeCheck' tp f (Map.insert v (r,0) bind) expr u

class Typeable t => GTLType t where
  typeCheckBin :: (Ord a,Show a,GTLType t)
                 => Map a TypeRep
                 -> (Maybe String -> String -> Either String a)
                 -> ExistsBinding a
                 -> t
                 -> BinOp -> GExpr -> GExpr -> Either String (Expr a t)
  typeCheckUn :: (Ord a,Show a,GTLType t)
                 => Map a TypeRep
                 -> (Maybe String -> String -> Either String a)
                 -> ExistsBinding a
                 -> t
                 -> UnOp -> GExpr -> Either String (Expr a t)

instance GTLType Bool where
  typeCheckBin tp f bind u op lhs rhs = case toBoolOp op of
    Nothing -> case toRelOp op of
      Nothing -> Left $ show op ++ " is not a boolean operator"
      Just rel -> do
        rl <- typeCheck' tp f bind lhs undefined
        rr <- typeCheck' tp f bind rhs undefined
        return $ ExprRel rel rl rr
    Just rop -> do
      rl <- typeCheck' tp f bind lhs undefined
      rr <- typeCheck' tp f bind rhs undefined
      return $ ExprBinBool rop rl rr
  typeCheckUn tp f bind u op expr = do
    case op of
      GOpAlways -> do
        rexpr <- typeCheck' tp f bind expr undefined
        return $ ExprAlways rexpr
      GOpNext -> do
        rexpr <- typeCheck' tp f (fmap (\(v,lvl) -> (v,lvl+1)) bind) expr undefined
        return $ ExprNext rexpr
      GOpNot -> do
        rexpr <- typeCheck' tp f bind expr undefined
        return $ ExprNot rexpr
      GOpFinally Nothing -> Left "Unbounded finally not allowed"
      GOpFinally (Just n) -> do
        res <- mapM (\i -> typeCheck' tp f (fmap (\(v,lvl) -> (v,lvl+i)) bind) expr undefined) [0..n]
        return $ foldl1 (\x y -> ExprBinBool Or x (ExprNext y)) res

instance GTLType Int where
  typeCheckBin tp f bind u op lhs rhs = case toIntOp op of
    Nothing -> Left $ show op ++ " is not an integer operator"
    Just rop -> do
      rl <- typeCheck' tp f bind lhs undefined
      rr <- typeCheck' tp f bind rhs undefined
      return $ ExprBinInt rop rl rr
  typeCheckUn tp f bind u op expr = Left $ show op ++ " is not an integer operator"    
  
-- | Cast a binary operator into an arithmetic operator. Returns `Nothing' if the cast fails.
toIntOp :: BinOp -> Maybe IntOp
toIntOp GOpPlus = Just OpPlus
toIntOp GOpMinus = Just OpMinus
toIntOp GOpMult = Just OpMult
toIntOp GOpDiv = Just OpDiv
toIntOp _ = Nothing

{-
-- | Same as `typeCheckBool' but returns an expression of type `Int'.
typeCheckInt :: ExistsBinding -> GExpr -> Either String (Expr (Maybe String,String) Int)
typeCheckInt bind (GVar q n) = case q of
  Just _ -> Right (ExprVar (q,n) 0)
  Nothing -> case Map.lookup n bind of
    Nothing -> Right (ExprVar (q,n) 0)
    Just (q',n',lvl) -> Right (ExprVar (q',n') lvl)
typeCheckInt _ (GConst c) = Right (ExprConst c)
typeCheckInt bind (GBin op l r) = case toIntOp op of
  Just iop -> do
    res_l <- typeCheckInt bind l
    res_r <- typeCheckInt bind r
    return $ ExprBinInt iop res_l res_r
  Nothing -> Left $ "Operator "++show op++" has wrong type, expected: int"
typeCheckInt _ (GUn op _) = Left $ "Operator "++show op++" has wrong type, expected: int"
typeCheckInt _ (GSet vs) = Left $ "Expression "++show vs++" has type {int}, expected int" -}
      
instance (Eq a,Eq v) => Eq (Expr v a) where
  (ExprVar n1 lvl1) == (ExprVar n2 lvl2) = n1 == n2 && lvl1 == lvl2
  (ExprConst i1) == (ExprConst i2) = i1 == i2
  (ExprBinInt op1 l1 r1) == (ExprBinInt op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprBinBool op1 l1 r1) == (ExprBinBool op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprRel rel1 l1 r1) == (ExprRel rel2 l2 r2) = rel1==rel2 && l1==l2 && r1==r2
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
  compare (ExprRel rel1 l1 r1) (ExprRel rel2 l2 r2) = case compare rel1 rel2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprRel _ _ _) _ = LT
  compare (ExprElem n1 s1 p1) (ExprElem n2 s2 p2) = case compare (ExprVar n1 0::Expr v Int) (ExprVar n2 0) of
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
  show (ExprRel rel lhs rhs) = "(" ++ show lhs ++ ") " ++
                               (case rel of
                                   BinLT -> "<"
                                   BinLTEq -> "<="
                                   BinGT -> ">"
                                   BinGTEq -> ">="
                                   BinEq -> "="
                                   BinNEq -> "!=") ++
                               " (" ++ show rhs ++ ")"
  show (ExprElem q ints pos) = show (ExprVar q 0::Expr v Int) ++
                               (if pos then " in "
                                else " not in ") ++
                               show ints
  show (ExprNot e) = "not ("++show e++")"
  show (ExprAlways e) = "always ("++show e++")"
  show (ExprNext e) = "next ("++show e++")"

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
              deriving (Show,Eq,Ord,Enum)

instance Binary Relation where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> Relation) get

-- | Information about the initialization of a variable.
data InitExpr = InitAll -- ^ The variable is initialized with all possible values.
              | InitOne Integer -- ^ The variable is initialized with a specific value.
              deriving (Show,Eq)

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

-- | Pushes a negation as far into the formula as possible by applying simplification rules.
pushNot :: Expr v Bool -> Expr v Bool
pushNot (ExprNot x) = pushNot' x
  where
    pushNot' :: Expr v Bool -> Expr v Bool
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
getVars (ExprRel _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprElem n _ _) = [(n,0)]
getVars (ExprNot e) = getVars e
getVars (ExprAlways e) = getVars e
getVars (ExprNext e) = getVars e

-- | Extracts the maximum level of history for each variable in the expression.
maximumHistory :: Ord v => Expr v a -> Map v Integer
maximumHistory exprs = foldl (\mp (n,lvl) -> Map.insertWith max n lvl mp) Map.empty (getVars exprs)

-- | Change the type of the variables in an expression.
mapVars :: (v -> w) -> Expr v a -> Expr w a
mapVars f (ExprVar n lvl) = ExprVar (f n) lvl
mapVars f (ExprConst c) = ExprConst c
mapVars f (ExprBinInt op lhs rhs) = ExprBinInt op (mapVars f lhs) (mapVars f rhs)
mapVars f (ExprBinBool op lhs rhs) = ExprBinBool op (mapVars f lhs) (mapVars f rhs)
mapVars f (ExprRel rel lhs rhs) = ExprRel rel (mapVars f lhs) (mapVars f rhs)
mapVars f (ExprElem n vals b) = ExprElem (f n) vals b
mapVars f (ExprNot e) = ExprNot (mapVars f e)
mapVars f (ExprAlways e) = ExprAlways (mapVars f e)
mapVars f (ExprNext e) = ExprNext (mapVars f e)
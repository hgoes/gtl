{-# LANGUAGE ScopedTypeVariables,GADTs,DeriveDataTypeable,FlexibleInstances,
  ExistentialQuantification, StandaloneDeriving, TypeSynonymInstances #-}
{-| Provides the expression data type as well as the type-checking algorithm.
 -}
module Language.GTL.Expression where

import Language.GTL.Parser.Syntax
import Language.GTL.Parser.Token
import Language.GTL.Buchi
import Language.GTL.Types

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
import Data.Set as Set
import Data.List as List (find)
import Data.Either
import Data.Foldable
import Prelude hiding (foldl,foldl1,concat)

data GTLTypeVal = IntVal Int | BoolVal Bool
  deriving (Show, Eq, Ord)

-- | GTL variables associated with their
-- name, time reference and type.
data Variable v = Variable
                  { name :: v
                  , time :: Integer
                  , varType :: GTLType
                  } deriving (Eq, Ord)

-- | Representation of typed constants
data Constant = Constant
                  { value :: GTLTypeVal   -- maybe change to sum type
                  , constType :: GTLType
                  } deriving (Show, Eq, Ord)

data GTLOp = IntOp IntOp deriving (Eq, Ord)

-- | Dynamically typed
data VarType v => Term v
  = VarExpr (Variable v)
  | ConstExpr Constant
  | BinExpr GTLType GTLOp (Term v) (Term v)

-- | In between
data VarType v => BoolExpr v
  = RelExpr Relation (Term v) (Term v)
  | ElemExpr (Variable v) [Constant] Bool
  | BoolConst Bool
  | BoolVar (Variable v) -- TODO: type inference should lift boolean variables and constants!

-- | Statically typed
data VarType v => LogicExpr v
  = LogicTerm (BoolExpr v)
  | Not (LogicExpr v)
  | BinLogicExpr BoolOp (LogicExpr v) (LogicExpr v)
  | Always (LogicExpr v)
  | Next (LogicExpr v)
  | ExprAutomaton (GBuchi Integer (LogicExpr v) Bool)

-- | A typed expression type.
--   /v/ is the type of variables description (for example `String' or `(String, String)'
--  for unqualified or qualified names).
-- We split the expression typing in 'static' and 'dynamic' typing.
-- This is because we have expressions which types are fixed (e.g. bool)
-- and terms which get a type that is determined by the user in the formula.
-- And then there are things which have dynamically typed 'parameters' and
-- a fixed 'return' type (e.g. relations).
data VarType v => Expr v
  = Term (Term v)
  | BoolExpr (BoolExpr v)
  | LogicExpr (LogicExpr v)

exprType :: VarType v => Expr v -> GTLType
exprType (Term (VarExpr v)) = varType v
exprType (Term (ConstExpr c)) = constType c
exprType (Term (BinExpr t _ _ _)) = t
exprType (BoolExpr _) = GTLBool
exprType (LogicExpr _) = GTLBool

instance Ord TypeRep where
    compare t1 t2 =
        compare
            (unsafePerformIO $ typeRepKey t1)
            (unsafePerformIO $ typeRepKey t2)

class (Show v, Ord v, Eq v) => VarType v where
instance VarType String where
instance VarType (String, String) where
instance VarType (Maybe String, String)

class (Show a, Eq a, Ord a, Typeable a, Binary a) => BaseType a where
instance BaseType Bool where
instance BaseType Int where
instance BaseType (Array Integer Integer) where

-- | Constructs a value of type b by appliying the constructor
-- to the value castet from type a into its correct type.
construct :: BaseType a => a -> (Map GTLType (Dynamic -> b)) -> Maybe b
construct x constructors =
  let c' = Map.lookup (gtlTypeOf x) constructors
  in case c' of
    Nothing -> Nothing
    Just c -> Just (c (toDyn x))

unsafeFromDyn :: Typeable a => Dynamic -> a
unsafeFromDyn x = case fromDynamic x of
  Nothing -> error $ "Can't convert dynamic"++show x++" to "++show (typeOf c)
  Just p -> p
  _ -> c
  where
    c = undefined

gtlTypeOf :: Typeable a => a -> GTLType
gtlTypeOf x
  | typeOf x == (typeOf (undefined::Int)) = GTLInt
  | typeOf x == (typeOf (undefined::Bool)) = GTLBool
  | typeOf x == (typeOf (undefined::Float)) = GTLFloat

getLogicExpr :: VarType v => Expr v -> Either String (LogicExpr v)
getLogicExpr (LogicExpr e) = Right e
getLogicExpr (BoolExpr e) = Right $ LogicTerm e
getLogicExpr _ = Left ""

makeUnaryLogicExpr :: VarType v => (LogicExpr v -> LogicExpr v) -> String -> Expr v -> Either String (LogicExpr v)
makeUnaryLogicExpr constructor _ (LogicExpr e) = Right $ constructor e
makeUnaryLogicExpr constructor _ (BoolExpr e) = Right $ constructor $ LogicTerm e
makeUnaryLogicExpr _ opName _ = Left $ "Expected boolean expression or logical term as argument for operator " ++ opName ++ "."

-- | Typecheck an untyped expression. Converts it into the `Expr' type which is strongly typed.
--   Returns either an error message or the resulting expression of type /t/.
typeCheckLogicExpr :: (VarType v)
             => Map v GTLType -- ^ Type mapping
             -> (Maybe String -> String -> Either String v) -- ^ Function to convert variable names
             -> ExistsBinding v
             -> GExpr -- ^ The expression to convert
             -> Either String (LogicExpr v) -- ^ Typed expression
typeCheckLogicExpr tp f bind expr = do
    expr <- inferType tp f bind expr
    case expr of
      LogicExpr (e) -> return e
      _ -> Left $ "Error"

-- | Traverses the untyped expression tree and converts it into a typed one
-- while calculating the types bottom up.
inferType :: VarType a
             => Map a GTLType -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> GExpr -- ^ The expression to convert
             -> Either String (Expr a) -- ^ Typed expression
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
    Just t -> return $ Term $ VarExpr $ Variable rv lvl t
inferType _ _ _ (GConst c) = Right $ Term $ ConstExpr $ Constant (IntVal c) GTLInt
inferType _ _ _ (GConstBool c) =  Right $ Term $ ConstExpr $ Constant (BoolVal c) GTLBool
inferType _ _ _ (GSet c) = Left $ "Type error for set constant " ++ show c ++ ": unknown type." -- Right (TypeErasedExpr (ConstExpr c))
inferType tp f bind (GBin op l r) = inferTypeBinary tp f bind op l r
inferType tp f bind (GUn op expr) = inferTypeUnary tp f bind op expr
inferType tp f bind (GExists v q n expr) = do
  r <- f q n
  inferType tp f (Map.insert v (r,0) bind) expr
inferType tp f bind (GAutomaton states) = fmap LogicExpr (inferTypeAutomaton tp f bind states)

-- | Infers the type for binary expressions. The type of the two arguments
-- must be equal as all binary operations and relations require that
-- for now.
inferTypeBinary :: VarType a
             => Map a GTLType -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> BinOp -- ^ The operator to type check
             -> GExpr -- ^ The left hand side of the operator
             -> GExpr -- ^ The right hand side of the operator
             -> Either String (Expr a)
inferTypeBinary tp f bind op lhs rhs = do
  le <- inferType tp f bind lhs
  re <- inferType tp f bind rhs
  let typeLeft = exprType le
  let typeRight = exprType re
  if not (typeLeft == typeRight) then
      Left $ "Type " ++ show typeLeft ++ " of lhs not equal to type " ++ show typeRight ++ " of rhs"
    else case toBoolOp op of
      Nothing -> case toRelOp op of
        Nothing -> case toIntOp op of
          Nothing -> Left $ "Unknown operator type: " ++ show op ++ "."
          Just intOp -> case le of
            Term tl -> case re of
              Term tr -> Right $ Term $ BinExpr typeLeft (IntOp intOp) tl tr
              _ -> Left $ "Expected variable, constant or term expression on rhs of operator " ++ show intOp ++ "."
            _ -> Left $ "Expected variable, constant or term expression on lhs of operator " ++ show intOp ++ "."
        Just relOp -> case le of
          Term tl -> case re of
            Term tr -> Right $ BoolExpr $ RelExpr relOp tl tr
            _ -> Left $ "Expected variable, constant or term expression on rhs of relation " ++ show relOp ++ "."
          _ -> Left $ "Expected variable, constant or term expression on lhs of relation " ++ show relOp ++ "."
      Just boolOp -> do
        tl <- case le of
          BoolExpr t -> Right $ LogicTerm t
          LogicExpr t -> Right t
          _ -> Left $ "Expected boolean term or logical expression on lhs of logical operator " ++ show boolOp ++ "."
        tr <- case re of
          BoolExpr t -> Right $ LogicTerm t
          LogicExpr t -> Right t
          _ -> Left $ "Expected boolean term or logical expression on rhs of logical operator " ++ show boolOp ++ "."
        return $ LogicExpr $ BinLogicExpr boolOp tl tr

inferTypeUnary :: VarType a
             => Map a GTLType -- ^ Type mapping
             -> (Maybe String -> String -> Either String a) -- ^ Function to convert variable names
             -> ExistsBinding a
             -> UnOp -- ^ The operator to type check
             -> GExpr -- ^ The left hand side of the operator
             -> Either String (Expr a)
inferTypeUnary tp f bind op expr =
  case op of
    GOpAlways -> do
      rexpr <- inferType tp f bind expr
      fmap LogicExpr $ makeUnaryLogicExpr Always "always" rexpr
    GOpNext -> do
      rexpr <- inferType tp f (fmap (\(v,lvl) -> (v,lvl+1)) bind) expr
      fmap LogicExpr $ makeUnaryLogicExpr Next "next" rexpr
    GOpNot -> do
      rexpr <- inferType tp f bind expr
      fmap LogicExpr $ makeUnaryLogicExpr Not "not" rexpr
    GOpFinally Nothing -> Left "Unbounded finally not allowed"
    GOpFinally (Just n) -> do
      res <- Prelude.mapM (\i -> inferType tp f (fmap (\(v,lvl) -> (v,lvl+i)) bind) expr) [0..n]
      let t = exprType (head res)
      if t == GTLBool then do
          first <- makeUnaryLogicExpr Next "next" (head res)
          folded <- foldM (\x y -> do { eNext <- (makeUnaryLogicExpr Next "next" y); return $ BinLogicExpr Or x eNext }) first (tail res)
          return $ LogicExpr folded
        else
          Left $ "Expected type Bool for operator finally but got type " ++ show t ++ "."

inferTypeAutomaton :: (VarType a)
                      => Map a GTLType
                      -> (Maybe String -> String -> Either String a)
                      -> ExistsBinding a
                      -> [State]
                      -> Either String (LogicExpr a) -- (GBuchi Integer (Expr a Bool) Bool)
inferTypeAutomaton tp f bind states = do
  (buchi,_,_) <- foldlM (\(cbuchi,ccur,cmp) state -> do
                            (res,nbuchi,ncur,nmp) <- typeCheckState tp f bind states state Nothing ccur cmp cbuchi
                            return (nbuchi,ncur,nmp)
                        ) (Map.empty,0,Map.empty) [ state | state <- states, stateInitial state ]
  return $ ExprAutomaton buchi

typeCheckState :: (VarType a)
                  => Map a GTLType
                  -> (Maybe String -> String -> Either String a)
                  -> ExistsBinding a
                  -> [State]
                  -> State
                  -> Maybe GExpr
                  -> Integer
                  -> Map (String,Maybe GExpr) Integer
                  -> GBuchi Integer (LogicExpr a) Bool
                  -> Either String (Integer,GBuchi Integer (LogicExpr a) Bool,Integer,Map (String,Maybe GExpr) Integer)
typeCheckState tp f bind all st cond cur mp buchi = case Map.lookup (stateName st,cond) mp of
  Just res -> return (res,buchi,cur,mp)
  Nothing -> do
    rcont <- mapM (\cont -> case cont of
                      Left expr -> do
                        l <- inferType tp f bind expr
                        return $ Left l
                      Right nxt -> return $ Right nxt) (stateContent st)
    rcond <- case cond of
      Nothing -> return Nothing
      Just c -> do
        r <- inferType tp f bind c
        return $ Just r
    let (exprs,nexts) = partitionEithers rcont
    let rexprs = case rcond of
          Nothing -> exprs
          Just jcond -> jcond:exprs
    (nbuchi,ncur,nmp,succ) <- foldrM (\(nxt,nxt_cond) (cbuchi,ccur,cmp,succ) -> case List.find (\cst -> (stateName cst) == nxt) all of
                                         Nothing -> Left ("Undefined state: "++nxt)
                                         Just rst -> do
                                           (res,nbuchi,ncur,nmp) <- typeCheckState tp f bind all rst nxt_cond ccur cmp cbuchi
                                           return (nbuchi,ncur,nmp,Set.insert res succ)
                                     ) (buchi,cur+1,Map.insert (stateName st,cond) cur mp,Set.empty) nexts
    varExpr <- makeVars rexprs
    return (cur,Map.insert cur (BuchiState { isStart = (stateInitial st) && isNothing cond
                                           , vars = varExpr
                                           , finalSets = stateFinal st
                                           , successors = succ
                                           }) nbuchi,ncur,nmp)
  where
    makeVars :: VarType a => [Expr a] -> Either String (LogicExpr a)
    makeVars [] = Right $ LogicTerm $ BoolConst True
    makeVars rexprs =
      let first = head rexprs
      in case first of
        LogicExpr first' -> do
          foldM (\x y -> do { y' <- getLogicExpr y; return $ BinLogicExpr And x y' }) first' (tail rexprs)
        _ -> Left $ "Expected type Bool for operator finally but got type " ++ (show $ exprType first) ++ "."

{-
      let t = exprType (head res)
      if t == GTLBool then do
          first <- makeUnaryLogicExpr Next "next" (head res)
          folded <- foldM (\x y -> do { eNext <- (makeUnaryLogicExpr Next "next" y); return $ BinLogicExpr Or x eNext }) first (tail res)
          return $ LogicExpr folded
        else
          Left $ "Expected type Bool for operator finally but got type " ++ show t ++ "."
-}

instance VarType v => Eq (Term v) where
  (VarExpr v1) == (VarExpr v2) = v1 == v2
  (ConstExpr c1) == (ConstExpr c2) = c1 == c2
  (BinExpr t1 op1 l1 r1) == (BinExpr t2 op2 l2 r2) = t1 == t2 && op1==op2 && l1==l2 && r1==r2

instance VarType v => Eq (BoolExpr v) where
  (RelExpr rel1 lhs1 rhs1) == (RelExpr rel2 lhs2 rhs2) = rel1 == rel2 && lhs1 == lhs2 && rhs1 == rhs1
  (ElemExpr n1 s1 p1) == (ElemExpr n2 s2 p2) = n1 == n2 && s1 == s2 && p1 == p2

instance VarType v => Eq (LogicExpr v) where
  (Not e1) == (Not e2) = e1 == e2
  (Always e1) == (Always e2) = e1 == e2
  (Next e1) == (Next e2) = e1 == e2

instance VarType v => Ord (Term v) where
  compare (VarExpr v1) (VarExpr v2) = compare v1 v2
  compare (ConstExpr c1) (ConstExpr c2) = compare c1 c2
  compare (BinExpr t1 op1 l1 r1) (BinExpr t2 op2 l2 r2) = case compare t1 t2 of
    EQ -> case compare op1 op2 of
      EQ -> case compare l1 l2 of
        EQ -> compare r1 r2
        r -> r
      r -> r
    r -> r

instance VarType v => Ord (BoolExpr v) where
  compare (RelExpr rel1 lhs1 rhs1) (RelExpr rel2 lhs2 rhs2) = case compare rel1 rel2 of
    EQ -> case compare lhs1 lhs2 of
      EQ -> compare rhs1 rhs1
    r -> r
  compare (RelExpr _ _ _) _ = LT
  compare (ElemExpr v1 s1 p1) (ElemExpr v2 s2 p2) = case compare v1 v2 of
    EQ -> case compare s1 s2 of
      EQ -> compare p1 p2
      r -> r
    r -> r
  compare (ElemExpr _ _ _) _ = LT

instance VarType v => Ord (LogicExpr v) where
  compare (Not e1) (Not e2) = compare e1 e2
  compare (Not _) _ = LT
  compare (Always e1) (Always e2) = compare e1 e2
  compare (Always _) _ = LT
  compare (Next e1) (Next e2) = compare e1 e2
  compare (Next _) _ = LT

instance Show GTLOp where
  show (IntOp op) = case op of
                     OpPlus -> "+"
                     OpMinus -> "-"
                     OpMult -> "*"
                     OpDiv -> "/"

instance VarType v => Show (Variable v) where
  show v = let suff = case time v of
                        0 -> ""
                        _ -> "#" ++ (show $ time v)
            in (show $ name v) ++ suff

instance VarType v => Show (Term v) where
  show (VarExpr v) = show v
  show (ConstExpr i) = show i
  show (BinExpr _ op lhs rhs) = "(" ++ show lhs ++ ")"
                                 ++ show op
                                 ++ "(" ++ show rhs ++ ")"

instance VarType v => Show (BoolExpr v) where
  show (RelExpr rel lhs rhs) = "(" ++ show lhs ++ ") " ++
                               show rel ++
                               " (" ++ show rhs ++ ")"
  show (ElemExpr v ints pos) = show v ++
                               (if pos then " in "
                                else " not in ") ++
                               show ints
  show (BoolConst c) = show c
  show (BoolVar v) = show v

instance VarType v => Show (LogicExpr v) where
  show (LogicTerm t) = show t
  show (BinLogicExpr op lhs rhs) = "(" ++ show lhs ++ ") " ++
                                  (case op of
                                      And -> "and"
                                      Or -> "or"
                                      Implies -> "implies"
                                      Until -> "until") ++
                                  " ("++show rhs++")"
  show (Not e) = "not (" ++ show e ++ ")"
  show (Always e) = "always (" ++ show e ++ ")"
  show (Next e) = "next (" ++ show e ++ ")"
  show (ExprAutomaton a) = "Automaton"

instance VarType v => Show (Expr v) where
  show (Term e) = show e
  show (BoolExpr e) = show e
  show (LogicExpr e) = show e

instance (VarType v, Binary v) => Binary (Variable v) where
  put v = put (varType v) >> put (name v) >> put (time v)
  get = do
    varType <- get
    name <- get
    time <- get
    return $ Variable name time varType

putBinaryGTLTypeVal :: GTLTypeVal -> Put
putBinaryGTLTypeVal (IntVal c) = put c
putBinaryGTLTypeVal (BoolVal c) = put c

getBinaryGTLTypeVal :: GTLType -> Get GTLTypeVal
getBinaryGTLTypeVal GTLInt = fmap IntVal $ (get :: Get Int)
getBinaryGTLTypeVal GTLBool = fmap BoolVal $ (get :: Get Bool)

instance Binary Constant where
  put c = put (constType c) >> putBinaryGTLTypeVal (value c)
  get = do
    t <- get :: Get GTLType
    c <- getBinaryGTLTypeVal t
    return $ Constant c t

instance Binary GTLOp where
  put (IntOp o) = put o
  get = fmap IntOp $ get

instance (VarType v, Binary v) => Binary (Term v) where
  put (VarExpr v) = putWord8 0 >> put v
  put (ConstExpr c) = putWord8 1 >> put c
  put (BinExpr t op lhs rhs) = putWord8 2 >> put t >> put op >> put lhs >> put rhs
  get = do
    which <- getWord8
    case which of
      0 -> fmap VarExpr $ (get :: Get (Variable v))
      1 -> fmap ConstExpr $ (get :: Get Constant)
      2 -> do
        t <- get
        op <- get
        lhs <- get
        rhs <- get
        return $ BinExpr t op lhs rhs

instance (VarType v, Binary v) => Binary (BoolExpr v) where
  put (RelExpr rel lhs rhs) = putWord8 3 >> put rel >> put lhs >> put rhs
  put (ElemExpr n vals b) = putWord8 4 >> put n >> put vals >> put b
  put (BoolConst c) = putWord8 5 >> put c
  put (BoolVar v) = putWord8 6 >> put v
  get = do
    which <- getWord8
    case which of
      3 -> do
        rel <- get
        lhs <- get
        rhs <- get
        return $ RelExpr rel lhs rhs
      4 -> do
        var <- get
        cs <- get
        isIn <- get
        return $ ElemExpr var cs isIn
      5 -> fmap BoolConst get
      6 -> do
        v <- get :: Get (Variable v)
        -- assert (varType v) == GTLBool
        return $ BoolVar v


instance (VarType v, Binary v) => Binary (LogicExpr v) where
  put (Not e) = putWord8 7 >> put e
  put (Always e) = putWord8 8 >> put e
  put (Next e) = putWord8 9 >> put e
  put (LogicTerm t) = putWord8 10 >> put t
  put (ExprAutomaton _ ) = undefined
  get = do
    i <- getWord8
    case i of
      7 -> do
        e <- get
        return $ Not e
      8 -> do
        e <- get
        return $ Always e
      9 -> do
        e <- get
        return $ Next e
      10 -> do
        t <- get
        return $ LogicTerm t

-- | Pushes a negation as far into the formula as possible by applying simplification rules.
pushNot :: VarType v => LogicExpr v -> LogicExpr v
pushNot (Not x) = negateExpr x
  where
    negateTerm :: VarType v => BoolExpr v -> BoolExpr v
    negateTerm (RelExpr rel x y) = RelExpr (relNot rel) x y
    negateTerm (ElemExpr n lst neg) = ElemExpr n lst (not neg)
    -- negateTerm t = error $ "Can not negate " ++ show t

    negateExpr :: VarType v => LogicExpr v -> LogicExpr v
    negateExpr (LogicTerm t) = LogicTerm $ negateTerm t
    negateExpr (Not x) = x
    negateExpr (BinLogicExpr op x y) = case op of
      And -> BinLogicExpr Or (negateExpr x) (negateExpr y)
      Or -> BinLogicExpr And (negateExpr x) (negateExpr y)
      Implies -> BinLogicExpr And (pushNot x) (negateExpr y)
    negateExpr (Always x) = error "always operator must not be negated"
    negateExpr (Next x) = Next (negateExpr x)

pushNot (BinLogicExpr op x y) = BinLogicExpr op (pushNot x) (pushNot y)
pushNot (Always x) = Always (pushNot x)
pushNot (Next x) = Next (pushNot x)
pushNot expr = expr



-- | Extracts all variables with their level of history from an expression.
getVarsTerm (VarExpr v) = [(name v, time v)]
getVarsTerm (ConstExpr _) = []
getVarsTerm (BinExpr _ _ lhs rhs) = getVarsTerm lhs ++ getVarsTerm rhs

getVarsBoolExpr (RelExpr _ lhs rhs) = getVarsTerm lhs ++ getVarsTerm rhs
getVarsBoolExpr (ElemExpr v _ _) = [(name v, 0)]
getVarsBoolExpr (BoolConst _) = []
getVarsBoolExpr (BoolVar v) = [(name v, time v)]

getVars :: VarType v => Expr v -> [(v,Integer)]
getVars (Term t) = getVarsTerm t
getVars (BoolExpr e) = getVarsBoolExpr e
getVars (LogicExpr e) = getVarsLogic e
  where
    getVarsLogic (Not e) = getVarsLogic e
    getVarsLogic (Always e) = getVarsLogic e
    getVarsLogic (Next e) = getVarsLogic e
    getVarsLogic (ExprAutomaton aut) = concat $ fmap (\(_,st) -> getVarsLogic (vars st)) (Map.toList aut)

-- | Extracts the maximum level of history for each variable in the expression.
maximumHistory :: VarType v => Expr v -> Map v Integer
maximumHistory exprs = foldl (\mp (n,lvl) -> Map.insertWith max n lvl mp) Map.empty (getVars exprs)

-- | Change the type of the variables in an expression.
mapVarsTerm :: (VarType v, VarType w) => (v -> w) -> Term v -> Term w
mapVarsTerm f (VarExpr v) = VarExpr $ v {name = f (name v)}
mapVarsTerm _ (ConstExpr c) = ConstExpr c
mapVarsTerm f (BinExpr t op lhs rhs) = BinExpr t op (mapVarsTerm f lhs) (mapVarsTerm f rhs)

mapVarsBoolExpr :: (VarType v, VarType w) => (v -> w) -> BoolExpr v -> BoolExpr w
mapVarsBoolExpr f (RelExpr rel lhs rhs) = RelExpr rel (mapVarsTerm f lhs) (mapVarsTerm f rhs)
mapVarsBoolExpr f (ElemExpr v vals b) = ElemExpr (v {name = f (name v)}) vals b
mapVarsBoolExpr f (BoolConst c) = BoolConst c
mapVarsBoolExpr f (BoolVar v) = BoolVar $ v {name = f (name v)}

mapVars :: (VarType v, VarType w) => (v -> w) -> Expr v -> Expr w
mapVars f (Term t) = Term $ mapVarsTerm f t
mapVars f (BoolExpr e) = BoolExpr $ mapVarsBoolExpr f e
mapVars f (LogicExpr e) = LogicExpr $ mapVarsLogic f e
  where
    mapVarsLogic f (Not e) = Not (mapVarsLogic f e)
    mapVarsLogic f (Always e) = Always (mapVarsLogic f e)
    mapVarsLogic f (Next e) = Next (mapVarsLogic f e)

-- | Binary boolean operators with the traditional semantics.
data BoolOp = And     -- ^ &#8896;
            | Or      -- ^ &#8897;
            | Implies -- ^ &#8658;
            | Until
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

-- | Lift `gcast' in a monad and fail with an error if the cast fails
castSer :: (Typeable a,Typeable b,Monad m) => c a -> m (c b)
castSer = maybe (error "Internal serialization error") return . gcast


-- | Cast a binary operator into a boolean operator. Returns `Nothing' if the cast fails.
toBoolOp :: BinOp -> Maybe BoolOp
toBoolOp GOpAnd = Just And
toBoolOp GOpOr = Just Or
toBoolOp GOpImplies = Just Implies
toBoolOp GOpUntil = Just Until
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

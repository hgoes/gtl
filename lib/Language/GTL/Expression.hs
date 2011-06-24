{-# LANGUAGE ScopedTypeVariables,GADTs,DeriveDataTypeable,FlexibleInstances,
  ExistentialQuantification, StandaloneDeriving, TypeSynonymInstances, FlexibleContexts,
  DeriveFunctor #-}
{-| Provides the expression data type as well as the type-checking algorithm.
 -}
module Language.GTL.Expression where

import Language.GTL.Parser.Syntax
import Language.GTL.Parser.Token
import Language.GTL.Buchi
import Language.GTL.Types

import Data.Binary
import Data.Maybe
import Data.Map as Map
import Data.Set as Set
import Data.List as List (genericLength,genericIndex)
import Data.Either
import Data.Foldable
import Data.Traversable
import Prelude hiding (foldl,foldl1,concat,elem,mapM_,mapM)
import Control.Monad.Error ()

data Fix f = Fix { unfix :: f (Fix f) }

data Term v r = Var v Integer
              | Value (GTLValue r)
              | BinBoolExpr BoolOp r r
              | BinRelExpr Relation r r
              | BinIntExpr IntOp r r
              | UnBoolExpr UnBoolOp r
              | IndexExpr r Integer
              | Automaton (GBuchi Integer r Bool)
              deriving (Eq,Ord)

type GTLConstant = Fix GTLValue

type Expr v = Term v (Fix (Term v))

data Typed a r = Typed { getType :: GTLType
                       , getValue :: a r
                       } deriving (Eq,Ord)

type TypedExpr v = Typed (Term v) (Fix (Typed (Term v)))

instance Show (Fix GTLValue) where
  showsPrec p x = showGTLValue show p (unfix x)

instance Functor (Term v) where
  fmap f (Var x lvl) = Var x lvl
  fmap f (Value val) = Value (fmap f val)
  fmap f (BinBoolExpr op l r) = BinBoolExpr op (f l) (f r)
  fmap f (BinRelExpr op l r) = BinRelExpr op (f l) (f r)
  fmap f (BinIntExpr op l r) = BinIntExpr op (f l) (f r)
  fmap f (UnBoolExpr op p) = UnBoolExpr op (f p)
  fmap f (IndexExpr x i) = IndexExpr (f x) i

instance Functor a => Functor (Typed a) where
  fmap f t = Typed { getType = getType t
                   , getValue = fmap f (getValue t)
                   }

instance (Binary r,Binary v) => Binary (Term v r) where
  put (Var v l) = put (0::Word8) >> put v >> put l
  put (Value val) = put (1::Word8) >> put val
  put (BinBoolExpr op l r) = put (2::Word8) >> put op >> put l >> put r
  put (BinRelExpr op l r) = put (3::Word8) >> put op >> put l >> put r
  put (BinIntExpr op l r) = put (4::Word8) >> put op >> put l >> put r
  put (UnBoolExpr op p) = put (5::Word8) >> put op >> put p
  put (IndexExpr e i) = put (6::Word8) >> put i >> put e
  put (Automaton aut) = put (7::Word8) >> put aut
  get = do
    (i::Word8) <- get
    case i of
      0 -> do
        v <- get
        l <- get
        return $ Var v l
      1 -> fmap Value get
      2 -> do
        op <- get
        l <- get
        r <- get
        return $ BinBoolExpr op l r
      3 -> do
        op <- get
        l <- get
        r <- get
        return $ BinRelExpr op l r
      4 -> do
        op <- get
        l <- get
        r <- get
        return $ BinIntExpr op l r
      5 -> do
        op <- get
        p <- get
        return $ UnBoolExpr op p
      6 -> do
        i <- get
        e <- get
        return $ IndexExpr e i
      7 -> do
        aut <- get
        return $ Automaton aut

var :: v -> Integer -> TypedExpr v
var name lvl = Typed GTLBool (Var name lvl)

constant :: ToGTL a => a -> TypedExpr v
constant x = Typed (gtlTypeOf x) (Value (toGTL x))

gnot :: TypedExpr v -> TypedExpr v
gnot expr
  | getType expr == GTLBool = Typed GTLBool (UnBoolExpr Not (Fix expr))

gtlAnd :: TypedExpr v -> TypedExpr v -> TypedExpr v
gtlAnd x y
  | getType x == GTLBool && getType y == GTLBool = Typed GTLBool (BinBoolExpr And (Fix x) (Fix y))

instance Binary (a r) => Binary (Typed a r) where
  put x = put (getType x) >> put (getValue x)
  get = do
    tp <- get
    val <- get
    return (Typed tp val)

instance Binary v => Binary (Fix (Typed (Term v))) where
  put = put . unfix
  get = fmap Fix get

instance (Show v,Show r) => Show (Term v r) where
  show = showTerm show

instance Show v => Show (Fix (Term v)) where
  show = showTerm show . unfix

instance Show (a r) => Show (Typed a r) where
  show x = show (getValue x)

instance Show v => Show (Fix (Typed (Term v))) where
  show = showTerm show . getValue . unfix

instance Eq v => Eq (Fix (Typed (Term v))) where
  e1 == e2 = (getValue $ unfix e1) == (getValue $ unfix e2)

instance Ord v => Ord (Fix (Typed (Term v))) where
  compare e1 e2 = compare (getValue $ unfix e1) (getValue $ unfix e2)

instance Eq (Fix GTLValue) where
  e1 == e2 = (unfix e1) == (unfix e2)

instance Ord (Fix GTLValue) where
  compare e1 e2 = compare (unfix e1) (unfix e2)

showTerm :: Show v => (r -> String) -> Term v r -> String
showTerm f (Var name lvl) = show name ++ (if lvl==0
                                          then ""
                                          else "_"++show lvl)
showTerm f (Value val) = showGTLValue f 0 val ""
showTerm f (BinBoolExpr op l r) = "(" ++ (f l) ++ (case op of
                                                      And -> " and "
                                                      Or -> " or "
                                                      Implies -> " implies "
                                                      Until -> " until "
                                                  ) ++ (f r) ++ ")"
showTerm f (BinRelExpr rel l r) = "(" ++ (f l) ++ (case rel of
                                                      BinLT -> " < "
                                                      BinLTEq -> " <= "
                                                      BinGT -> " > "
                                                      BinGTEq -> " >= "
                                                      BinEq -> " = "
                                                      BinNEq -> " != ") ++ (f r) ++ ")"
showTerm f (BinIntExpr op l r) = "(" ++ (f l) ++ (case op of
                                                     OpPlus -> " + "
                                                     OpMinus -> " - "
                                                     OpMult -> " * "
                                                     OpDiv -> " / ") ++ (f r) ++ ")"
showTerm f (UnBoolExpr op p) = "(" ++ (case op of
                                          Not -> "not "
                                          Always -> "always "
                                          Next -> "next ") ++ (f p) ++ ")"
showTerm f (IndexExpr expr idx) = f expr ++ "["++show idx++"]"

enforceType :: String -> GTLType -> GTLType -> Either String ()
enforceType expr ac tp = if ac == tp
                         then Right ()
                         else Left $ expr ++ " should have type "++show tp++" but it has type "++show ac

makeTypedExpr :: (Ord v,Show v) => (Maybe String -> String -> Either String v) -> Map v GTLType -> Set [String] -> GExpr -> Either String (TypedExpr v)
makeTypedExpr f varmp enums expr = parseTerm f Map.empty expr >>= typeCheck varmp enums

getConstant :: TypedExpr v -> Maybe GTLConstant
getConstant e = case getValue e of
  Value p -> do
    np <- mapM (getConstant.unfix) p
    return $ Fix np
  _ -> Nothing

typeCheck :: (Ord v,Show v) => Map v GTLType -> Set [String] -> Expr v -> Either String (TypedExpr v)
typeCheck varmp enums = typeCheck' (\expr -> typeCheck varmp enums (unfix expr) >>= return.Fix) (getType . unfix) (show . untyped . unfix) varmp enums

typeCheck' :: (Ord v,Show v)
              => (r1 -> Either String r2)
              -> (r2 -> GTLType)
              -> (r2 -> String)
              -> Map v GTLType -> Set [String] -> Term v r1 -> Either String (Typed (Term v) r2)
typeCheck' mu mutp mus varmp enums (Var x lvl) = case Map.lookup x varmp of
  Nothing -> Left $ "Unknown variable "++show x
  Just tp -> return $ Typed tp (Var x lvl)
typeCheck' mu mutp mus varmp enums (Value val) = case val of
  GTLIntVal i -> return $ Typed GTLInt (Value $ GTLIntVal i)
  GTLByteVal i -> return $ Typed GTLByte (Value $ GTLByteVal i)
  GTLBoolVal i -> return $ Typed GTLBool (Value $ GTLBoolVal i)
  GTLFloatVal i -> return $ Typed GTLFloat (Value $ GTLFloatVal i)
  GTLEnumVal x -> case find (elem x) enums of
    Nothing -> Left $ "Unknown enum value "++show x
    Just e -> return $ Typed (GTLEnum e) (Value $ GTLEnumVal x)
  GTLArrayVal vals -> do
    res <- mapM mu vals
    case res of
      [] -> Left "Empty arrays not allowed"
      (x:xs) -> mapM_ (\tp -> if (mutp tp)==(mutp x)
                              then return ()
                              else Left "Not all array elements have the same type") xs
    return $ Typed (GTLArray (genericLength res) (mutp (head res))) (Value $ GTLArrayVal res)
  GTLTupleVal vals -> do
    tps <- mapM mu vals
    return $ Typed (GTLTuple (fmap mutp tps)) (Value $ GTLTupleVal tps)
typeCheck' mu mutp mus varmp enums (BinBoolExpr op l r) = do
  ll <- mu l
  rr <- mu r
  enforceType (mus ll) (mutp ll) GTLBool
  enforceType (mus rr) (mutp rr) GTLBool
  return $ Typed GTLBool (BinBoolExpr op ll rr)
typeCheck' mu mutp mus varmp enums (BinRelExpr rel l r) = do
  ll <- mu l
  rr <- mu r
  if rel==BinEq || rel==BinNEq
    then (do
             enforceType (mus rr) (mutp rr) (mutp ll))
    else (do
             enforceType (mus ll) (mutp ll) GTLInt
             enforceType (mus rr) (mutp rr) GTLInt)
  return $ Typed GTLBool (BinRelExpr rel ll rr)
typeCheck' mu mutp mus varmp enums (BinIntExpr op l r) = do
  ll <- mu l
  rr <- mu r
  enforceType (mus ll) (mutp ll) GTLInt
  enforceType (mus rr) (mutp rr) GTLInt
  return $ Typed GTLInt (BinIntExpr op ll rr)
typeCheck' mu mutp mus varmp enums (UnBoolExpr op p) = do
  pp <- mu p
  enforceType (mus pp) (mutp pp) GTLBool
  return $ Typed GTLBool (UnBoolExpr op pp)
typeCheck' mu mutp mus varmp enums (IndexExpr p idx) = do
  pp <- mu p
  case mutp pp of
    GTLArray sz tp -> if idx < sz
                      then return $ Typed tp (IndexExpr pp idx)
                      else Left $ "Index "++show idx++" out of bounds "++show sz
    GTLTuple tps -> if idx < genericLength tps
                    then return $ Typed (tps `genericIndex` idx) (IndexExpr pp idx)
                    else Left $ "Index "++show idx++" out of bounds "++show (genericLength tps)
    _ -> Left $ "Expression " ++ mus pp ++ " is not indexable"
typeCheck' mu mutp mus varmp enums (Automaton buchi) = do
  nbuchi <- mapM (\st -> do
                     nvars <- mu (vars st)
                     return $ st { vars = nvars }) buchi
  return $ Typed GTLBool (Automaton nbuchi)

untyped :: TypedExpr v -> Expr v
untyped expr = fmap (Fix . untyped . unfix) (getValue expr)

parseTerm :: (Maybe String -> String -> Either String v) -> ExistsBinding v -> GExpr -> Either String (Expr v)
parseTerm f ex = parseTerm' (\ex' expr -> parseTerm f ex' expr >>= return.Fix) f ex

parseTerm' :: (ExistsBinding v -> GExpr -> Either String r)
              -> (Maybe String -> String -> Either String v) -> ExistsBinding v -> GExpr -> Either String (Term v r)
parseTerm' mu f ex (GBin op l r) = do
  rec_l <- mu ex l
  rec_r <- mu ex r
  case toBoolOp op of
    Just rop -> return $ BinBoolExpr rop rec_l rec_r
    Nothing -> case toRelOp op of
      Just rop -> return $ BinRelExpr rop rec_l rec_r
      Nothing -> case toIntOp op of
        Just rop -> return $ BinIntExpr rop rec_l rec_r
        Nothing -> Left $ "Internal error, please implement parseTerm for operator "++show op
parseTerm' mu f ex (GUn op p) = do
  rec <- mu (case op of
                GOpNext -> fmap (\(v,lvl) -> (v,lvl+1)) ex
                _ -> ex
            ) p
  return $ UnBoolExpr (case op of
                          GOpAlways -> Always
                          GOpNext -> Next
                          GOpNot -> Not
                          GOpFinally t -> Finally t
                      ) rec
parseTerm' mu f ex (GConst x) = return $ Value (GTLIntVal $ fromIntegral x)
parseTerm' mu f ex (GConstBool x) = return $ Value (GTLBoolVal x)
parseTerm' mu f ex (GEnum x) = return $ Value (GTLEnumVal x)
parseTerm' mu f ex (GTuple args) = do
  res <- mapM (mu ex) args
  return $ Value (GTLTupleVal res)
parseTerm' mu f ex (GArray args) = do
  res <- mapM (mu ex) args
  return $ Value (GTLArrayVal res)
parseTerm' mu f ex (GVar q n) = case q of
  Nothing -> case Map.lookup n ex of
    Nothing -> do
      var <- f q n
      return $ Var var 0
    Just (r,lvl) -> return $ Var r lvl
  Just _ -> do
    var <- f q n
    return $ Var var 0
parseTerm' mu f ex (GExists b q n expr) = case q of
  Nothing -> case Map.lookup n ex of
    Nothing -> do
      var <- f q n
      parseTerm' mu f (Map.insert b (var,0) ex) expr
    Just (v,lvl) -> parseTerm' mu f (Map.insert b (v,lvl) ex) expr
  Just _ -> do
    var <- f q n
    parseTerm' mu f (Map.insert b (var,0) ex) expr
parseTerm' mu f ex (GAutomaton sts) = do
  (buchi,_,_) <- foldlM (\(cbuchi,ccur,cmp) state -> do
                            (res,nbuchi,ncur,nmp) <- parseState state Nothing ccur cmp cbuchi
                            return (nbuchi,ncur,nmp)
                        ) (Map.empty,0,Map.empty) [ state | state <- sts, stateInitial state ]
  return $ Automaton buchi
    where
      parseState st cond cur mp buchi = case Map.lookup (stateName st,cond) mp of
        Just res -> return (res,buchi,cur,mp)
        Nothing -> do
          let (exprs,nexts) = partitionEithers (stateContent st)
          let rexprs = case cond of
                Nothing -> exprs
                Just jcond -> jcond:exprs
          (nbuchi,ncur,nmp,succ) <- foldrM (\(nxt,nxt_cond) (cbuchi,ccur,cmp,succ) -> case find (\cst -> (stateName cst) == nxt) sts of
                                               Nothing -> Left ("Undefined state: "++nxt)
                                               Just rst -> do
                                                 (res,nbuchi,ncur,nmp) <- parseState rst nxt_cond ccur cmp cbuchi
                                                 return (nbuchi,ncur,nmp,Set.insert res succ)
                                           ) (buchi,cur+1,Map.insert (stateName st,cond) cur mp,Set.empty) nexts
          varExpr <- case rexprs of
                [] -> mu ex (GConstBool True)
                _ -> mu ex (foldl1 (GBin GOpAnd) rexprs)
          return (cur,Map.insert cur (BuchiState { isStart = (stateInitial st) && isNothing cond
                                                 , vars = varExpr
                                                 , finalSets = stateFinal st
                                                 , successors = succ
                                                 }) nbuchi,ncur,nmp)
parseTerm' mu f ex (GIndex expr ind) = do
  rind <- case ind of
    GConst x -> return x
    _ -> Left $ "Index must be an integer"
  rexpr <- mu ex expr
  return $ IndexExpr rexpr (fromIntegral rind)

distributeNot :: TypedExpr v -> TypedExpr v
distributeNot expr
  | getType expr == GTLBool = case getValue expr of
    Var x lvl -> Typed GTLBool $ UnBoolExpr Not (Fix expr)
    Value (GTLBoolVal x) -> Typed GTLBool $ Value (GTLBoolVal (not x))
    BinBoolExpr op l r -> Typed GTLBool $ case op of
      And -> BinBoolExpr Or (Fix $ distributeNot $ unfix l) (Fix $ distributeNot $ unfix r)
      Or -> BinBoolExpr And (Fix $ distributeNot $ unfix l) (Fix $ distributeNot $ unfix r)
      Implies -> BinBoolExpr And (Fix $ pushNot $ unfix l) (Fix $ distributeNot $ unfix r)
      Until -> BinBoolExpr UntilOp (Fix $ distributeNot $ unfix l) (Fix $ distributeNot $ unfix r)
    BinRelExpr rel l r -> Typed GTLBool $ BinRelExpr (relNot rel) l r
    UnBoolExpr op p -> case op of
      Not -> pushNot (unfix p)
      Next -> Typed GTLBool $ UnBoolExpr Next (Fix $ distributeNot $ unfix p)
      Always -> Typed GTLBool $ BinBoolExpr Until (Fix (Typed GTLBool (Value (GTLBoolVal True)))) (Fix $ distributeNot $ unfix p)
    IndexExpr e i -> Typed GTLBool $ UnBoolExpr Not (Fix expr)
    Automaton buchi -> Typed GTLBool $ UnBoolExpr Not (Fix expr)

pushNot :: TypedExpr v -> TypedExpr v
pushNot expr
  | getType expr == GTLBool = case getValue expr of
    BinBoolExpr op l r -> Typed GTLBool $ BinBoolExpr op (Fix $ pushNot $ unfix l) (Fix $ pushNot $ unfix r)
    UnBoolExpr Not p -> distributeNot $ unfix p
    UnBoolExpr op p -> Typed GTLBool $ UnBoolExpr op (Fix $ pushNot $ unfix p)
    IndexExpr e i -> Typed (getType expr) (IndexExpr (Fix $ pushNot $ unfix e) i)
    _ -> expr

-- | Extracts the maximum level of history for each variable in the expression.
maximumHistory :: Ord v => TypedExpr v -> Map v Integer
maximumHistory exprs = foldl (\mp (n,_,lvl,_) -> Map.insertWith max n lvl mp) Map.empty (getVars exprs)


-- | Extracts all variables with their level of history from an expression.
getVars :: TypedExpr v -> [(v,[Integer],Integer,GTLType)]
getVars x = getTermVars (getVars . unfix) x

getTermVars :: (r -> [(v,[Integer],Integer,GTLType)]) -> Typed (Term v) r -> [(v,[Integer],Integer,GTLType)]
getTermVars mu expr = case getValue expr of
  Var n lvl -> [(n,[],lvl,getType expr)]
  Value x -> getValueVars mu x
  BinBoolExpr op l r -> (mu l)++(mu r)
  BinRelExpr op l r -> (mu l)++(mu r)
  BinIntExpr op l r -> (mu l)++(mu r)
  UnBoolExpr op p -> mu p
  IndexExpr e i -> fmap (\(v,idx,lvl,tp) -> (v,i:idx,lvl,tp)) (mu e)
  Automaton buchi -> concat $ fmap (\st -> mu (vars st)) (Map.elems buchi)

getValueVars :: (r -> [(v,[Integer],Integer,GTLType)]) -> GTLValue r -> [(v,[Integer],Integer,GTLType)]
getValueVars mu (GTLArrayVal xs) = concat (fmap mu xs)
getValueVars mu (GTLTupleVal xs) = concat (fmap mu xs)
getValueVars _ _ = []

-- | Change the type of the variables in an expression.
mapGTLVars :: (v -> w) -> TypedExpr v -> TypedExpr w
mapGTLVars f expr = Typed (getType expr) (mapTermVars f (Fix . mapGTLVars f . unfix) (getValue expr))

mapTermVars :: (v -> w) -> (r1 -> r2) -> Term v r1 -> Term w r2
mapTermVars f mu (Var name lvl) = Var (f name) lvl
mapTermVars f mu (Value x) = Value (mapValueVars mu x)
mapTermVars f mu (BinBoolExpr op l r) = BinBoolExpr op (mu l) (mu r)
mapTermVars f mu (BinRelExpr rel l r) = BinRelExpr rel (mu l) (mu r)
mapTermVars f mu (BinIntExpr op l r) = BinIntExpr op (mu l) (mu r)
mapTermVars f mu (UnBoolExpr op p) = UnBoolExpr op (mu p)
mapTermVars f mu (IndexExpr e i) = IndexExpr (mu e) i
mapTermVars f mu (Automaton buchi) = Automaton $ fmap (\st -> st { vars = mu (vars st) }) buchi

mapValueVars :: (r1 -> r2) -> GTLValue r1 -> GTLValue r2
mapValueVars mu (GTLIntVal x) = GTLIntVal x
mapValueVars mu (GTLByteVal x) = GTLByteVal x
mapValueVars mu (GTLBoolVal x) = GTLBoolVal x
mapValueVars mu (GTLFloatVal x) = GTLFloatVal x
mapValueVars mu (GTLEnumVal x) = GTLEnumVal x
mapValueVars mu (GTLArrayVal xs) = GTLArrayVal (fmap mu xs)
mapValueVars mu (GTLTupleVal xs) = GTLTupleVal (fmap mu xs)

-- | Binary boolean operators with the traditional semantics.
data BoolOp = And     -- ^ &#8896;
            | Or      -- ^ &#8897;
            | Implies -- ^ &#8658;
            | Until
            | UntilOp
            deriving (Show,Eq,Ord,Enum)

data UnBoolOp = Not
              | Always
              | Next
              | Finally (Maybe Integer)
              deriving (Show,Eq,Ord)

instance Binary BoolOp where
  put x = put (fromIntegral (fromEnum x) :: Word8)
  get = fmap (toEnum . fromIntegral :: Word8 -> BoolOp) get

instance Binary UnBoolOp where
  put Not = put (0::Word8)
  put Always = put (1::Word8)
  put Next = put (2::Word8)
  put (Finally Nothing) = put (3::Word8)
  put (Finally (Just p)) = put (4::Word8) >> put p
  get = do
    i <- get
    case (i::Word8) of
      0 -> return Not
      1 -> return Always
      2 -> return Next
      3 -> return $ Finally Nothing
      4 -> do
        p <- get
        return $ Finally (Just p)

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

{-# LANGUAGE ScopedTypeVariables,GADTs,DeriveDataTypeable,FlexibleInstances,
  ExistentialQuantification, StandaloneDeriving, TypeSynonymInstances, FlexibleContexts,
  DeriveFunctor,RankNTypes #-}
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
import Control.Exception
import Debug.Trace

-- | A fixpoint data structure.
--   Allows the construction of infinite data types from finite constructors.
data Fix f = Fix { unfix :: f (Fix f) }

-- | Represents a GTL term without recursion, which can be added by applying the 'Fix' constructor.
data Term v r = Var v Integer -- ^ A variable with a name and a history level
              | Value (GTLValue r) -- ^ A value which may contain more terms
              | BinBoolExpr BoolOp r r -- ^ A logical binary expression
              | BinRelExpr Relation r r -- ^ A relation between two terms
              | BinIntExpr IntOp r r -- ^ An arithmetic expression
              | UnBoolExpr UnBoolOp r -- ^ A unary logical expression
              | IndexExpr r Integer -- ^ Use an index to access a subcomponent of an expression
              | Automaton (BA [r] String) -- ^ A automaton specifying a temporal logical condition
              | BuiltIn String [r]
              deriving (Eq,Ord)

-- | A constant is a value applied to the 'Fix' constructor
type GTLConstant = Fix GTLValue

-- | An expression is a recursive term
type Expr v = Term v (Fix (Term v))

-- | Used to supply type information to expressions
data Typed a r = Typed { getType :: GTLType
                       , getValue :: a r
                       } deriving (Eq,Ord)

-- | A typed expression is a recursive term with type informations
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

instance (Binary r,Binary v,Ord r,Ord v) => Binary (Term v r) where
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

-- | Construct a variable of a given type
var :: GTLType -> v -> Integer -> TypedExpr v
var t name lvl = Typed t (Var name lvl)

-- | Create a GTL value from a haskell constant
constant :: ToGTL a => a -> TypedExpr v
constant x = Typed (gtlTypeOf x) (Value (toGTL x))

-- | Negate a given expression
gnot :: TypedExpr v -> TypedExpr v
gnot expr
  | getType expr == GTLBool = Typed GTLBool (UnBoolExpr Not (Fix expr))

-- | Create the logical conjunction of two expressions
gand :: TypedExpr v -> TypedExpr v -> TypedExpr v
gand x y
  | getType x == GTLBool && getType y == GTLBool = Typed GTLBool (BinBoolExpr And (Fix x) (Fix y))

-- | Create an equality relation between two expressions
geq :: TypedExpr v -> TypedExpr v -> TypedExpr v
geq x y
  | getType x == getType y = Typed GTLBool (BinRelExpr BinEq (Fix x) (Fix y))

-- | Create an unequality relation between two expressions
gneq :: TypedExpr v -> TypedExpr v -> TypedExpr v
gneq x y
  | getType x == getType y = Typed GTLBool (BinRelExpr BinNEq (Fix x) (Fix y))

-- | Create a enumeration value for a given enumeration type
enumConst :: [String] -> String -> TypedExpr v
enumConst tp v = Typed (GTLEnum tp) (Value (GTLEnumVal v))

instance Binary (a r) => Binary (Typed a r) where
  put x = put (getType x) >> put (getValue x)
  get = do
    tp <- get
    val <- get
    return (Typed tp val)

instance (Binary v,Ord v) => Binary (Fix (Typed (Term v))) where
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

instance Eq v => Eq (Fix (Term v)) where
  e1 == e2 = (unfix e1) == (unfix e2)

instance Ord v => Ord (Fix (Term v)) where
  compare e1 e2 = compare (unfix e1) (unfix e2)

instance Eq (Fix GTLValue) where
  e1 == e2 = (unfix e1) == (unfix e2)

instance Ord (Fix GTLValue) where
  compare e1 e2 = compare (unfix e1) (unfix e2)

-- | Render a term by applying a recursive rendering function to it.
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

-- | Helper function for type checking: If the two supplied types are the same,
--   return 'Right' (), otherwise generate an error using the supplied identifier.
enforceType :: String -- ^ A string representation of the type checked entity
               -> GTLType -- ^ The actual type of the entity
               -> GTLType -- ^ The expected type
               -> Either String ()
enforceType expr ac tp = if ac == tp
                         then Right ()
                         else Left $ expr ++ " should have type "++show tp++" but it has type "++show ac

-- | Convert a untyped, generalized expression into a typed expression by performing type checking
makeTypedExpr :: (Ord v,Show v) => (Maybe String -> String -> Either String v) -- ^ A function to create variable names from qualified and unqualified variables
                 -> Map v GTLType -- ^ A type mapping for variables
                 -> Set [String] -- ^ All possible enum types
                 -> GExpr -- ^ The generalized expression to type check
                 -> Either String (TypedExpr v)
makeTypedExpr f varmp enums expr = parseTerm f Map.empty expr >>= typeCheck varmp enums

-- | Convert an expression into a constant, if it is one.
--   If not, return 'Nothing'.
getConstant :: TypedExpr v -> Maybe GTLConstant
getConstant e = case getValue e of
  Value p -> do
    np <- mapM (getConstant.unfix) p
    return $ Fix np
  _ -> Nothing

-- | Type-check an untyped expression.
typeCheck :: (Ord v,Show v) => Map v GTLType -- ^ A type mapping for all variables
             -> Set [String] -- ^ A set of all allowed enum types
             -> Expr v -- ^ The untyped expression
             -> Either String (TypedExpr v)
typeCheck varmp enums = typeCheck' (\expr -> typeCheck varmp enums (unfix expr) >>= return.Fix) (getType . unfix) (show . untyped . unfix) varmp enums
  where
    typeCheck' :: (Ord v,Show v,Ord r2)
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
      ntrans <- mapM (\trans -> do
                         trans' <- mapM (\(cond,trg) -> do
                                            ncond <- mapM mu cond
                                            return (ncond,trg)
                                        ) (Set.toList trans)
                         return $ Set.fromList trans') (baTransitions buchi)
      return $ Typed GTLBool (Automaton $ buchi { baTransitions = ntrans })
    typeCheck' mu mutp mus varmp enums (BuiltIn name args) = do
      tps <- mapM mu args
      case name of
        "equal" -> do
          case tps of
            [] -> return $ Typed GTLBool (BuiltIn name [])
            x:xs -> do
              mapM_ (\tp -> if (mutp tp)==(mutp x)
                            then return ()
                            else Left "Not all \"equal\" arguments have the same type") xs
              return $ Typed GTLBool (BuiltIn name tps)
        _ -> Left $ "Unknown built-in "++show name

-- | Discard type information for an expression
untyped :: TypedExpr v -> Expr v
untyped expr = fmap (Fix . untyped . unfix) (getValue expr)

-- | Convert a generalized expression into a regular one.
parseTerm :: Ord v => (Maybe String -> String -> Either String v) -- ^ A function to create variable names from qualified or unqualified variables
             -> ExistsBinding v -- ^ All existentially bound variables
             -> GExpr -- ^ The generalized expression
             -> Either String (Expr v)
parseTerm f ex = parseTerm' (\ex' expr -> parseTerm f ex' expr >>= return.Fix) f ex
  where
    parseTerm' :: Ord r => (ExistsBinding v -> GExpr -> Either String r)
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
      stmp <- foldlM (\mp st -> do
                         let (exprs,nexts) = partitionEithers (stateContent st)
                         rexpr <- mapM (mu ex) exprs
                         rnexts <- mapM (\(trg,cond) -> do
                                            rcond <- case cond of
                                              Nothing -> return Nothing
                                              Just cond' -> do
                                                r <- mu ex cond'
                                                return $ Just r
                                            return (rcond,trg)
                                        ) nexts
                         return $ Map.insert (stateName st) (stateInitial st,stateFinal st,rexpr,rnexts) mp
                     ) Map.empty sts
      return $ Automaton $ BA { baTransitions = fmap (\(_,_,_,nxts) -> Set.fromList [ (case cond of
                                                                                          Nothing -> tcond
                                                                                          Just t -> t:tcond,trg)
                                                                                    | (cond,trg) <- nxts, 
                                                                                      let (_,_,tcond,_) = stmp!trg
                                                                                    ]) stmp
                              , baInits = Map.keysSet $ Map.filter (\(init,_,_,_) -> init) stmp
                              , baFinals = Map.keysSet $ Map.filter (\(_,fin,_,_) -> fin) stmp
                              }
    parseTerm' mu f ex (GIndex expr ind) = do
      rind <- case ind of
        GConst x -> return x
        _ -> Left $ "Index must be an integer"
      rexpr <- mu ex expr
      return $ IndexExpr rexpr (fromIntegral rind)
    parseTerm' mu f ex (GBuiltIn name args) = do
      res <- mapM (mu ex) args
      return $ BuiltIn name res

-- | Distribute a negation as deep as possible into an expression until it only ever occurs in front of variables.
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

-- | If negations occur in the given expression, push them as deep into the expression as possible.
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

-- | Extract all variables used in the given term.
getTermVars :: (r -> [(v,[Integer],Integer,GTLType)]) -> Typed (Term v) r -> [(v,[Integer],Integer,GTLType)]
getTermVars mu expr = case getValue expr of
  Var n lvl -> [(n,[],lvl,getType expr)]
  Value x -> getValueVars mu x
  BinBoolExpr op l r -> (mu l)++(mu r)
  BinRelExpr op l r -> (mu l)++(mu r)
  BinIntExpr op l r -> (mu l)++(mu r)
  UnBoolExpr op p -> mu p
  IndexExpr e i -> fmap (\(v,idx,lvl,tp) -> (v,i:idx,lvl,tp)) (mu e)
  Automaton buchi -> concat [ concat $ fmap mu cond
                            | trans <- Map.elems (baTransitions buchi), 
                              (cond,_) <- Set.toList trans
                            ]
  BuiltIn _ args -> concat $ fmap mu args

-- | Get all variables used in a GTL value.
getValueVars :: (r -> [(v,[Integer],Integer,GTLType)]) -> GTLValue r -> [(v,[Integer],Integer,GTLType)]
getValueVars mu (GTLArrayVal xs) = concat (fmap mu xs)
getValueVars mu (GTLTupleVal xs) = concat (fmap mu xs)
getValueVars _ _ = []

-- | Change the type of the variables in an expression.
mapGTLVars :: (Ord v,Ord w) => (v -> w) -> TypedExpr v -> TypedExpr w
mapGTLVars f expr = Typed (getType expr) (mapTermVars f (Fix . mapGTLVars f . unfix) (getValue expr))


-- | Change the type of the variables used in a term
mapTermVars :: (Ord r1,Ord r2) => (v -> w) -> (r1 -> r2) -> Term v r1 -> Term w r2
mapTermVars f mu (Var name lvl) = Var (f name) lvl
mapTermVars f mu (Value x) = Value (mapValueVars mu x)
mapTermVars f mu (BinBoolExpr op l r) = BinBoolExpr op (mu l) (mu r)
mapTermVars f mu (BinRelExpr rel l r) = BinRelExpr rel (mu l) (mu r)
mapTermVars f mu (BinIntExpr op l r) = BinIntExpr op (mu l) (mu r)
mapTermVars f mu (UnBoolExpr op p) = UnBoolExpr op (mu p)
mapTermVars f mu (IndexExpr e i) = IndexExpr (mu e) i
mapTermVars f mu (Automaton buchi)
  = Automaton $ buchi { baTransitions = fmap (Set.map (\(cond,trg) -> (fmap mu cond,trg))) (baTransitions buchi) }

-- | Change the type of the variables used in a value
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

-- | Unary boolean operators with the traditional semantics.
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

-- | Represents the relations in which two expressions can stand
data ExprOrdering = EEQ -- ^ Both expressions define the same value space
                  | ENEQ -- ^ The expressions define non-overlapping value spaces
                  | EGT -- ^ The value space of the second expression is contained by the first
                  | ELT -- ^ The value space of the first expression is contained by the second
                  | EUNK -- ^ The expressions have overlapping value spaces or the relation isn't known
                  deriving (Show,Eq,Ord)

-- | Convert a typed expression to a linear combination of variables.
toLinearExpr :: Ord v => TypedExpr v -> Map (Map (v,Integer) Integer) GTLConstant
toLinearExpr e = case getValue e of
  Var v h -> Map.singleton (Map.singleton (v,h) 1) one
  Value v -> let Just c = getConstant e
             in Map.singleton Map.empty c
  BinIntExpr op lhs rhs
    -> let p1 = toLinearExpr (unfix lhs)
           p2 = toLinearExpr (unfix rhs)
       in case op of
         OpPlus -> Map.unionWith (constantOp (+)) p1 p2
         OpMinus -> Map.unionWith (constantOp (-)) p1 p2
         OpMult -> Map.fromList [ (Map.unionWith (+) t1 t2,constantOp (*) c1 c2) | (t1,c1) <- Map.toList p1, (t2,c2) <- Map.toList p2 ]
  where
    one = Fix $ case getType e of
      GTLInt -> GTLIntVal 1
      GTLByte -> GTLByteVal 1
      GTLFloat -> GTLFloatVal 1

-- | Apply an operation to a GTL value.
constantOp :: (forall a. Num a => a -> a -> a)
              -> GTLConstant -> GTLConstant -> GTLConstant
constantOp iop x y = Fix $ case unfix x of
  GTLIntVal x' -> let GTLIntVal y' = unfix y in GTLIntVal (iop x' y')
  GTLByteVal x' -> let GTLByteVal y' = unfix y in GTLByteVal (iop x' y')
  GTLFloatVal x' -> let GTLFloatVal y' = unfix y in GTLFloatVal (iop x' y')

compareExprDebug :: (Ord v,Show v) => TypedExpr v -> TypedExpr v -> ExprOrdering
compareExprDebug e1 e2 = let res = compareExpr e1 e2
                         in trace ("COMP ["++show e1++"] # ["++show e2++"]\t\t"++show res) res

-- TODO: Use a constraint solver here?
-- | Compare the value spaces of two expressions
compareExpr :: Ord v => TypedExpr v -> TypedExpr v -> ExprOrdering
compareExpr e1 e2
  = assert (getType e1 == getType e2) $
    case getType e1 of
      GTLInt -> lincomp
      GTLByte -> lincomp
      GTLFloat -> lincomp
      GTLBool -> case getValue e2 of
        UnBoolExpr Not (Fix e2') -> case compareExpr e1 e2' of
          EEQ -> ENEQ
          _ -> EUNK
        _ -> case getValue e1 of
          Var v1 h1 -> case getValue e2 of
            Var v2 h2 -> if v1==v2 && h1==h2
                         then EEQ
                         else EUNK
            _ -> EUNK
          Value c1 -> case getValue e2 of
            Value c2 -> if c1 == c2
                        then EEQ
                        else ENEQ
            _ -> EUNK
          IndexExpr (Fix ee1) i1 -> case getValue e2 of
            IndexExpr (Fix ee2) i2 -> case compareExpr ee1 ee2 of
              EEQ -> if i1==i2
                     then EEQ
                     else EUNK
              _ -> EUNK
            _ -> EUNK
          BinRelExpr op1 (Fix l1) (Fix r1) -> case getValue e2 of
            BinRelExpr op2 (Fix l2) (Fix r2) -> case op1 of
              BinEq -> case op2 of
                BinEq -> case compareExpr l1 l2 of
                  EEQ -> compareExpr r1 r2
                  ENEQ -> case compareExpr r1 r2 of
                    EEQ -> ENEQ
                    ENEQ -> EUNK
                    _ -> EUNK
                  _ -> EUNK
                BinNEq -> case compareExpr l1 l2 of
                  EEQ -> case compareExpr r1 r2 of
                    EEQ -> ENEQ
                    _ -> ELT
                  ENEQ -> case compareExpr r1 r2 of
                    EEQ -> ENEQ
                    _ -> EUNK
                  _ -> EUNK
                _ -> EUNK
              BinNEq -> case op2 of
                BinNEq -> case compareExpr l1 l2 of
                  EEQ -> case compareExpr r1 r2 of
                    EEQ -> EEQ
                    ENEQ -> if getType l1 == GTLBool
                            then ENEQ
                            else EUNK
                    _ -> EUNK
                  _ -> EUNK
                _ -> EUNK
              _ -> EUNK
            _ -> EUNK
          UnBoolExpr Not (Fix p) -> case getValue e2 of
            UnBoolExpr Not (Fix p') -> case compareExpr p p' of
              ELT -> EGT
              EGT -> ELT
              r -> r
            _ -> case compareExpr p e2 of
              EEQ -> ENEQ
              _ -> EUNK
      _ -> case getValue e1 of
        Value c1 -> case getValue e2 of
          Value c2 -> if c1 == c2
                      then EEQ
                      else ENEQ
          _ -> EUNK
        _ -> if getValue e1 == getValue e2
             then EEQ
             else EUNK
    where
      p1 = toLinearExpr e1
      p2 = toLinearExpr e2
      lincomp = if p1 == p2
                then EEQ
                else (if Map.size p1 == 1 && Map.size p2 == 1
                      then (case Map.lookup Map.empty p1 of
                               Nothing -> EUNK
                               Just c1 -> case Map.lookup Map.empty p2 of
                                 Nothing -> EUNK
                                 Just c2 -> ENEQ)
                      else EUNK)

{-# LANGUAGE ScopedTypeVariables,GADTs,DeriveDataTypeable,FlexibleInstances,
  ExistentialQuantification, StandaloneDeriving, TypeSynonymInstances, FlexibleContexts,
  DeriveFunctor,RankNTypes #-}
{-| Provides the expression data type as well as the type-checking algorithm.
 -}
module Language.GTL.Expression
       (Fix(..),
        Term(..),
        GTLConstant,
        Expr,
        Typed(..),
        TypedExpr,
        BoolOp(..),
        UnBoolOp(..),
        TimeSpec(..),
        IntOp(..),
        Relation(..),
        ExprOrdering(..),
        VarUsage(..),
        var,
        constant,
        gnot,
        gand,
        gor,
        geq,
        gneq,
        galways,
        gfinally,
        gimplies,
        enumConst,
        isInput,isOutput,isState,
        typeCheck,
        compareExpr,
        compareExprDebug,
        distributeNot,
        makeTypedExpr,
        getConstant,
        mapGTLVars,
        getVars,
        relTurn,
        relNot,
        maximumHistory,
        getClocks,
        automatonClocks,
        showTermWith
        ) where

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
import Data.Fix
import Debug.Trace
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad (liftM)
import Text.Show

data VarUsage = Input
              | Output
              | StateIn
              | StateOut
              deriving (Show,Eq,Ord)

-- | Represents a GTL term without recursion, which can be added by applying the 'Fix' constructor.
data Term v r = Var v Integer VarUsage -- ^ A variable with a name and a history level
              | Value (GTLValue r) -- ^ A value which may contain more terms
              | BinBoolExpr BoolOp r r -- ^ A logical binary expression
              | BinRelExpr Relation r r -- ^ A relation between two terms
              | BinIntExpr IntOp r r -- ^ An arithmetic expression
              | UnBoolExpr UnBoolOp r -- ^ A unary logical expression
              | IndexExpr r Integer -- ^ Use an index to access a subcomponent of an expression
              | Automaton (BA [r] String) -- ^ A automaton specifying a temporal logical condition
              | ClockReset Integer Integer
              | ClockRef Integer
              | BuiltIn String [r]
              deriving (Eq,Ord)

-- | A constant is a value applied to the 'Fix' constructor
type GTLConstant = Fix GTLValue

-- | An expression is a recursive term
type Expr v = Fix (Term v)

-- | Used to supply type information to expressions
data Typed a r = Typed { getType :: GTLType
                       , getValue :: a r
                       } deriving (Eq,Ord)

-- | A typed expression is a recursive term with type informations
type TypedExpr v = Fix (Typed (Term v))

instance Functor (Term v) where
  fmap f (Var x lvl u) = Var x lvl u
  fmap f (Value val) = Value (fmap f val)
  fmap f (BinBoolExpr op l r) = BinBoolExpr op (f l) (f r)
  fmap f (BinRelExpr op l r) = BinRelExpr op (f l) (f r)
  fmap f (BinIntExpr op l r) = BinIntExpr op (f l) (f r)
  fmap f (UnBoolExpr op p) = UnBoolExpr op (f p)
  fmap f (IndexExpr x i) = IndexExpr (f x) i
  fmap f (ClockReset x y) = ClockReset x y
  fmap f (ClockRef x) = ClockRef x

instance Functor a => Functor (Typed a) where
  fmap f t = Typed { getType = getType t
                   , getValue = fmap f (getValue t)
                   }

instance Binary VarUsage where
  put u = put ((case u of
                   Input -> 0
                   Output -> 1
                   StateIn -> 2
                   StateOut -> 3)::Word8)
  get = do
    w <- get
    return $ case (w::Word8) of
      0 -> Input
      1 -> Output
      2 -> StateIn
      3 -> StateOut

instance (Binary r,Binary v,Ord v) => Binary (Term v r) where
  put (Var v l u) = put (0::Word8) >> put v >> put l >> put u
  put (Value val) = put (1::Word8) >> put val
  put (BinBoolExpr op l r) = put (2::Word8) >> put op >> put l >> put r
  put (BinRelExpr op l r) = put (3::Word8) >> put op >> put l >> put r
  put (BinIntExpr op l r) = put (4::Word8) >> put op >> put l >> put r
  put (UnBoolExpr op p) = put (5::Word8) >> put op >> put p
  put (IndexExpr e i) = put (6::Word8) >> put i >> put e
  put (Automaton aut) = put (7::Word8) >> put aut
  put (ClockReset x y) = put (8::Word8) >> put x >> put y
  put (ClockRef x) = put (9::Word8) >> put x
  get = do
    (i::Word8) <- get
    case i of
      0 -> do
        v <- get
        l <- get
        u <- get
        return $ Var v l u
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
      8 -> do
        x <- get
        y <- get
        return $ ClockReset x y
      9 -> do
        x <- get
        return $ ClockRef x

isInput :: VarUsage -> Bool
isInput Input = True
isInput StateIn = True
isInput _ = False

isOutput :: VarUsage -> Bool
isOutput Output = True
isOutput StateOut = True
isOutput _ = False

isState :: VarUsage -> Bool
isState StateIn = True
isState StateOut = True
isState _ = False

-- | Construct a variable of a given type
var :: GTLType -> v -> Integer -> VarUsage -> TypedExpr v
var t name lvl u = Fix $ Typed t (Var name lvl u)

-- | Create a GTL value from a haskell constant
constant :: ToGTL a => a -> TypedExpr v
constant x = Fix $ Typed (gtlTypeOf x) (Value (toGTL x))

-- | Negate a given expression
gnot :: TypedExpr v -> TypedExpr v
gnot expr
  | getType (unfix expr) == gtlBool = Fix $ Typed gtlBool (UnBoolExpr Not expr)

-- | Create the logical conjunction of two expressions
gand :: TypedExpr v -> TypedExpr v -> TypedExpr v
gand x y
  | getType (unfix x) == gtlBool && getType (unfix y) == gtlBool = Fix $ Typed gtlBool (BinBoolExpr And x y)

-- | Create the logical disjunction of two expressions
gor :: TypedExpr v -> TypedExpr v -> TypedExpr v
gor x y
  | getType (unfix x) == gtlBool && getType (unfix y) == gtlBool = Fix $ Typed gtlBool (BinBoolExpr Or x y)

-- | Create an equality relation between two expressions
geq :: TypedExpr v -> TypedExpr v -> TypedExpr v
geq x y
  | getType (unfix x) == getType (unfix y) = Fix $ Typed gtlBool (BinRelExpr BinEq x y)

-- | Create an unequality relation between two expressions
gneq :: TypedExpr v -> TypedExpr v -> TypedExpr v
gneq x y
  | getType (unfix x) == getType (unfix y) = Fix $ Typed gtlBool (BinRelExpr BinNEq x y)

galways :: TypedExpr v -> TypedExpr v
galways x
  | getType (unfix x) == gtlBool = Fix $ Typed gtlBool (UnBoolExpr Always x)

gfinally :: TypedExpr v -> TypedExpr v
gfinally x
  | getType (unfix x) == gtlBool = Fix $ Typed gtlBool (UnBoolExpr (Finally NoTime) x)

gimplies :: TypedExpr v -> TypedExpr v -> TypedExpr v
gimplies x y
  | getType (unfix x) == gtlBool && getType (unfix y) == gtlBool = Fix $ Typed gtlBool (BinBoolExpr Implies x y)

-- | Create a enumeration value for a given enumeration type
enumConst :: [String] -> String -> TypedExpr v
enumConst tp v = Fix $ Typed (gtlEnum tp) (Value (GTLEnumVal v))

instance Binary2 a => Binary2 (Typed a) where
  put2 x = put (getType x) >> put2 (getValue x)
  get2 = do
    tp <- get
    val <- get2
    return (Typed tp val)

instance Eq v => Eq2 (Term v) where
  eq2 = (==)

instance Ord v => Ord2 (Term v) where
  compare2 = compare

instance (Binary v,Ord v) => Binary2 (Term v) where
  get2 = get
  put2 = put

instance (Show v) => Show2 (Term v) where
  show2 = showTerm show

instance Show2 a => Show2 (Typed a) where
  show2 x = show2 (getValue x)

instance Eq v => Eq2 (Typed (Term v)) where
  eq2 = (==)

instance Ord v => Ord2 (Typed (Term v)) where
  compare2 = compare


-- | Render a term by applying a recursive rendering function to it.
showTerm :: Show v => (r -> String) -> Term v r -> String
showTerm g t = showTermWith (\name lvl -> showsPrec 0 name . (if lvl==0 then id else (showChar '_' . showsPrec 0 lvl))) (\p r -> showString $ g r) 0 t ""

opPrec And = 5
opPrec Or = 4
opPrec Implies = 6
opPrec (Until _) = 3

intPrec OpPlus = 9
intPrec OpMinus = 10
intPrec OpMult = 11
intPrec OpDiv = 12

unPrec Not = 7
unPrec Always = 2
unPrec (Next _) = 2

showTermWith :: (v -> Integer -> ShowS) -> (Integer -> r -> ShowS) -> Integer -> Term v r -> ShowS
showTermWith f g p (Var name lvl u) = (if u == StateOut
                                       then showString "#out " 
                                       else id) . f name lvl
showTermWith f g p (Value val) = showString $ showGTLValue (\r -> g 0 r "") 0 val ""
showTermWith f g p (BinBoolExpr op l r)
  = showParen (p > opPrec op) $
    (g (opPrec op) l) .
    (case op of
        And -> showString " and "
        Or -> showString " or "
        Implies -> showString " implies "
        Until ts -> showString $ " until"++show ts++" "
    ) . (g (opPrec op) r)
showTermWith f g p (BinRelExpr rel l r)
  = showParen (p > 8) $
    (g 8 l) . (showString $ case rel of
                  BinLT -> " < "
                  BinLTEq -> " <= "
                  BinGT -> " > "
                  BinGTEq -> " >= "
                  BinEq -> " = "
                  BinNEq -> " != "
                  BinAssign -> " := ") . (g 8 r)
showTermWith f g p (BinIntExpr op l r)
  = showParen (p > intPrec op) $ 
    (g (intPrec op) l) .
    (showString $ case op of
        OpPlus -> " + "
        OpMinus -> " - "
        OpMult -> " * "
        OpDiv -> " / ") .
    (g (intPrec op) r)
showTermWith f g p (UnBoolExpr op arg)
  = showParen (p > unPrec op) $ 
    (showString $ case op of
        Not -> "not "
        Always -> "always "
        Next ts -> "next"++show ts++" ") . 
    (g (unPrec op) arg)
showTermWith f g p (IndexExpr expr idx) = showParen (p > 13) $ g 13 expr . showChar '[' . showsPrec 0 idx . showChar ']'
showTermWith f g p (ClockReset clk limit) = showString "clock(" .  showsPrec 0 clk . showString ") := " . showsPrec 0 limit
showTermWith f g p (ClockRef clk) = showString "clock(" . showsPrec 0 clk . showChar ')'

-- | Helper function for type checking: If the two supplied types are the same,
--   return 'Right' (), otherwise generate an error using the supplied identifier.
enforceType :: MonadError String m =>
              String -- ^ A string representation of the type checked entity
               -> GTLType -- ^ The actual type of the entity
               -> GTLType -- ^ The expected type
               -> m ()
enforceType expr ac tp = if baseType ac == baseType tp
                         then return ()
                         else throwError $ expr ++ " should have type "++show tp++" but it has type "++show ac

-- | Convert a untyped, generalized expression into a typed expression by performing type checking
makeTypedExpr :: (Ord v,Show v,MonadError String m) =>
                (Maybe String -> String -> Maybe ContextInfo -> m (v,VarUsage)) -- ^ A function to create variable names from qualified and unqualified variables
                 -> Map v GTLType -- ^ A type mapping for variables
                 -> Set [String] -- ^ All possible enum types
                 -> GExpr -- ^ The generalized expression to type check
                 -> m (TypedExpr v)
makeTypedExpr f varmp enums expr = parseTerm f Map.empty Nothing expr >>= typeCheck varmp enums

-- | Convert an expression into a constant, if it is one.
--   If not, return 'Nothing'.
getConstant :: TypedExpr v -> Maybe GTLConstant
getConstant e = case getValue (unfix e) of
  Value p -> do
    np <- mapM getConstant p
    return $ Fix np
  _ -> Nothing

-- | Type-check an untyped expression.
typeCheck :: (Ord v,Show v,MonadError String m) =>
            Map v GTLType -- ^ A type mapping for all variables
             -> Set [String] -- ^ A set of all allowed enum types
             -> Expr v -- ^ The untyped expression
             -> m (TypedExpr v)
typeCheck varmp enums e = liftM Fix $ typeCheck' (typeCheck varmp enums) (getType.unfix) (show . untyped) varmp enums (unfix e)
  where
    typeCheck' :: (Ord v,Show v,Ord r2,MonadError String m) =>
                  (r1 -> m r2)
                  -> (r2 -> GTLType)
                  -> (r2 -> String)
                  -> Map v GTLType -> Set [String] -> Term v r1 -> m (Typed (Term v) r2)
    typeCheck' mu mutp mus varmp enums (Var x lvl u) = case Map.lookup x varmp of
      Nothing -> throwError $ "Unknown variable "++show x
      Just tp -> return $ Typed tp (Var x lvl u)
    typeCheck' mu mutp mus varmp enums (Value val) = case val of
      GTLIntVal i -> return $ Typed gtlInt (Value $ GTLIntVal i)
      GTLByteVal i -> return $ Typed gtlByte (Value $ GTLByteVal i)
      GTLBoolVal i -> return $ Typed gtlBool (Value $ GTLBoolVal i)
      GTLFloatVal i -> return $ Typed gtlFloat (Value $ GTLFloatVal i)
      GTLEnumVal x -> case find (elem x) enums of
        Nothing -> throwError $ "Unknown enum value "++show x
        Just e -> return $ Typed (gtlEnum e) (Value $ GTLEnumVal x)
      GTLArrayVal vals -> do
        res <- mapM mu vals
        case res of
          [] -> throwError "Empty arrays not allowed"
          (x:xs) -> mapM_ (\tp -> if (mutp tp)==(mutp x)
                                  then return ()
                                  else throwError "Not all array elements have the same type") xs
        return $ Typed (gtlArray (genericLength res) (mutp (head res))) (Value $ GTLArrayVal res)
      GTLTupleVal vals -> do
        tps <- mapM mu vals
        return $ Typed (gtlTuple (fmap mutp tps)) (Value $ GTLTupleVal tps)
    typeCheck' mu mutp mus varmp enums (BinBoolExpr op l r) = do
      ll <- mu l
      rr <- mu r
      enforceType (mus ll) (mutp ll) gtlBool
      enforceType (mus rr) (mutp rr) gtlBool
      return $ Typed gtlBool (BinBoolExpr op ll rr)
    typeCheck' mu mutp mus varmp enums (BinRelExpr rel l r) = do
      ll <- mu l
      rr <- mu r
      if rel==BinEq || rel==BinNEq
        then (do
                 enforceType (mus rr) (mutp rr) (mutp ll))
        else (do
                 enforceType (mus ll) (mutp ll) gtlInt
                 enforceType (mus rr) (mutp rr) gtlInt)
      return $ Typed gtlBool (BinRelExpr rel ll rr)
    typeCheck' mu mutp mus varmp enums (BinIntExpr op l r) = do
      ll <- mu l
      rr <- mu r
      enforceType (mus ll) (mutp ll) gtlInt
      enforceType (mus rr) (mutp rr) gtlInt
      return $ Typed gtlInt (BinIntExpr op ll rr)
    typeCheck' mu mutp mus varmp enums (UnBoolExpr op p) = do
      pp <- mu p
      enforceType (mus pp) (mutp pp) gtlBool
      return $ Typed gtlBool (UnBoolExpr op pp)
    typeCheck' mu mutp mus varmp enums (IndexExpr p idx) = do
      pp <- mu p
      case unfix $ baseType $ mutp pp of
        GTLArray sz tp -> if idx < sz
                          then return $ Typed tp (IndexExpr pp idx)
                          else throwError $ "Index "++show idx++" out of bounds "++show sz
        GTLTuple tps -> if idx < genericLength tps
                        then return $ Typed (tps `genericIndex` idx) (IndexExpr pp idx)
                        else throwError $ "Index "++show idx++" out of bounds "++show (genericLength tps)
        _ -> throwError $ "Expression " ++ mus pp ++ " is not indexable"
    typeCheck' mu mutp mus varmp enums (Automaton buchi) = do
      ntrans <- mapM (\trans -> mapM (\(cond,trg) -> do
                                         ncond <- mapM mu cond
                                         return (ncond,trg)
                                     ) trans
                     ) (baTransitions buchi)
      return $ Typed gtlBool (Automaton $ buchi { baTransitions = ntrans })
    typeCheck' mu mutp mus varmp enums (BuiltIn name args) = do
      tps <- mapM mu args
      case name of
        "equal" -> do
          case tps of
            [] -> return $ Typed gtlBool (BuiltIn name [])
            x:xs -> do
              mapM_ (\tp -> if (mutp tp)==(mutp x)
                            then return ()
                            else throwError "Not all \"equal\" arguments have the same type") xs
              return $ Typed gtlBool (BuiltIn name tps)
        _ -> throwError $ "Unknown built-in "++show name

-- | Discard type information for an expression
untyped :: TypedExpr v -> Expr v
untyped expr = Fix $ fmap untyped (getValue (unfix expr))

-- | Convert a generalized expression into a regular one.
parseTerm :: (MonadError String m, Ord v) =>
            (Maybe String -> String -> Maybe ContextInfo -> m (v,VarUsage)) -- ^ A function to create variable names and usage from qualified or unqualified variables
             -> ExistsBinding v -- ^ All existentially bound variables
             -> Maybe ContextInfo -- ^ Information about variable context (input or output)
             -> GExpr -- ^ The generalized expression
             -> m (Expr v)
parseTerm f ex inf e = liftM Fix $ parseTerm' (\ex' inf' expr -> parseTerm f ex' inf' expr) f ex inf e
  where
    parseTerm' :: (MonadError String m, Ord r) => (ExistsBinding v -> Maybe ContextInfo -> GExpr -> m r)
                  -> (Maybe String -> String -> Maybe ContextInfo -> m (v,VarUsage))
                  -> ExistsBinding v
                  -> Maybe ContextInfo
                  -> GExpr -> m (Term v r)
    parseTerm' mu f ex inf (GBin op tspec l r) = do
      rec_l <- mu ex inf l
      rec_r <- mu ex inf r
      case toBoolOp op tspec of
        Just rop -> return $ BinBoolExpr rop rec_l rec_r
        Nothing -> case toRelOp op of
          Just rop -> return $ BinRelExpr rop rec_l rec_r
          Nothing -> case toIntOp op of
            Just rop -> return $ BinIntExpr rop rec_l rec_r
            Nothing -> throwError $ "Internal error, please implement parseTerm for operator "++show op
    parseTerm' mu f ex inf (GUn op ts p) = do
      rec <- mu (case op of
                    GOpNext -> fmap (\(v,lvl,u) -> (v,lvl+1,u)) ex
                    _ -> ex
                ) inf p
      return $ UnBoolExpr (case op of
                              GOpAlways -> Always
                              GOpNext -> Next ts
                              GOpNot -> Not
                              GOpFinally -> Finally ts
                              GOpAfter -> After ts
                          ) rec
    parseTerm' mu f ex inf (GConst x) = return $ Value (GTLIntVal $ fromIntegral x)
    parseTerm' mu f ex inf (GConstBool x) = return $ Value (GTLBoolVal x)
    parseTerm' mu f ex inf (GEnum x) = return $ Value (GTLEnumVal x)
    parseTerm' mu f ex inf (GTuple args) = do
      res <- mapM (mu ex inf) args
      return $ Value (GTLTupleVal res)
    parseTerm' mu f ex inf (GArray args) = do
      res <- mapM (mu ex inf) args
      return $ Value (GTLArrayVal res)
    parseTerm' mu f ex inf (GVar q n) = case q of
      Nothing -> case Map.lookup n ex of
        Nothing -> do
          (var,u) <- f q n inf
          return $ Var var 0 u
        Just (r,lvl,u) -> return $ Var r lvl u
      Just _ -> do
        (var,u) <- f q n inf
        return $ Var var 0 u
    parseTerm' mu f ex inf (GExists b q n expr) = case q of
      Nothing -> case Map.lookup n ex of
        Nothing -> do
          (var,u) <- f q n inf
          parseTerm' mu f (Map.insert b (var,0,u) ex) inf expr
        Just (v,lvl,u) -> parseTerm' mu f (Map.insert b (v,lvl,u) ex) inf expr
      Just _ -> do
        (var,u) <- f q n inf
        parseTerm' mu f (Map.insert b (var,0,u) ex) inf expr
    parseTerm' mu f ex inf (GAutomaton sts) = do
      stmp <- foldlM (\mp st -> do
                         let (exprs,nexts) = partitionEithers (stateContent st)
                         rexpr <- mapM (mu ex inf) exprs
                         rnexts <- mapM (\(trg,cond) -> do
                                            rcond <- case cond of
                                              Nothing -> return Nothing
                                              Just cond' -> do
                                                r <- mu ex inf cond'
                                                return $ Just r
                                            return (rcond,trg)
                                        ) nexts
                         return $ Map.insert (stateName st) (stateInitial st,stateFinal st,rexpr,rnexts) mp
                     ) Map.empty sts
      return $ Automaton $ BA { baTransitions = fmap (\(_,_,_,nxts) -> [ (case cond of
                                                                             Nothing -> tcond
                                                                             Just t -> t:tcond,trg)
                                                                       | (cond,trg) <- nxts,
                                                                         let (_,_,tcond,_) = stmp!trg
                                                                       ]) stmp
                              , baInits = Map.keysSet $ Map.filter (\(init,_,_,_) -> init) stmp
                              , baFinals = Map.keysSet $ Map.filter (\(_,fin,_,_) -> fin) stmp
                              }
    parseTerm' mu f ex inf (GIndex expr ind) = do
      rind <- case ind of
        GConst x -> return x
        _ -> throwError $ "Index must be an integer"
      rexpr <- mu ex inf expr
      return $ IndexExpr rexpr (fromIntegral rind)
    parseTerm' mu f ex inf (GBuiltIn name args) = do
      res <- mapM (mu ex inf) args
      return $ BuiltIn name res
    parseTerm' mu f ex _ (GContext inf expr) = parseTerm' mu f ex (Just inf) expr

-- | Distribute a negation as deep as possible into an expression until it only ever occurs in front of variables.
distributeNot :: TypedExpr v -> TypedExpr v
distributeNot expr
  | getType (unfix expr) == gtlBool = case getValue (unfix expr) of
    Var x lvl u -> Fix $ Typed gtlBool $ UnBoolExpr Not expr
    Value (GTLBoolVal x) -> Fix $ Typed gtlBool $ Value (GTLBoolVal (not x))
    BinBoolExpr op l r -> Fix $ Typed gtlBool $ case op of
      And -> BinBoolExpr Or (distributeNot l) (distributeNot r)
      Or -> BinBoolExpr And (distributeNot l) (distributeNot r)
      Implies -> BinBoolExpr And (pushNot l) (distributeNot r)
      Until ts -> BinBoolExpr (UntilOp ts) (distributeNot l) (distributeNot r)
    BinRelExpr rel l r -> Fix $ Typed gtlBool $ BinRelExpr (relNot rel) l r
    UnBoolExpr op p -> case op of
      Not -> pushNot p
      Next NoTime -> Fix $ Typed gtlBool $ UnBoolExpr (Next NoTime) (distributeNot p)
      Always -> Fix $ Typed gtlBool $ BinBoolExpr (Until NoTime) (Fix (Typed gtlBool (Value (GTLBoolVal True)))) (distributeNot p)
    IndexExpr e i -> Fix $ Typed gtlBool $ UnBoolExpr Not expr
    Automaton buchi -> Fix $ Typed gtlBool $ UnBoolExpr Not expr
    ClockRef x -> Fix $ Typed gtlBool $ UnBoolExpr Not expr
    ClockReset _ _ -> error "Can't negate a clock reset"

-- | If negations occur in the given expression, push them as deep into the expression as possible.
pushNot :: TypedExpr v -> TypedExpr v
pushNot expr
  | getType (unfix expr) == gtlBool = case getValue (unfix expr) of
    BinBoolExpr op l r -> Fix $ Typed gtlBool $ BinBoolExpr op (pushNot l) (pushNot r)
    UnBoolExpr Not p -> distributeNot p
    UnBoolExpr op p -> Fix $ Typed gtlBool $ UnBoolExpr op (pushNot p)
    IndexExpr e i -> Fix $ Typed (getType $ unfix expr) (IndexExpr (pushNot e) i)
    _ -> expr

-- | Extracts the maximum level of history for each variable in the expression.
maximumHistory :: Ord v => TypedExpr v -> Map v Integer
maximumHistory exprs = foldl (\mp (n,_,_,lvl,_) -> Map.insertWith max n lvl mp) Map.empty (getVars exprs)


-- | Extracts all variables with their level of history from an expression.
getVars :: TypedExpr v -> [(v,VarUsage,[Integer],Integer,GTLType)]
getVars x = getTermVars getVars (unfix x)

-- | Extract all variables used in the given term.
getTermVars :: (r -> [(v,VarUsage,[Integer],Integer,GTLType)]) -> Typed (Term v) r -> [(v,VarUsage,[Integer],Integer,GTLType)]
getTermVars mu expr = case getValue expr of
  Var n lvl u -> [(n,u,[],lvl,getType expr)]
  Value x -> getValueVars mu x
  BinBoolExpr op l r -> (mu l)++(mu r)
  BinRelExpr op l r -> (mu l)++(mu r)
  BinIntExpr op l r -> (mu l)++(mu r)
  UnBoolExpr op p -> mu p
  IndexExpr e i -> fmap (\(v,u,idx,lvl,tp) -> (v,u,i:idx,lvl,tp)) (mu e)
  Automaton buchi -> concat [ concat $ fmap mu cond
                            | trans <- Map.elems (baTransitions buchi),
                              (cond,_) <- trans
                            ]
  BuiltIn _ args -> concat $ fmap mu args

-- | Get all variables used in a GTL value.
getValueVars :: (r -> [(v,VarUsage,[Integer],Integer,GTLType)]) -> GTLValue r -> [(v,VarUsage,[Integer],Integer,GTLType)]
getValueVars mu (GTLArrayVal xs) = concat (fmap mu xs)
getValueVars mu (GTLTupleVal xs) = concat (fmap mu xs)
getValueVars _ _ = []

-- | Change the type of the variables in an expression.
mapGTLVars :: (Ord v,Ord w) => (v -> w) -> TypedExpr v -> TypedExpr w
mapGTLVars f (Fix expr) = Fix $ Typed (getType expr) (mapTermVars f (mapGTLVars f) (getValue expr))


-- | Change the type of the variables used in a term
mapTermVars :: (Ord r1,Ord r2) => (v -> w) -> (r1 -> r2) -> Term v r1 -> Term w r2
mapTermVars f mu (Var name lvl u) = Var (f name) lvl u
mapTermVars f mu (Value x) = Value (mapValueVars mu x)
mapTermVars f mu (BinBoolExpr op l r) = BinBoolExpr op (mu l) (mu r)
mapTermVars f mu (BinRelExpr rel l r) = BinRelExpr rel (mu l) (mu r)
mapTermVars f mu (BinIntExpr op l r) = BinIntExpr op (mu l) (mu r)
mapTermVars f mu (UnBoolExpr op p) = UnBoolExpr op (mu p)
mapTermVars f mu (IndexExpr e i) = IndexExpr (mu e) i
mapTermVars f mu (Automaton buchi)
  = Automaton $ buchi { baTransitions = fmap (fmap (\(cond,trg) -> (fmap mu cond,trg))) (baTransitions buchi) }

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
            | Until TimeSpec
            | UntilOp TimeSpec
            deriving (Show,Eq,Ord)

-- | Unary boolean operators with the traditional semantics.
data UnBoolOp = Not
              | Always
              | Next TimeSpec
              | Finally TimeSpec
              | After TimeSpec
              deriving (Show,Eq,Ord)

instance Binary TimeSpec where
  put NoTime = put (0::Word8)
  put (TimeSteps n) = put (1::Word8) >> put n
  put (TimeUSecs n) = put (2::Word8) >> put n
  get = do
    i <- get
    case (i::Word8) of
      0 -> return NoTime
      1 -> do
        n <- get
        return $ TimeSteps n
      2 -> do
        n <- get
        return $ TimeUSecs n

instance Binary BoolOp where
  put And = put (0::Word8)
  put Or = put (1::Word8)
  put Implies = put (2::Word8)
  put (Until ts) = put (3::Word8) >> put ts
  put (UntilOp ts) = put (4::Word8) >> put ts
  get = do
    i <- get
    case (i::Word8) of
      0 -> return And
      1 -> return Or
      2 -> return Implies
      3 -> do
        ts <- get
        return $ Until ts
      4 -> do
        ts <- get
        return (UntilOp ts)

instance Binary UnBoolOp where
  put Not = put (0::Word8)
  put Always = put (1::Word8)
  put (Next ts) = put (2::Word8) >> put ts
  put (Finally ts) = put (3::Word8) >> put ts
  get = do
    i <- get
    case (i::Word8) of
      0 -> return Not
      1 -> return Always
      2 -> do
        ts <- get
        return $ Next ts
      3 -> do
        ts <- get
        return $ Finally ts

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
              | BinAssign -- ^ :=
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
toBoolOp :: BinOp -> TimeSpec -> Maybe BoolOp
toBoolOp GOpAnd NoTime = Just And
toBoolOp GOpOr NoTime = Just Or
toBoolOp GOpImplies NoTime = Just Implies
toBoolOp GOpUntil spec = Just (Until spec)
toBoolOp _ _ = Nothing


-- | Cast a binary operator into a relation. Returns `Nothing' if the cast fails.
toRelOp :: BinOp -> Maybe Relation
toRelOp GOpLessThan = Just BinLT
toRelOp GOpLessThanEqual = Just BinLTEq
toRelOp GOpGreaterThan = Just BinGT
toRelOp GOpGreaterThanEqual = Just BinGTEq
toRelOp GOpEqual = Just BinEq
toRelOp GOpAssign = Just BinAssign
toRelOp GOpNEqual = Just BinNEq
toRelOp _ = Nothing

-- | Cast a binary operator into an element operator. Returns `Nothing' if the cast fails.
toElemOp :: BinOp -> Maybe Bool
toElemOp GOpIn = Just True
toElemOp GOpNotIn = Just False
toElemOp _ = Nothing

-- | Binds variables to other variables from the past.
type ExistsBinding a = Map String (a,Integer,VarUsage)


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
  --BinAssign -> error "Can't negate assignments"

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
  --BinAssign -> error "Can't turn assignments"

-- | Represents the relations in which two expressions can stand
data ExprOrdering = EEQ -- ^ Both expressions define the same value space
                  | ENEQ -- ^ The expressions define non-overlapping value spaces
                  | EGT -- ^ The value space of the second expression is contained by the first
                  | ELT -- ^ The value space of the first expression is contained by the second
                  | EUNK -- ^ The expressions have overlapping value spaces or the relation isn't known
                  deriving (Show,Eq,Ord)

getClocks :: TypedExpr v -> [Integer]
getClocks (Fix e) = case getValue e of
  ClockReset c _ -> [c]
  ClockRef c -> [c]
  BinBoolExpr _ lhs rhs -> (getClocks lhs) ++ (getClocks rhs)
  UnBoolExpr _ r -> getClocks r
  Automaton aut -> automatonClocks id aut
  BuiltIn _ r -> concat $ fmap getClocks r
  _ -> []

automatonClocks :: (a -> [TypedExpr v]) -> BA a st -> [Integer]
automatonClocks f aut = concat [ concat $ fmap getClocks (f cond)
                               | trans <- Map.elems (baTransitions aut),
                                 (cond,_) <- trans
                               ]

-- | Convert a typed expression to a linear combination of variables.
toLinearExpr :: Ord v => TypedExpr v -> Map (Map (v,Integer,VarUsage) Integer) GTLConstant
toLinearExpr e = case getValue (unfix e) of
  Var v h u -> Map.singleton (Map.singleton (v,h,u) 1) one
  Value v -> let Just c = getConstant e
             in Map.singleton Map.empty c
  BinIntExpr op lhs rhs
    -> let p1 = toLinearExpr lhs
           p2 = toLinearExpr rhs
       in case op of
         OpPlus -> Map.unionWith (constantOp (+)) p1 p2
         OpMinus -> Map.unionWith (constantOp (-)) p1 p2
         OpMult -> Map.fromList [ (Map.unionWith (+) t1 t2,constantOp (*) c1 c2) | (t1,c1) <- Map.toList p1, (t2,c2) <- Map.toList p2 ]
  where
    one = Fix $ case unfix $ getType (unfix e) of
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
  = assert (getType (unfix e1) == getType (unfix e2)) $
    case unfix $ getType (unfix e1) of
      GTLInt -> lincomp
      GTLByte -> lincomp
      GTLFloat -> lincomp
      GTLBool -> case getValue (unfix e2) of
        UnBoolExpr Not e2' -> case compareExpr e1 e2' of
          EEQ -> ENEQ
          _ -> EUNK
        _ -> case getValue (unfix e1) of
          Var v1 h1 u1 -> case getValue (unfix e2) of
            Var v2 h2 u2 -> if v1==v2 && h1==h2 && u1 == u2
                            then EEQ
                            else EUNK
            _ -> EUNK
          Value c1 -> case getValue (unfix e2) of
            Value c2 -> if c1 == c2
                        then EEQ
                        else ENEQ
            _ -> EUNK
          IndexExpr ee1 i1 -> case getValue (unfix e2) of
            IndexExpr ee2 i2 -> case compareExpr ee1 ee2 of
              EEQ -> if i1==i2
                     then EEQ
                     else EUNK
              _ -> EUNK
            _ -> EUNK
          BinRelExpr op1 l1 r1 -> case getValue (unfix e2) of
            BinRelExpr op2 l2 r2 -> case op1 of
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
                    ENEQ -> if getType (unfix l1) == gtlBool
                            then ENEQ
                            else EUNK
                    _ -> EUNK
                  _ -> EUNK
                BinEq -> case compareExpr l1 l2 of
                  EEQ -> case compareExpr r1 r2 of
                    EEQ -> ENEQ
                    ENEQ -> EGT
                    _ -> EUNK
                  _ -> EUNK
                _ -> EUNK
              _ -> EUNK
            _ -> EUNK
          UnBoolExpr Not p -> case getValue (unfix e2) of
            UnBoolExpr Not p' -> case compareExpr p p' of
              ELT -> EGT
              EGT -> ELT
              r -> r
            _ -> case compareExpr p e2 of
              EEQ -> ENEQ
              _ -> EUNK
          ClockReset x y -> case getValue (unfix e2) of
            ClockReset x' y' -> if x==x'
                                then (if y==y' then EEQ else ENEQ)
                                else EUNK
            _ -> EUNK
          ClockRef x -> case getValue (unfix e2) of
            ClockRef y -> if x==y then EEQ else EUNK
            _ -> EUNK
      _ -> case getValue (unfix e1) of
        Value c1 -> case getValue (unfix e2) of
          Value c2 -> if c1 == c2
                      then EEQ
                      else ENEQ
          _ -> EUNK
        _ -> if getValue (unfix e1) == getValue (unfix e2)
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

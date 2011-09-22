{-# LANGUAGE DeriveTraversable,DeriveFoldable,DeriveFunctor,TypeSynonymInstances #-}
{-| Realizes the type-system of the GTL. Provides data structures for types
    and their values, as well as type-checking helper functions. -}
module Language.GTL.Types
       (GTLType'(..),
        GTLType,
        UnResolvedType'(..),
        UnResolvedType,
        resolveType,baseType,
        gtlInt,gtlByte,gtlBool,gtlFloat,gtlEnum,gtlArray,gtlTuple,
        GTLValue(..),
        ToGTL(..),
        resolveIndices,
        isInstanceOf,
        isSubtypeOf,
        showGTLValue) where

import Text.Read hiding (get)
import Data.Binary
import Data.List (genericLength,genericIndex)
import Data.Foldable (Foldable)
import Data.Traversable
import Control.Monad.Error ()
import Data.Fix
import Data.Map as Map
import Data.Set as Set
import Prelude hiding (mapM)

-- | All types that can occur in a GTL specification
data GTLType' r = GTLInt -- ^ A 64bit unsigned integer
                | GTLByte -- ^ A 8bit unsigned integer
                | GTLBool -- ^ Either true or false
                | GTLFloat -- ^ 64bit IEEE double
                | GTLEnum [String] -- ^ An enumeration type with a list of possible values
                | GTLArray Integer r -- ^ A fixed-size array of a given type
                | GTLTuple [r] -- ^ A tuple containing a number of types
                | GTLNamed String r -- ^ A type alias
                deriving (Eq,Ord,Show)

gtlInt,gtlByte,gtlBool,gtlFloat :: GTLType
gtlInt = Fix GTLInt
gtlByte = Fix GTLByte
gtlBool = Fix GTLBool
gtlFloat = Fix GTLFloat

gtlEnum :: [String] -> GTLType
gtlEnum constr = Fix $ GTLEnum constr

gtlArray :: Integer -> GTLType -> GTLType
gtlArray i tp = Fix $ GTLArray i tp

gtlTuple :: [GTLType] -> GTLType
gtlTuple tps = Fix $ GTLTuple tps

type GTLType = Fix GTLType'

newtype UnResolvedType' r = UnResolvedType' (Either String (GTLType' r))

type UnResolvedType = Fix UnResolvedType'

instance Show2 UnResolvedType' where
  show2 (UnResolvedType' tp) = show tp

resolveType :: Map String UnResolvedType -> UnResolvedType -> Either String GTLType
resolveType mp = resolveType' mp Set.empty

resolveType' :: Map String UnResolvedType -> Set String -> UnResolvedType -> Either String GTLType
resolveType' mp tried (Fix (UnResolvedType' tp))
  = case tp of
  Right GTLInt -> Right gtlInt
  Right GTLByte -> Right gtlByte
  Right GTLBool -> Right gtlBool
  Right GTLFloat -> Right gtlFloat
  Right (GTLEnum xs) -> Right $ gtlEnum xs
  Right (GTLArray sz t) -> do
    t' <- resolveType' mp tried t
    return $ gtlArray sz t'
  Right (GTLTuple xs) -> do
    xs' <- mapM (resolveType' mp tried) xs
    return $ gtlTuple xs'
  Left name -> if Set.member name tried
               then Left $ "Recursive types not allowed."
               else case Map.lookup name mp of
                 Nothing -> Left $ "Language.GTL.Types.resolveType: Unknown named type "++show name
                 Just rtp -> do
                   rtp' <- resolveType' mp (Set.insert name tried) rtp
                   return $ Fix $ GTLNamed name rtp'
    
baseType :: GTLType -> GTLType
baseType (Fix (GTLNamed _ tp)) = baseType tp
baseType x = x

-- | Represents the corresponding values to the 'GTLType'.
--   The parameter `r` is used to specify what values are
--   allowed inside arrays and tuples.
data GTLValue r = GTLIntVal Integer
                | GTLByteVal Word8
                | GTLBoolVal Bool
                | GTLFloatVal Float
                | GTLEnumVal String
                | GTLArrayVal [r]
                | GTLTupleVal [r]
                deriving (Eq,Ord,Foldable,Traversable)

-- | A helper class to convert haskell values to GTL values and types.
class ToGTL t where
  -- | Converts a haskell value to a GTL value
  toGTL :: t -> GTLValue a
  -- | Gets the GTL type of a haskell value
  gtlTypeOf :: t -> GTLType

instance ToGTL Integer where
  toGTL = GTLIntVal
  gtlTypeOf _ = Fix GTLInt

instance ToGTL Word8 where
  toGTL = GTLByteVal
  gtlTypeOf _ = Fix GTLByte

instance ToGTL Bool where
  toGTL = GTLBoolVal
  gtlTypeOf _ = Fix GTLBool

instance ToGTL Float where
  toGTL = GTLFloatVal
  gtlTypeOf _ = Fix GTLFloat

instance Functor GTLValue where
  fmap _ (GTLIntVal i) = GTLIntVal i
  fmap _ (GTLByteVal i) = GTLByteVal i
  fmap _ (GTLBoolVal i) = GTLBoolVal i
  fmap _ (GTLFloatVal i) = GTLFloatVal i
  fmap _ (GTLEnumVal i) = GTLEnumVal i
  fmap f (GTLArrayVal i) = GTLArrayVal (fmap f i)
  fmap f (GTLTupleVal i) = GTLTupleVal (fmap f i)

instance Eq2 GTLType' where
  eq2 = (==)

-- | Check if a type is a subtype of another type
--   `isSubtypeOf t1 t2` returns true iff t1 can be used where t2 is required
isSubtypeOf :: GTLType -> GTLType -> Bool
isSubtypeOf (Fix (GTLNamed n1 _)) (Fix (GTLNamed n2 _)) = n1==n2
isSubtypeOf tp (Fix (GTLNamed n tp2)) = isSubtypeOf tp tp2
isSubtypeOf tp1 tp2 = tp1 == tp2

-- | Given a list of indices, resolve the resulting type.
--   For example, if the type is a tuple of (int,float,int) and the indices are
--   [1], the result would be float.
--   Fails if the type isn't indexable.
resolveIndices :: GTLType -> [Integer] -> Either String GTLType
resolveIndices tp [] = return tp
resolveIndices (Fix (GTLArray sz tp)) (x:xs) = if x < sz
                                               then resolveIndices tp xs
                                               else Left $ "Index "++show x++" is out of array bounds ("++show sz++")"
resolveIndices (Fix (GTLTuple tps)) (x:xs) = if x < (genericLength tps)
                                             then resolveIndices (tps `genericIndex` x) xs
                                             else Left $ "Index "++show x++" is out of array bounds ("++show (genericLength tps)++")"
resolveIndices (Fix (GTLNamed _ tp)) idx = resolveIndices tp idx
resolveIndices tp _ = Left $ "Type "++show tp++" isn't indexable"

-- | Given a type, a function to extract type information from sub-values and a
--   value, this function checks if the value is in the domain of the given type.
isInstanceOf :: GTLType -> (r -> GTLType) -> GTLValue r -> Bool
isInstanceOf (Fix GTLInt) _ (GTLIntVal _) = True
isInstanceOf (Fix GTLByte) _ (GTLByteVal _) = True
isInstanceOf (Fix GTLBool) _ (GTLBoolVal _) = True
isInstanceOf (Fix GTLFloat) _ (GTLFloatVal _) = True
isInstanceOf (Fix (GTLEnum enums)) _ (GTLEnumVal x) = elem x enums
isInstanceOf (Fix (GTLArray sz tp)) f (GTLArrayVal els) = (and (fmap (tp==) (fmap f els))) && (sz == genericLength els)
isInstanceOf (Fix (GTLTuple [])) _ (GTLTupleVal []) = True
isInstanceOf (Fix (GTLTuple (tp:tps))) f (GTLTupleVal (v:vs)) = (tp==(f v)) && (isInstanceOf (Fix $ GTLTuple tps) f (GTLTupleVal vs))
isInstanceOf _ _ _ = False

intersperseS :: ShowS -> [ShowS] -> ShowS
intersperseS i [] = id
intersperseS i [x] = x
intersperseS i (x:xs) = x . i . (intersperseS i xs)

instance Show2 GTLType' where
  showsPrec2 _ GTLInt = showString "int"
  showsPrec2 _ GTLByte = showString "byte"
  showsPrec2 _ GTLBool = showString "bool"
  showsPrec2 _ GTLFloat = showString "float"
  showsPrec2 p (GTLEnum constr) = showParen (p > 5) $
                                  showString "enum { " .
                                  intersperseS (showString ", ") (fmap showString constr) .
                                  showString " }"
  showsPrec2 p (GTLArray sz tp) = showParen (p > 7) $
                                  showsPrec 7 tp .
                                  showChar '^' .
                                  shows sz
  showsPrec2 p (GTLTuple tps) = showChar '(' .
                                intersperseS (showString ", ") (fmap (showsPrec 0) tps) .
                                showChar ')'
  showsPrec2 p (GTLNamed name tp) = showString name

-- | Render a given GTL value by providing a recursive rendering function and a precedence value.
showGTLValue :: (r -> String) -> Int -> GTLValue r -> ShowS
showGTLValue _ p (GTLIntVal v) = showsPrec p v
showGTLValue _ p (GTLByteVal v) = showsPrec p v
showGTLValue _ p (GTLBoolVal v) = showsPrec p v
showGTLValue _ p (GTLFloatVal v) = showsPrec p v
showGTLValue _ p (GTLEnumVal v) = showString v
showGTLValue f p (GTLArrayVal vals) = showChar '(' .
                                      intersperseS (showString ", ") (fmap (showString.f) vals) .
                                      showChar ')'
showGTLValue f p (GTLTupleVal vals) = showChar '(' .
                                      intersperseS (showString ", ") (fmap (showString.f) vals) .
                                      showChar ')'

instance Show2 GTLValue where
  showsPrec2 = showGTLValue show

instance Show a => Show (GTLValue a) where
  showsPrec = showsPrec2

instance Eq2 GTLValue where
  eq2 = (==)

instance Ord2 GTLValue where
  compare2 = compare

readIntersperse :: ReadPrec b -> ReadPrec a -> ReadPrec [a]
readIntersperse i f = (do
                          first <- f
                          rest <- readIntersperse'
                          return (first:rest)
                      ) <++ (return [])
  where
    readIntersperse' = (do
                           i
                           x <- f
                           xs <- readIntersperse'
                           return (x:xs)
                       ) <++ (return [])

lexPunc :: String -> ReadPrec ()
lexPunc c = do
  x <- lexP
  case x of
    Punc str -> if str==c
                then return ()
                else pfail
    _ -> pfail

instance Read GTLType where
  readPrec = do
    tp <- readSingle
    readPow tp
    where
      readPow tp = (do
        tok <- lexP
        case tok of
          Symbol "^" -> do
            n <- lexP
            case n of
              Int n' -> readPow (Fix $ GTLArray n' tp)
              _ -> pfail
          _ -> pfail) <++ (return tp)
      readSingle = do
        tok <- lexP
        case tok of
          Ident "int" -> return $ Fix GTLInt
          Ident "byte" -> return $ Fix GTLByte
          Ident "float" -> return $ Fix GTLFloat
          Ident "enum" -> do
            op <- lexP
            case op of
              Punc "{" -> do
                lits <- readIntersperse (lexPunc ",")
                        (do
                            c <- lexP
                            case c of
                              Ident l -> return l
                              _ -> pfail)
                cl <- lexP
                case cl of
                  Punc "}" -> return (Fix $ GTLEnum lits)
                  _ -> pfail
          Punc "(" -> do
            tps <- readIntersperse (lexPunc ",") readPrec
            cl <- lexP
            case cl of
              Punc ")" -> return (Fix $ GTLTuple tps)
              _ -> pfail
          _ -> pfail

instance Binary2 GTLType' where
  put2 GTLInt = put (0::Word8)
  put2 GTLByte = put (1::Word8)
  put2 GTLBool = put (2::Word8)
  put2 GTLFloat = put (3::Word8)
  put2 (GTLEnum xs) = put (4::Word8) >> put xs
  put2 (GTLArray sz tp) = put (5::Word8) >> put sz >> put tp
  put2 (GTLTuple tps) = put (6::Word8) >> put tps
  get2 = do
    i <- get
    case (i::Word8) of
      0 -> return GTLInt
      1 -> return GTLByte
      2 -> return GTLBool
      3 -> return GTLFloat
      4 -> do
        xs <- get
        return (GTLEnum xs)
      5 -> do
        sz <- get
        tp <- get
        return (GTLArray sz tp)
      6 -> do
        tps <- get
        return (GTLTuple tps)

instance Ord2 GTLType' where
  compare2 = compare

instance Binary r => Binary (GTLValue r) where
  put (GTLIntVal x) = put (0::Word8) >> put x
  put (GTLByteVal x) = put (1::Word8) >> put x
  put (GTLBoolVal x) = put (2::Word8) >> put x
  put (GTLFloatVal x) = put (3::Word8) >> put x
  put (GTLEnumVal x) = put (4::Word8) >> put x
  put (GTLArrayVal x) = put (5::Word8) >> put x
  put (GTLTupleVal x) = put (6::Word8) >> put x
  get = do
    i <- get
    case (i::Word8) of
      0 -> fmap GTLIntVal get
      1 -> fmap GTLByteVal get
      2 -> fmap GTLBoolVal get
      3 -> fmap GTLFloatVal get
      4 -> fmap GTLEnumVal get
      5 -> fmap GTLArrayVal get
      6 -> fmap GTLTupleVal get


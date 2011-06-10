{-# LANGUAGE DeriveTraversable,DeriveFoldable #-}
module Language.GTL.Types where

import Text.Read hiding (get)
import Data.Binary
import Data.List (genericLength,genericIndex)
import Data.Foldable (Foldable)
import Data.Traversable

data GTLType = GTLInt
             | GTLByte
             | GTLBool
             | GTLFloat
             | GTLEnum [String]
             | GTLArray Integer GTLType
             | GTLTuple [GTLType]
             deriving (Eq,Ord)

data GTLValue r = GTLIntVal Integer
                | GTLByteVal Word8
                | GTLBoolVal Bool
                | GTLFloatVal Float
                | GTLEnumVal String
                | GTLArrayVal [r]
                | GTLTupleVal [r]
                deriving (Eq,Ord,Foldable,Traversable)

class ToGTL t where
  toGTL :: t -> GTLValue a
  gtlTypeOf :: t -> GTLType

instance ToGTL Integer where
  toGTL = GTLIntVal
  gtlTypeOf _ = GTLInt

instance ToGTL Word8 where
  toGTL = GTLByteVal
  gtlTypeOf _ = GTLByte

instance ToGTL Bool where
  toGTL = GTLBoolVal
  gtlTypeOf _ = GTLBool

instance ToGTL Float where
  toGTL = GTLFloatVal
  gtlTypeOf _ = GTLFloat

instance Functor GTLValue where
  fmap _ (GTLIntVal i) = GTLIntVal i
  fmap _ (GTLByteVal i) = GTLByteVal i
  fmap _ (GTLBoolVal i) = GTLBoolVal i
  fmap _ (GTLFloatVal i) = GTLFloatVal i
  fmap _ (GTLEnumVal i) = GTLEnumVal i
  fmap f (GTLArrayVal i) = GTLArrayVal (fmap f i)
  fmap f (GTLTupleVal i) = GTLTupleVal (fmap f i)

resolveIndices :: GTLType -> [Integer] -> Either String GTLType
resolveIndices tp [] = return tp
resolveIndices (GTLArray sz tp) (x:xs) = if x < sz
                                         then resolveIndices tp xs
                                         else Left $ "Index "++show x++" is out of array bounds ("++show sz++")"
resolveIndices (GTLTuple tps) (x:xs) = if x < (genericLength tps)
                                       then resolveIndices (tps `genericIndex` x) xs
                                       else Left $ "Index "++show x++" is out of array bounds ("++show (genericLength tps)++")"
resolveIndices tp _ = Left $ "Type "++show tp++" isn't indexable"

isInstanceOf :: GTLType -> (r -> GTLType) -> GTLValue r -> Bool
isInstanceOf GTLInt _ (GTLIntVal _) = True
isInstanceOf GTLByte _ (GTLByteVal _) = True
isInstanceOf GTLBool _ (GTLBoolVal _) = True
isInstanceOf GTLFloat _ (GTLFloatVal _) = True
isInstanceOf (GTLEnum enums) _ (GTLEnumVal x) = elem x enums
isInstanceOf (GTLArray sz tp) f (GTLArrayVal els) = (and (fmap (tp==) (fmap f els))) && (sz == genericLength els)
isInstanceOf (GTLTuple []) _ (GTLTupleVal []) = True
isInstanceOf (GTLTuple (tp:tps)) f (GTLTupleVal (v:vs)) = (tp==(f v)) && (isInstanceOf (GTLTuple tps) f (GTLTupleVal vs))
isInstanceOf _ _ _ = False

intersperseS :: ShowS -> [ShowS] -> ShowS
intersperseS i [] = id
intersperseS i [x] = x
intersperseS i (x:xs) = x . i . (intersperseS i xs)

instance Show GTLType where
  showsPrec _ GTLInt = showString "int"
  showsPrec _ GTLByte = showString "byte"
  showsPrec _ GTLBool = showString "bool"
  showsPrec _ GTLFloat = showString "float"
  showsPrec p (GTLEnum constr) = showParen (p > 5) $
                                 showString "enum { " .
                                 intersperseS (showString ", ") (fmap showString constr) .
                                 showString " }"
  showsPrec p (GTLArray sz tp) = showParen (p > 7) $
                                 showsPrec 7 tp .
                                 showChar '^' .
                                 shows sz
  showsPrec p (GTLTuple tps) = showChar '(' .
                               intersperseS (showString ", ") (fmap (showsPrec 0) tps) .
                               showChar ')'

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

instance Show r => Show (GTLValue r) where
  showsPrec = showGTLValue show

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
              Int n' -> readPow (GTLArray n' tp)
              _ -> pfail
          _ -> pfail) <++ (return tp)
      readSingle = do
        tok <- lexP
        case tok of
          Ident "int" -> return GTLInt
          Ident "byte" -> return GTLByte
          Ident "float" -> return GTLFloat
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
                  Punc "}" -> return (GTLEnum lits)
                  _ -> pfail
          Punc "(" -> do
            tps <- readIntersperse (lexPunc ",") readPrec
            cl <- lexP
            case cl of
              Punc ")" -> return (GTLTuple tps)
              _ -> pfail
          _ -> pfail

instance Binary GTLType where
  put GTLInt = put (0::Word8)
  put GTLByte = put (1::Word8)
  put GTLBool = put (2::Word8)
  put GTLFloat = put (3::Word8)
  put (GTLEnum xs) = put (4::Word8) >> put xs
  put (GTLArray sz tp) = put (5::Word8) >> put sz >> put tp
  put (GTLTuple tps) = put (6::Word8) >> put tps
  get = do
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


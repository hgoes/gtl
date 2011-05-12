module Language.GTL.Types where

import Text.Read

data GTLType = GTLInt
             | GTLByte
             | GTLFloat
             | GTLEnum [String]
             | GTLArray Integer GTLType
             | GTLTuple [GTLType]
             deriving (Eq,Ord)

intersperseS :: ShowS -> [ShowS] -> ShowS
intersperseS i [] = id
intersperseS i [x] = x
intersperseS i (x:xs) = x . i . (intersperseS i xs)

instance Show GTLType where
  showsPrec _ GTLInt = showString "int"
  showsPrec _ GTLByte = showString "byte"
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
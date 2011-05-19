module Language.GTL.Parser.Token where

data Token = Identifier String
           | ConstEnum String
           | Key KeyWord
           | Bracket BracketType Bool
           | Dot
           | Semicolon
           | Colon
           | Comma
           | ConstString String
           | ConstInt Integer
           | Unary UnOp
           | Binary BinOp
           deriving Show

data KeyWord = KeyAll
             | KeyBool
             | KeyByte
             | KeyConnect
             | KeyContract
             | KeyEnum
             | KeyModel
             | KeyOutput
             | KeyFalse
             | KeyFloat
             | KeyInit
             | KeyInput
             | KeyInt
             | KeyInstance
             | KeyVerify
             | KeyExists
             | KeyFinal
             | KeyAutomaton
             | KeyState
             | KeyTransition
             | KeyTrue
             | KeyUntil
             deriving Show

data BracketType = Parentheses
                 | Square
                 | Curly
                 deriving Show

data UnOp = GOpAlways
          | GOpNext
          | GOpNot
          | GOpFinally (Maybe Integer)
          deriving (Show,Eq,Ord)

data BinOp = GOpAnd
           | GOpOr
           | GOpImplies
           | GOpIn
           | GOpNotIn
           | GOpUntil
           | GOpLessThan
           | GOpLessThanEqual
           | GOpGreaterThan
           | GOpGreaterThanEqual
           | GOpEqual
           | GOpNEqual
           | GOpPlus
           | GOpMinus
           | GOpMult
           | GOpDiv
           | GOpPow
           deriving (Show,Eq,Ord)
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
           | CtxIn
           | CtxOut
           | EOF
           deriving (Show,Eq,Ord)

data KeyWord = KeyAll
             | KeyBool
             | KeyByte
             | KeyConnect
             | KeyContract
             | KeyCycleTime
             | KeyEnum
             | KeyGuaranteed
             | KeyLocal
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
             | KeyType
             | KeyUntil
             deriving (Show,Eq,Ord)

data BracketType = Parentheses
                 | Square
                 | Curly
                 deriving (Show,Eq,Ord)

data UnOp = GOpAlways
          | GOpNext
          | GOpNot
          | GOpFinally
          | GOpAfter
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
           | GOpAssign
           | GOpNEqual
           | GOpPlus
           | GOpMinus
           | GOpMult
           | GOpDiv
           | GOpPow
           deriving (Show,Eq,Ord)
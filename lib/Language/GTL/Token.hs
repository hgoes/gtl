module Language.GTL.Token where

data Token = Identifier String
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
             | KeyConnect
             | KeyContract
             | KeyModel
             | KeyOutput
             | KeyInit
             | KeyInput
             | KeyVerify
             | KeyExists
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
           deriving (Show,Eq,Ord)
module Language.GTL.Token where

data Token = Identifier String
           | Key KeyWord
           | Bracket BracketType Bool
           | Dot
           | Semicolon
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
             | KeyInit
             | KeyVerify
             deriving Show

data BracketType = Parentheses
                 | Square
                 | Curly
                 deriving Show

data UnOp = GOpAlways
          | GOpNext Integer
          | GOpNot
          deriving (Show,Eq,Ord)

data BinOp = GOpAnd
           | GOpOr
           | GOpFollows
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
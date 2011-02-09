module Language.GTL.Token where

data Token = Identifier String
           | Key KeyWord
           | Bracket BracketType Bool
           | Dot
           | Semicolon
           | Comma
           | ConstString String
           | ConstInt Integer
           | LessThan
           | GreaterThan
           | Equals
           deriving Show

data KeyWord = KeyAll
             | KeyAlways
             | KeyAnd
             | KeyConnect
             | KeyContract
             | KeyFollows
             | KeyModel
             | KeyNext
             | KeyNot
             | KeyOr
             | KeyIn
             | KeyInit
             | KeyVerify
             deriving Show

data BracketType = Parentheses
                 | Square
                 | Curly
                 deriving Show
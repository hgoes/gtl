module Language.GTL.Syntax where

data Declaration = Model ModelDecl
                 | Connect ConnectDecl
                 deriving Show

data ModelDecl = ModelDecl
                 { modelName :: String
                 , modelType :: String
                 , modelArgs :: [String]
                 , modelContract :: [Formula]
                 } deriving Show

data ConnectDecl = ConnectDecl
                   { connectFromModel :: String
                   , connectFromVariable :: String
                   , connectToModel :: String
                   , connectToVariable :: String
                   } deriving Show

data Lit = Constant Integer
         | Variable String
         deriving Show

data Formula = BinLT Lit Lit
             | BinGT Lit Lit
             | BinEQ Lit Lit
             | Not Formula
             | And Formula Formula
             | Or Formula Formula
             | Follows Formula Formula
             | Always Formula
             | Next Formula
             deriving Show
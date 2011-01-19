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
         deriving (Show,Eq,Ord)

data Formula = BinRel Relation Lit Lit
             | BinOp Operator Formula Formula
             | Not Formula
             | Always Formula
             | Next Formula
             deriving (Show,Eq,Ord)

data Operator = And
              | Or
              | Follows
              deriving (Show,Eq,Ord)

data Relation = BinLT
              | BinLTEq
              | BinGT
              | BinGTEq
              | BinEq
              | BinNEq
              deriving (Show,Eq,Ord)

relNot :: Relation -> Relation
relNot rel = case rel of
  BinLT -> BinGTEq
  BinLTEq -> BinGT
  BinGT -> BinLTEq
  BinGTEq -> BinLT
  BinEq -> BinNEq
  BinNEq -> BinEq

pushNot :: Formula -> Formula
pushNot (Not x) = pushNot' x
pushNot (BinOp op x y) = BinOp op (pushNot x) (pushNot y)
pushNot (Always x) = Always (pushNot x)
pushNot (Next x) = Next (pushNot x)
pushNot (BinRel rel x y) = BinRel rel x y

pushNot' :: Formula -> Formula
pushNot' (BinRel rel x y) = BinRel (case rel of
                                       BinLT -> BinGTEq
                                       BinLTEq -> BinGT
                                       BinGT -> BinLTEq
                                       BinGTEq -> BinLT
                                       BinEq -> BinNEq
                                       BinNEq -> BinEq) x y
pushNot' (Not x) = x
pushNot' (BinOp op x y) = case op of
  And -> BinOp Or (pushNot' x) (pushNot' y)
  Or -> BinOp And (pushNot' x) (pushNot' y)
  Follows -> BinOp And (pushNot x) (pushNot' y)
pushNot' (Always x) = error "always operator must not be negated"
pushNot' (Next x) = Next (pushNot' x)

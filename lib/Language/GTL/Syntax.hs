{-# LANGUAGE GADTs #-}
module Language.GTL.Syntax where

data Declaration = Model ModelDecl
                 | Connect ConnectDecl
                 | Verify VerifyDecl
                 deriving Show

data ModelDecl = ModelDecl
                 { modelName :: String
                 , modelType :: String
                 , modelArgs :: [String]
                 , modelContract :: [Formula]
                 , modelInits :: [(String,InitExpr)]
                 } deriving Show

data ConnectDecl = ConnectDecl
                   { connectFromModel :: String
                   , connectFromVariable :: String
                   , connectToModel :: String
                   , connectToVariable :: String
                   } deriving Show

data VerifyDecl = VerifyDecl
                  { verifyFormulas :: [Formula]
                  } deriving Show

type Formula = Expr Bool

data Expr a where
  ExprVar :: Maybe String -> String -> Expr Int
  ExprConst :: Integer -> Expr Int
  ExprBinInt :: IntOp -> Expr Int -> Expr Int -> Expr Int
  ExprBinBool :: BoolOp -> Expr Bool -> Expr Bool -> Expr Bool
  ExprRel :: Relation -> Expr Int -> Expr Int -> Expr Bool
  ExprElem :: Maybe String -> String -> [Integer] -> Bool -> Expr Bool
  ExprNot :: Expr Bool -> Expr Bool
  ExprAlways :: Expr Bool -> Expr Bool
  ExprNext :: Expr Bool -> Expr Bool

instance Eq (Expr a) where
  (ExprVar q1 n1) == (ExprVar q2 n2) = q1 == q2 && n1 == n2
  (ExprConst i1) == (ExprConst i2) = i1 == i2
  (ExprBinInt op1 l1 r1) == (ExprBinInt op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprBinBool op1 l1 r1) == (ExprBinBool op2 l2 r2) = op1==op2 && l1==l2 && r1==r2
  (ExprRel rel1 l1 r1) == (ExprRel rel2 l2 r2) = rel1==rel2 && l1==l2 && r1==r2
  (ExprElem q1 n1 s1 p1) == (ExprElem q2 n2 s2 p2) = q1==q2 && n1==n2 && s1==s2 && p1==p2
  (ExprNot e1) == (ExprNot e2) = e1==e2
  (ExprAlways e1) == (ExprAlways e2) = e1==e2
  (ExprNext e1) == (ExprNext e2) = e1==e2
  _ == _ = False

instance Ord (Expr a) where
  compare (ExprVar q1 n1) (ExprVar q2 n2) = case compare q1 q2 of
    EQ -> compare n1 n2
    r -> r
  compare (ExprVar _ _) _ = LT
  compare (ExprConst i1) (ExprConst i2) = compare i1 i2
  compare (ExprConst _) _ = LT
  compare (ExprBinInt op1 l1 r1) (ExprBinInt op2 l2 r2) = case compare op1 op2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprBinInt _ _ _) _ = LT
  compare (ExprBinBool op1 l1 r1) (ExprBinBool op2 l2 r2) = case compare op1 op2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprBinBool _ _ _) _ = LT
  compare (ExprRel rel1 l1 r1) (ExprRel rel2 l2 r2) = case compare rel1 rel2 of
    EQ -> case compare l1 l2 of
      EQ -> compare r1 r2
      r -> r
    r -> r
  compare (ExprRel _ _ _) _ = LT
  compare (ExprElem q1 n1 s1 p1) (ExprElem q2 n2 s2 p2) = case compare (ExprVar q1 n1) (ExprVar q2 n2) of
    EQ -> case compare s1 s2 of
      EQ -> compare p1 p2
      r -> r
    r -> r
  compare (ExprElem _ _ _ _) _ = LT
  compare (ExprNot e1) (ExprNot e2) = compare e1 e2
  compare (ExprNot _) _ = LT
  compare (ExprAlways e1) (ExprAlways e2) = compare e1 e2
  compare (ExprAlways _) _ = LT
  compare (ExprNext e1) (ExprNext e2) = compare e1 e2
  compare (ExprNext _) _ = LT

instance Show (Expr a) where
  show (ExprVar q name) = case q of
    Nothing -> name
    Just rq -> rq ++ "." ++ name
  show (ExprConst i) = show i
  show (ExprBinInt op lhs rhs) = "(" ++ show lhs ++ ")" ++
                                 (case op of
                                     OpPlus -> "+"
                                     OpMinus -> "-"
                                     OpMult -> "*"
                                     OpDiv -> "/") ++
                                 "(" ++ show rhs ++ ")"
  show (ExprBinBool op lhs rhs) = "(" ++ show lhs ++ ") " ++
                                  (case op of
                                      And -> "and"
                                      Or -> "or"
                                      Follows -> "follows") ++
                                  " ("++show rhs++")"
  show (ExprRel rel lhs rhs) = "(" ++ show lhs ++ ") " ++
                               (case rel of
                                   BinLT -> "<"
                                   BinLTEq -> "<="
                                   BinGT -> ">"
                                   BinGTEq -> ">="
                                   BinEq -> "="
                                   BinNEq -> "!=") ++
                               " (" ++ show rhs ++ ")"
  show (ExprElem q name ints pos) = show (ExprVar q name) ++
                                    (if pos then " in "
                                     else " not in ") ++
                                    show ints
  show (ExprNot e) = "not ("++show e++")"
  show (ExprAlways e) = "always ("++show e++")"
  show (ExprNext e) = "next ("++show e++")"
                                                               
  
data BoolOp = And | Or | Follows deriving (Show,Eq,Ord)

data IntOp = OpPlus | OpMinus | OpMult | OpDiv deriving (Show,Eq,Ord)

data Relation = BinLT
              | BinLTEq
              | BinGT
              | BinGTEq
              | BinEq
              | BinNEq
              deriving (Show,Eq,Ord)

data InitExpr = InitAll
              | InitOne Integer
              deriving (Show,Eq)

relNot :: Relation -> Relation
relNot rel = case rel of
  BinLT -> BinGTEq
  BinLTEq -> BinGT
  BinGT -> BinLTEq
  BinGTEq -> BinLT
  BinEq -> BinNEq
  BinNEq -> BinEq

relTurn :: Relation -> Relation
relTurn rel = case rel of
  BinLT -> BinGT
  BinLTEq -> BinGTEq
  BinGT -> BinLT
  BinGTEq -> BinLTEq
  BinEq -> BinEq
  BinNEq -> BinNEq

pushNot :: Formula -> Formula
pushNot (ExprNot x) = pushNot' x
pushNot (ExprBinBool op x y) = ExprBinBool op (pushNot x) (pushNot y)
pushNot (ExprAlways x) = ExprAlways (pushNot x)
pushNot (ExprNext x) = ExprNext (pushNot x)
pushNot expr = expr

pushNot' :: Formula -> Formula
pushNot' (ExprRel rel x y)
  = ExprRel (case rel of
                BinLT -> BinGTEq
                BinLTEq -> BinGT
                BinGT -> BinLTEq
                BinGTEq -> BinLT
                BinEq -> BinNEq
                BinNEq -> BinEq) x y
pushNot' (ExprNot x) = x
pushNot' (ExprBinBool op x y) = case op of
  And -> ExprBinBool Or (pushNot' x) (pushNot' y)
  Or -> ExprBinBool And (pushNot' x) (pushNot' y)
  Follows -> ExprBinBool And (pushNot x) (pushNot' y)
pushNot' (ExprAlways x) = error "always operator must not be negated"
pushNot' (ExprNext x) = ExprNext (pushNot' x)
pushNot' (ExprElem p n lst neg) = ExprElem p n lst (not neg)

getVars :: Expr a -> [(Maybe String,String)]
getVars (ExprVar q n) = [(q,n)]
getVars (ExprConst _) = []
getVars (ExprBinInt _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprBinBool _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprRel _ lhs rhs) = getVars lhs ++ getVars rhs
getVars (ExprElem q n _ _) = [(q,n)]
getVars (ExprNot e) = getVars e
getVars (ExprAlways e) = getVars e
getVars (ExprNext e) = getVars e

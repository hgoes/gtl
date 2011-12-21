{
{-# LANGUAGE BangPatterns #-}  
{-| The GTL Lexer  
 -}
module Language.GTL.Parser.Lexer (lexGTL) where

import Language.GTL.Parser.Token
}

%wrapper "monad"

$letter = [a-zA-Z\_]
$digit10 = [0-9]

tokens:-
  $white+                        { skip }
  "//".*                         { skip }
  "/*"                           { nestedComment }
  after                          { un GOpAfter }
  all                            { key KeyAll }
  always                         { un GOpAlways }
  and                            { bin GOpAnd }
  automaton                      { key KeyAutomaton }
  bool                           { key KeyBool }
  byte                           { key KeyByte }
  connect                        { key KeyConnect }
  contract                       { key KeyContract }
  cycle\-time                    { key KeyCycleTime }
  enum                           { key KeyEnum }
  false                          { key KeyFalse }
  float                          { key KeyFloat }
  implies                        { bin GOpImplies }
  init                           { key KeyInit }
  int                            { key KeyInt }
  instance                       { key KeyInstance }
  local                          { key KeyLocal }
  model                          { key KeyModel }
  finally                        { un GOpFinally }
  next                           { un GOpNext }
  exists                         { key KeyExists }
  final                          { key KeyFinal }
  not                              { un GOpNot }
  or                             { bin GOpOr }
  output                         { key KeyOutput }
  input				 { key KeyInput }
  in                             { bin GOpIn }
  state                          { key KeyState }
  transition                     { key KeyTransition }
  true                           { key KeyTrue }
  type                           { key KeyType }
  until                          { key KeyUntil }
  verify                         { key KeyVerify }
  "("                            { tok $ Bracket Parentheses False }
  ")"                            { tok $ Bracket Parentheses True }
  "["                            { tok $ Bracket Square False }
  "]"                            { tok $ Bracket Square True }
  "{"                            { tok $ Bracket Curly False }
  "}"                            { tok $ Bracket Curly True }
  ";"                            { tok Semicolon }
  ":="                           { bin GOpAssign }
  ":"                            { tok Colon }
  "."                            { tok Dot }
  ","                            { tok Comma }
  "<="                           { bin GOpLessThanEqual }
  "<"                            { bin GOpLessThan }
  "=>"                           { bin GOpImplies }
  ">="                           { bin GOpGreaterThanEqual }
  ">"                            { bin GOpGreaterThan }
  "="                            { bin GOpEqual }
  "!="                           { bin GOpNEqual }
  "!"                            { un GOpNot }
  "+"				 { bin GOpPlus }
  "-"                            { bin GOpMinus }
  "*"                            { bin GOpMult }
  "/"                            { bin GOpDiv }
  "^"                            { bin GOpPow }
  "#in"                          { tok CtxIn }
  "#out"                         { tok CtxOut }
  "'" $letter ($letter | $digit10)*              { withStr $ \s -> ConstEnum (tail s) }
  \" ([\x00-\xff] # [\\\"] | \\ [\x00-\xff])* \" { withStr $ \s -> ConstString (read s) }
  $letter ($letter | $digit10)*                  { withStr Identifier }
  $digit10+                                      { withStr $ \s -> ConstInt (read s) }

{

type Action r = AlexAction (Alex r)

nestedComment :: Action Token
nestedComment _ _ = do  
  input <- alexGetInput
  go 1 input
  where go 0 input = do
          alexSetInput input
          alexMonadScan
        go n input = do
          case alexGetChar input of
            Nothing -> err input
            Just (c,input) -> do
              case c of
                '*' -> case alexGetChar input of
                  Nothing -> err input
                  Just ('/',input) -> go (n-1) input
                  Just (c,input) -> go n input
                '/' -> case alexGetChar input of
                  Nothing -> err input
                  Just ('*',input) -> go (n+1) input
                  Just (c,input) -> go n input
                _ -> go n input
        err input = do
          alexSetInput input
          lexError "error in nested comment"
          
lexError s = do
  (p,c,input) <- alexGetInput
  alexError $ showPosn p ++ ": "++s++(if not (null input)
                                      then " before "++ show (head input)
                                      else " at end of file")

-- | Convert GTL code lazily into a list of tokens.
lexGTL :: String -> [Token]
lexGTL str = case (runAlex str $ do
                      let loop = do
                            tok <- alexMonadScan
                            if tok==EOF
                              then return []
                              else (do
                                       outp <- loop
                                       return (tok:outp))
                      loop) of
               Left msg -> error msg
               Right res -> res
  
key :: KeyWord -> Action Token
key w _ _ = return $ Key w

un :: UnOp -> Action Token
un o _ _ = return $ Unary o

bin :: BinOp -> Action Token
bin o _ _ = return $ Binary o

tok :: Token -> Action Token
tok t _ _ = return t

withStr :: (String -> Token) -> Action Token
withStr f (_,_,input) i = return $ f (take i input)

--alexEOF :: AlexAction Token
alexEOF = return EOF

showPosn (AlexPn _ line col) = show line ++ ':': show col

}
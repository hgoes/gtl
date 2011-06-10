{
{-| The GTL Lexer  
 -}
module Language.GTL.Parser.Lexer (lexGTL) where

import Language.GTL.Parser.Token
}

%wrapper "basic"

$letter = [a-zA-Z\_]
$digit10 = [0-9]

tokens:-
  $white+                        ;
  "//".*                         ;
  all                            { key KeyAll }
  always                         { un GOpAlways }
  and                            { bin GOpAnd }
  automaton                      { key KeyAutomaton }
  bool                           { key KeyBool }
  byte                           { key KeyByte }
  connect                        { key KeyConnect }
  contract                       { key KeyContract }
  enum                           { key KeyEnum }
  false                          { key KeyFalse }
  float                          { key KeyFloat }
  implies                        { bin GOpImplies }
  init                           { key KeyInit }
  int                            { key KeyInt }
  instance                       { key KeyInstance }
  model                          { key KeyModel }
  finally $digit10*              { \s -> Unary (GOpFinally (case drop 7 s of
                                                            [] -> Nothing
                                                            r -> Just (read r))) }
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
  until                          { key KeyUntil }
  verify                         { key KeyVerify }
  "("                            { const $ Bracket Parentheses False }
  ")"                            { const $ Bracket Parentheses True }
  "["                            { const $ Bracket Square False }
  "]"                            { const $ Bracket Square True }
  "{"                            { const $ Bracket Curly False }
  "}"                            { const $ Bracket Curly True }
  ";"                            { const Semicolon }
  ":"                            { const Colon }
  "."                            { const Dot }
  ","                            { const Comma }
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
  "'" $letter ($letter | $digit10)* { \s -> ConstEnum (tail s) }
  \" ([\x00-\xff] # [\\\"] | \\ [\x00-\xff])* \" { \s -> ConstString (read s) }
  $letter ($letter | $digit10)*  { Identifier }
  $digit10+                      { \s -> ConstInt (read s) }

{
-- | Convert GTL code lazily into a list of tokens.
lexGTL :: String -> [Token]
lexGTL = alexScanTokens
  
key :: KeyWord -> String -> Token
key w _ = Key w

un :: UnOp -> String -> Token
un o _ = Unary o

bin :: BinOp -> String -> Token
bin o _ = Binary o

}
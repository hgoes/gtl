{
module Language.GTL.Lexer where

import Language.GTL.Token
}

%wrapper "basic"

$letter = [a-zA-Z\_]
$digit10 = [0-9]

tokens:-
  $white+                        ;
  "//" .* \n                     ;
  all                            { key KeyAll }
  always                         { un GOpAlways }
  and                            { bin GOpAnd }
  connect                        { key KeyConnect }
  contract                       { key KeyContract }
  follows                        { bin GOpFollows }
  init                           { key KeyInit }
  model                          { key KeyModel }
  next $digit10*                 { \s -> Unary (GOpNext (case drop 4 s of
                                                            [] -> 1
                                                            r -> read r)) }
  exists                         { key KeyExists }
  not                              { un GOpNot }
  or                             { bin GOpOr }
  in                             { bin GOpIn }
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
  "=>"                           { bin GOpFollows }
  ">="                           { bin GOpGreaterThanEqual }
  ">"                            { bin GOpGreaterThan }
  "="                            { bin GOpEqual }
  "!="                           { bin GOpNEqual }
  "!"                            { un GOpNot }
  "+"				 { bin GOpPlus }
  "-"                            { bin GOpMinus }
  "*"                            { bin GOpMult }
  "/"                            { bin GOpDiv }
  \" ([\x00-\xff] # [\\\"] | \\ [\x00-\xff])* \" { \s -> ConstString (read s) }
  $letter ($letter | $digit10)*  { Identifier }
  $digit10+                      { \s -> ConstInt (read s) }

{
key :: KeyWord -> String -> Token
key w _ = Key w

un :: UnOp -> String -> Token
un o _ = Unary o

bin :: BinOp -> String -> Token
bin o _ = Binary o
  
}
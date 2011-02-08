{
module Language.GTL.Lexer where

import Language.GTL.Token
}

%wrapper "basic"

$letter = [a-zA-Z\_]
$digit10 = [0-9]

tokens:-
  $white+                        ;
  all                            { key KeyAll }
  always                         { key KeyAlways }
  and                            { key KeyAnd }
  connect                        { key KeyConnect }
  follows                        { key KeyFollows }
  init                           { key KeyInit }
  model                          { key KeyModel }
  next                           { key KeyNext }
  not                              { key KeyNot }
  or                             { key KeyOr }
  in                             { key KeyIn }
  verify                         { key KeyVerify }
  "("                            { const $ Bracket Parentheses False }
  ")"                            { const $ Bracket Parentheses True }
  "["                            { const $ Bracket Square False }
  "]"                            { const $ Bracket Square True }
  "{"                            { const $ Bracket Curly False }
  "}"                            { const $ Bracket Curly True }
  ";"                            { const Semicolon }
  "."                            { const Dot }
  ","                            { const Comma }
  "<"                            { const LessThan }
  "=>"                           { key KeyFollows }
  ">"                            { const GreaterThan }
  "="                            { const Equals }
  "!"                            { key KeyNot }
  \" ([\x00-\xff] # [\\\"] | \\ [\x00-\xff])* \" { \s -> ConstString (read s) }
  $letter ($letter | $digit10)*  { Identifier }
  $digit10+                      { \s -> ConstInt (read s) }

{
key :: KeyWord -> String -> Token
key w _ = Key w
  
}
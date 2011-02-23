{
module Language.GTL.Parser where

import Language.GTL.Token
import Language.GTL.Syntax

import Data.Maybe (mapMaybe)
}

%name gtl
%tokentype { Token }
%error { parseError }

%token
  "all"             { Key KeyAll }
  "always"          { Key KeyAlways }
  "connect"         { Key KeyConnect }
  "contract"        { Key KeyContract }
  "and"             { Key KeyAnd }
  "follows"         { Key KeyFollows }
  "model"           { Key KeyModel }
  "next"            { Key KeyNext }
  "not"             { Key KeyNot }
  "or"              { Key KeyOr }
  "in"              { Key KeyIn }
  "init"            { Key KeyInit }
  "verify"          { Key KeyVerify }
  "("               { Bracket Parentheses False }
  ")"               { Bracket Parentheses True }
  "["               { Bracket Square False }
  "]"               { Bracket Square True }
  "{"               { Bracket Curly False }
  "}"               { Bracket Curly True }
  ","               { Comma }
  ";"               { Semicolon }
  "<"               { LessThan }
  "<="              { LessThanEqual }
  ">"               { GreaterThan }
  ">="              { GreaterThanEqual }
  "="               { Equals }
  "."               { Dot }
  "+"               { Plus }
  "-"               { Minus }
  "*"               { Mult }
  "/"               { Div }
  id                { Identifier $$ }
  string            { ConstString $$ }
  int               { ConstInt $$ }

%left "always" "next"
%left "or"
%left "and"
%left "follows"
%left "not"
%left "+"
%left "-"
%left "*"
%left "/"

%%

declarations : declaration declarations { $1:$2 }
             |                          { [] }

declaration : model_decl    { Model $1 }
            | connect_decl  { Connect $1 }
            | verify_decl   { Verify $1 }

model_decl : "model" "[" id "]" id model_args model_contract { ModelDecl
                                                               { modelName = $5
                                                               , modelType = $3
                                                               , modelArgs = $6
                                                               , modelContract = mapMaybe (\el -> case el of
                                                                                              Left c -> Just c
                                                                                              Right _ -> Nothing) $7
                                                               , modelInits = mapMaybe (\el -> case el of
                                                                                           Left _ -> Nothing
                                                                                           Right c -> Just c) $7
                                                               }
                                                             }

model_args : "(" model_args1 ")" { $2 }
           |                     { [] }

model_args1 : string model_args2 { $1:$2 }
            |                    { [] }

model_args2 : "," string model_args2 { $2:$3 }
            |                        { [] }

model_contract : "{" formulas_or_inits "}" { $2 }
               | ";"                       { [] }

formulas_or_inits : mb_contract formula ";" formulas_or_inits   { (Left $2):$4 }
                  | init_decl ";" formulas_or_inits             { (Right $1):$3 }
                  |                                             { [] }

mb_contract : "contract" { }
            |            { }

formulas : formula ";" formulas { $1:$3 }
         |                      { [] }

formula : expr_bool { $1 }

expr_bool : expr_bool "and" expr_bool       { ExprBinBool And $1 $3 }
          | expr_bool "or" expr_bool        { ExprBinBool Or $1 $3 }
          | expr_bool "follows" expr_bool   { ExprBinBool Follows $1 $3 }
          | expr_int "<" expr_int           { ExprRel BinLT $1 $3 }
          | expr_int "<=" expr_int          { ExprRel BinLTEq $1 $3 }
          | expr_int ">" expr_int           { ExprRel BinGT $1 $3 }
          | expr_int ">=" expr_int          { ExprRel BinGTEq $1 $3 }
          | expr_int "=" expr_int           { ExprRel BinEq $1 $3 }
          | "not" expr_bool                 { ExprNot $2 }
          | "always" expr_bool              { ExprAlways $2 }
          | "next" expr_bool                { ExprNext $2 }
          | var "in" "{" ints "}"           { ExprElem (fst $1) (snd $1) $4 True }
          | var "not" "in" "{" ints "}"     { ExprElem (fst $1) (snd $1) $5 False }
          | "(" expr_bool ")"               { $2 }

expr_int : var                          { ExprVar (fst $1) (snd $1) }
         | int                          { ExprConst $1 }
         | expr_int "+" expr_int        { ExprBinInt OpPlus $1 $3 }
         | expr_int "-" expr_int        { ExprBinInt OpMinus $1 $3 }
         | expr_int "*" expr_int        { ExprBinInt OpMult $1 $3 }
         | expr_int "/" expr_int        { ExprBinInt OpDiv $1 $3 }
         | "(" expr_int ")"             { $2 }

var : id        { (Nothing,$1) }
    | id "." id { (Just $1,$3) }

ints : int comma_ints { $1:$2 }
     |                { [] }

comma_ints : "," int comma_ints { $2:$3 }
           |                    { [] }

connect_decl : "connect" id "." id id "." id ";" { ConnectDecl $2 $4 $5 $7 }

verify_decl : "verify" "{" formulas "}" { VerifyDecl $3 }

init_decl : "init" id "all" { ($2,InitAll) }
          | "init" id int   { ($2,InitOne $3) }

{
parseError xs = error ("Parse error at "++show (take 5 xs))
}

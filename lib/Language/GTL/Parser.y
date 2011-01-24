{
module Language.GTL.Parser where

import Language.GTL.Token
import Language.GTL.Syntax
}

%name gtl
%tokentype { Token }
%error { parseError }

%token
  "always"          { Key KeyAlways }
  "connect"         { Key KeyConnect }
  "and"             { Key KeyAnd }
  "follows"         { Key KeyFollows }
  "model"           { Key KeyModel }
  "next"            { Key KeyNext }
  "not"             { Key KeyNot }
  "or"              { Key KeyOr }
  "in"              { Key KeyIn }
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
  ">"               { GreaterThan }
  "="               { Equals }
  "."               { Dot }
  id                { Identifier $$ }
  string            { ConstString $$ }
  int               { ConstInt $$ }

%left "always" "next"
%left "or"
%left "and"
%left "follows"
%left "not"

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
                                                               , modelContract = $7
                                                               }
                                                             }

model_args : "(" model_args1 ")" { $2 }
           |                     { [] }

model_args1 : string model_args2 { $1:$2 }
            |                    { [] }

model_args2 : "," string model_args2 { $2:$3 }
            |                        { [] }

model_contract : "{" formulas "}" { $2 }
               | ";"              { [] }

formulas : formula ";" formulas { $1:$3 }
         |                      { [] }

formula : lit "<" lit                { BinRel BinLT $1 $3 }
        | lit ">" lit                { BinRel BinGT $1 $3 }
        | lit "=" lit                { BinRel BinEq $1 $3 }
        | id "in" "{" lits "}"       { Elem $1 $4 True }
        | id "not" "in" "{" lits "}" { Elem $1 $5 False }
        | "not" formula              { Not $2 }
        | formula "and" formula      { BinOp And $1 $3 }
        | formula "or" formula       { BinOp Or $1 $3 }
        | formula "follows" formula  { BinOp Follows $1 $3 }
        | "always" formula           { Always $2 }
        | "next" formula             { Next $2 }
        | "(" formula ")"            { $2 }

lit : int       { Constant $1 }
    | id        { Variable $1 }
    | id "." id { Qualified $1 $3 }

lits : lit comma_lits { $1:$2 }
     |                { [] }

comma_lits : "," lit comma_lits { $2:$3 }
           |                    { [] }

connect_decl : "connect" id "." id id "." id ";" { ConnectDecl $2 $4 $5 $7 }

verify_decl : "verify" "{" formulas "}" { VerifyDecl $3 }

{
parseError xs = error ("Parse error at "++show (take 5 xs))
}

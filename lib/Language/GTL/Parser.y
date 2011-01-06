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

formula : lit "<" lit               { BinLT $1 $3 }
        | lit ">" lit               { BinGT $1 $3 }
        | lit "=" lit               { BinEQ $1 $3 }
        | "not" formula             { Not $2 }
        | formula "and" formula     { And $1 $3 }
        | formula "or" formula      { Or $1 $3 }
        | formula "follows" formula { Follows $1 $3 }
        | "always" formula          { Always $2 }
        | "next" formula            { Next $2 }
        | "(" formula ")"           { $2 }

lit : int { Constant $1 }
    | id  { Variable $1 }

connect_decl : "connect" id "." id id "." id ";" { ConnectDecl $2 $4 $5 $7 }

{
parseError xs = error ("Parse error at "++show (take 5 xs))
}
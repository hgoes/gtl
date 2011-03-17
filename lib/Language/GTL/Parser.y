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
  "always"          { Unary GOpAlways }
  "connect"         { Key KeyConnect }
  "contract"        { Key KeyContract }
  "and"             { Binary GOpAnd }
  "follows"         { Binary GOpFollows }
  "model"           { Key KeyModel }
  "next"            { Unary GOpNext }
  "not"             { Unary GOpNot }
  "or"              { Binary GOpOr }
  "in"              { Binary GOpIn }
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
  "<"               { Binary GOpLessThan }
  "<="              { Binary GOpLessThanEqual }
  ">"               { Binary GOpGreaterThan }
  ">="              { Binary GOpGreaterThanEqual }
  "="               { Binary GOpEqual }
  "!="              { Binary GOpNEqual }
  "."               { Dot }
  "+"               { Binary GOpPlus }
  "-"               { Binary GOpMinus }
  "*"               { Binary GOpMult }
  "/"               { Binary GOpDiv }
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
%left "<" "<=" ">" ">=" "=" "!="
%left "in"

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

formula : expr { case typeCheckBool $1 of
                    Left err -> error err
                    Right e -> e
               }

expr : expr "and" expr        { GBin GOpAnd $1 $3 }
     | expr "or" expr         { GBin GOpOr $1 $3 }
     | expr "follows" expr    { GBin GOpFollows $1 $3 }
     | expr "<" expr          { GBin GOpLessThan $1 $3 }
     | expr "<=" expr         { GBin GOpLessThanEqual $1 $3 }
     | expr ">" expr          { GBin GOpGreaterThan $1 $3 }
     | expr ">=" expr         { GBin GOpGreaterThanEqual $1 $3 }
     | expr "=" expr          { GBin GOpEqual $1 $3 }
     | expr "!=" expr         { GBin GOpNEqual $1 $3 }
     | "not" expr             { GUn GOpNot $2 }
     | "always" expr          { GUn GOpAlways $2 }
     | "next" expr            { GUn GOpNext $2 }
     | expr "in" expr         { GBin GOpIn $1 $3 }
     | expr "not" "in" expr   { GBin GOpNotIn $1 $4 }
     | "{" ints "}"           { GSet $2 }
     | "(" expr ")"           { $2 }
     | var                    { GVar (fst $1) (snd $1) }
     | int                    { GConst $1 }
     | expr "+" expr          { GBin GOpPlus $1 $3 }
     | expr "-" expr          { GBin GOpMinus $1 $3 }
     | expr "/" expr          { GBin GOpDiv $1 $3 }
     | expr "*" expr          { GBin GOpMult $1 $3 }

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

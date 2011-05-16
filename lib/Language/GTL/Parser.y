{
{-| Implements a parser for the GTL specification language.
 -}
module Language.GTL.Parser (gtl) where

import Language.GTL.Parser.Token
import Language.GTL.Parser.Syntax
import Language.GTL.Types

import Data.Maybe (mapMaybe)
import qualified Data.Map as Map
}

%name gtl
%tokentype { Token }
%error { parseError }

%token
  "all"             { Key KeyAll }
  "always"          { Unary GOpAlways }
  "and"             { Binary GOpAnd }
  "automaton"       { Key KeyAutomaton }
  "bool"            { Key KeyBool }
  "byte"            { Key KeyByte }
  "connect"         { Key KeyConnect }
  "contract"        { Key KeyContract }
  "enum"            { Key KeyEnum }
  "exists"          { Key KeyExists }
  "final"           { Key KeyFinal }
  "finally"         { Unary (GOpFinally $$) }
  "float"           { Key KeyFloat }
  "implies"         { Binary GOpImplies }
  "int"             { Key KeyInt }
  "model"           { Key KeyModel }
  "next"            { Unary GOpNext}
  "not"             { Unary GOpNot }
  "or"              { Binary GOpOr }
  "in"              { Binary GOpIn }
  "init"            { Key KeyInit }
  "input"           { Key KeyInput }
  "output"          { Key KeyOutput }
  "state"           { Key KeyState }
  "transition"      { Key KeyTransition }
  "until"           { Key KeyUntil }
  "verify"          { Key KeyVerify }
  "("               { Bracket Parentheses False }
  ")"               { Bracket Parentheses True }
  "["               { Bracket Square False }
  "]"               { Bracket Square True }
  "{"               { Bracket Curly False }
  "}"               { Bracket Curly True }
  ","               { Comma }
  ";"               { Semicolon }
  ":"               { Colon }
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
  "^"               { Binary GOpPow }
  id                { Identifier $$ }
  string            { ConstString $$ }
  int               { ConstInt $$ }

%left ":"
%left "always" "next" "finally"
%left "until"
%left "or"
%left "and"
%left "implies"
%left "not"
%left "<" "<=" ">" ">=" "=" "!="
%left "+"
%left "-"
%left "*"
%left "/"
%left "["
%left "^"
%left "in"

%%

declarations : declaration declarations { $1:$2 }
             |                          { [] }

declaration : model_decl    { Model $1 }
            | connect_decl  { Connect $1 }
            | verify_decl   { Verify $1 }

model_decl : "model" "[" id "]" id model_args model_contract { $7 (ModelDecl
                                                               { modelName = $5
                                                               , modelType = $3
                                                               , modelArgs = $6
                                                               , modelContract = []
                                                               , modelInits = []
                                                               , modelInputs = Map.empty
                                                               , modelOutputs = Map.empty
                                                               })
                                                             }

model_args : "(" model_args1 ")" { $2 }
           |                     { [] }

model_args1 : string model_args2 { $1:$2 }
            |                    { [] }

model_args2 : "," string model_args2 { $2:$3 }
            |                        { [] }

model_contract : "{" formulas_or_inits "}" { $2 }
               | ";"                       { id }

formulas_or_inits : mb_contract formula ";" formulas_or_inits   { \decl -> let ndecl = $4 decl
                                                                           in ndecl { modelContract = $2:(modelContract ndecl)
                                                                                    } }
                  | init_decl ";" formulas_or_inits             { \decl -> let ndecl = $3 decl
                                                                           in ndecl { modelInits = $1:(modelInits ndecl)
                                                                                    } }
                  | "input" type id ";" formulas_or_inits         { \decl -> let ndecl = $5 decl
                                                                             in ndecl { modelInputs = Map.insert $3 $2 (modelInputs ndecl)
                                                                                      } }
                  | "output" type id ";" formulas_or_inits         { \decl -> let ndecl = $5 decl
                                                                              in ndecl { modelOutputs = Map.insert $3 $2 (modelOutputs ndecl)
                                                                                       } }

                  |                                             { id }

mb_contract : "contract" { }
            |            { }

formulas : formula ";" formulas { $1:$3 }
         |                      { [] }

formula : expr { $1 }

expr : expr "and" expr              { GBin GOpAnd $1 $3 }
     | expr "or" expr               { GBin GOpOr $1 $3 }
     | expr "implies" expr          { GBin GOpImplies $1 $3 }
     | expr "until" expr            { GBin GOpUntil $1 $3 }
     | expr "<" expr                { GBin GOpLessThan $1 $3 }
     | expr "<=" expr               { GBin GOpLessThanEqual $1 $3 }
     | expr ">" expr                { GBin GOpGreaterThan $1 $3 }
     | expr ">=" expr               { GBin GOpGreaterThanEqual $1 $3 }
     | expr "=" expr                { GBin GOpEqual $1 $3 }
     | expr "!=" expr               { GBin GOpNEqual $1 $3 }
     | "not" expr                   { GUn GOpNot $2 }
     | "always" expr                { GUn GOpAlways $2 }
     | "next" expr                  { GUn GOpNext $2 }
     | "finally" expr               { GUn (GOpFinally $1) $2 }
     | expr "in" expr               { GBin GOpIn $1 $3 }
     | expr "not" "in" expr         { GBin GOpNotIn $1 $4 }
     | "{" ints "}"                 { GSet $2 }
     | "(" expr_list ")"            { case $2 of
                                         [x] -> x
                                         xs -> GTuple xs
                                    }
     | var                          { GVar (fst $1) (snd $1) }
     | int                          { GConst $ fromIntegral $1 }
     | expr "+" expr                { GBin GOpPlus $1 $3 }
     | expr "-" expr                { GBin GOpMinus $1 $3 }
     | expr "/" expr                { GBin GOpDiv $1 $3 }
     | expr "*" expr                { GBin GOpMult $1 $3 }
     | "exists" id "=" var ":" expr { GExists $2 (fst $4) (snd $4) $6 }
     | "automaton" "{" states "}"   { GAutomaton $3 }
     | expr "[" expr "]"            { GIndex $1 $3 }

expr_list : expr expr_lists { $1:$2 }
          |                 { [] }

expr_lists : "," expr expr_lists { $2:$3 }
           |                     { [] }

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

states : state states { $1:$2 }
       |              { [] }

initial : "init" { True }
        |        { False }

final : "final" { True }
      |         { False }

state : initial final "state" id "{" state_contents "}" { State $4 $1 $2 $6 }

state_contents : state_content state_contents { $1:$2 }
               |                              { [] }

state_content : "transition" id ";"              { Right ($2,Nothing) }
              | "transition" "[" expr "]" id ";" { Right ($5,Just $3) }
              | expr ";"                         { Left $1 }

type : "int"                    { GTLInt }
     | "bool"                   { GTLBool }
     | "byte"                   { GTLByte }
     | "float"                  { GTLFloat }
     | "enum" "{" enum_list "}" { GTLEnum $3 }
     | "(" type_list ")"        { GTLTuple $2 }
     | type "^" int             { GTLArray $3 $1 }

enum_list : id enum_lists { $1:$2 }
          |               { [] }

enum_lists : "," id enum_lists { $2:$3 }
           |                   { [] }

type_list : type type_lists { $1:$2 }
          |                 { [] }

type_lists : "," type type_lists { $2:$3 }
           |                     { [] }

{
parseError xs = error ("Parse error at "++show (take 5 xs))
}

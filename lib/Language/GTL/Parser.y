{
{-| Implements a parser for the GTL specification language.
 -}
module Language.GTL.Parser (gtl) where

import Language.GTL.Parser.Token
import Language.GTL.Parser.Syntax
import Language.GTL.Parser.Monad
import Language.GTL.Parser.Lexer (gtlLexer)
import Language.GTL.Types
import Data.Fix

import qualified Data.Map as Map
import Control.Monad.Error
}

%name gtl
%tokentype { Token }
%lexer { gtlLexer } { EOF }
%monad { GTLParser }
%error { parseError }

%token
  "after"           { Unary GOpAfter }
  "all"             { Key KeyAll }
  "always"          { Unary GOpAlways }
  "and"             { Binary GOpAnd }
  "automaton"       { Key KeyAutomaton }
  "bool"            { Key KeyBool }
  "byte"            { Key KeyByte }
  "connect"         { Key KeyConnect }
  "contract"        { Key KeyContract }
  "cycle-time"      { Key KeyCycleTime }
  "enum"            { Key KeyEnum }
  "exists"          { Key KeyExists }
  "false"           { Key KeyFalse }
  "final"           { Key KeyFinal }
  "finally"         { Unary GOpFinally }
  "float"           { Key KeyFloat }
  "guaranteed"      { Key KeyGuaranteed }
  "implies"         { Binary GOpImplies }
  "int"             { Key KeyInt }
  "local"           { Key KeyLocal }
  "model"           { Key KeyModel }
  "next"            { Unary GOpNext}
  "not"             { Unary GOpNot }
  "or"              { Binary GOpOr }
  "in"              { Binary GOpIn }
  "init"            { Key KeyInit }
  "input"           { Key KeyInput }
  "instance"        { Key KeyInstance }
  "output"          { Key KeyOutput }
  "state"           { Key KeyState }
  "transition"      { Key KeyTransition }
  "true"            { Key KeyTrue }
  "type"            { Key KeyType }
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
  ":="              { Binary GOpAssign }
  "!="              { Binary GOpNEqual }
  "."               { Dot }
  "+"               { Binary GOpPlus }
  "-"               { Binary GOpMinus }
  "*"               { Binary GOpMult }
  "/"               { Binary GOpDiv }
  "^"               { Binary GOpPow }
  "#in"             { CtxIn }
  "#out"            { CtxOut }
  id                { Identifier $$ }
  enum              { ConstEnum $$ }
  string            { ConstString $$ }
  int               { ConstInt $$ }

%left "#in" "#out"
%left ":"
%left "always" "next" "finally" "after"
%left "until"
%left "or"
%left "and"
%left "implies"
%left "not"
%left "<" "<=" ">" ">=" "=" "!=" ":="
%left "+"
%left "-"
%left "*"
%left "/"
%left "["
%left "^"
%left "in"

%%

list(p,q) : p lists(p,q) { $1:$2 }
          |              { [] }

lists(p,q) : q p lists(p,q) { $2:$3 }
           |                { [] }

maybe(p) : p { Just $1 }
         |   { Nothing }

bool(p) : p { True }
        |   { False }

many(p) : p many(p) { $1:$2 }
        |           { [] }

fby(p,q) : p q { $1 }

declarations : many(declaration) { $1 }

declaration : model_decl    { Model $1 }
            | connect_decl  { Connect $1 }
            | verify_decl   { Verify $1 }
            | instance_decl { Instance $1 }
            | alias_decl    { $1 }

model_decl : "model" "[" id "]" id model_args model_contract { $7 (ModelDecl
                                                               { modelName = $5
                                                               , modelType = $3
                                                               , modelArgs = $6
                                                               , modelContract = []
                                                               , modelInits = []
                                                               , modelInputs = Map.empty
                                                               , modelOutputs = Map.empty
                                                               , modelLocals = Map.empty
                                                               , modelCycleTime = 1
                                                               })
                                                             }

instance_decl : "instance" id id instance_contract { $4 (InstanceDecl
                                                         { instanceModel = $2
                                                         , instanceName = $3
                                                         , instanceContract = []
                                                         , instanceInits =  []
                                                         }) }

alias_decl : "type" id "=" type ";" { TypeAlias $2 $4 }

model_args : "(" list(model_arg,",") ")" { $2 }
           |                             { [] }

model_arg : string          { StrArg $1 }
          | id ":=" pexpr   { ConstantDecl $1 $3 }

model_contract : "{" formulas_or_inits_or_vars "}" { $2 }
               | ";"                               { id }

instance_contract : "{" formulas_or_inits "}" { $2 }
                  | ";"                       { id }

contract : bool("guaranteed") bool("contract") pexpr { Contract $1 $3 }

formulas_or_inits_or_vars  : contract ";" formulas_or_inits_or_vars { \decl -> let ndecl = $3 decl
                                                                               in ndecl { modelContract = $1:(modelContract ndecl)
                                                                                                      } }
                           | init_decl ";" formulas_or_inits_or_vars           { \decl -> let ndecl = $3 decl
                                                                                          in ndecl { modelInits = $1:(modelInits ndecl)
                                                                                                   } }
                           | "input" type id ";" formulas_or_inits_or_vars       { \decl -> let ndecl = $5 decl
                                                                                          in ndecl { modelInputs = Map.insert $3 $2 (modelInputs ndecl)
                                                                                                   } }
                           | "output" type id ";" formulas_or_inits_or_vars      { \decl -> let ndecl = $5 decl
                                                                                          in ndecl { modelOutputs = Map.insert $3 $2 (modelOutputs ndecl)
                                                                                                   } }
                           | "local" type id ";" formulas_or_inits_or_vars       { \decl -> let ndecl = $5 decl
                                                                                            in ndecl { modelLocals = Map.insert $3 $2 (modelLocals ndecl)
                                                                                                   } }
                           | "cycle-time" int id ";" formulas_or_inits_or_vars { \decl -> let ndecl = $5 decl
                                                                                          in ndecl { modelCycleTime = $2 * (case $3 of
                                                                                                       "s" -> 1000000
                                                                                                       "ms" -> 1000
                                                                                                       "us" -> 1) } }
                           |                                                   { id }

formulas_or_inits : contract ";" formulas_or_inits { \decl -> let ndecl = $3 decl
                                                              in ndecl { instanceContract = $1:(instanceContract ndecl) } }
                  | init_decl ";" formulas_or_inits           { \decl -> let ndecl = $3 decl
                                                                         in ndecl { instanceInits = $1:(instanceInits ndecl) } }
                  |                                           { id }


formulas : many(fby(pexpr,";")) { $1 }

pexpr : expr {% do { pos <- getPos ; return (pos,$1) } }

expr : pexpr "and" pexpr                 { GBin GOpAnd NoTime $1 $3 }
     | pexpr "or" pexpr                  { GBin GOpOr NoTime $1 $3 }
     | pexpr "implies" pexpr             { GBin GOpImplies NoTime $1 $3 }
     | pexpr "until" pexpr               { GBin GOpUntil NoTime $1 $3 }
     | pexpr "until" time_spec pexpr     { GBin GOpUntil $3 $1 $4 }
     | pexpr "<" pexpr                   { GBin GOpLessThan NoTime $1 $3 }
     | pexpr "<=" pexpr                  { GBin GOpLessThanEqual NoTime $1 $3 }
     | pexpr ">" pexpr                   { GBin GOpGreaterThan NoTime $1 $3 }
     | pexpr ">=" pexpr                  { GBin GOpGreaterThanEqual NoTime $1 $3 }
     | pexpr "=" pexpr                   { GBin GOpEqual NoTime $1 $3 }
     | pexpr ":=" pexpr                  { GBin GOpEqual NoTime (fst $1,GContext ContextOut $1) (fst $3,GContext ContextIn $3) }
     | pexpr "!=" pexpr                  { GBin GOpNEqual NoTime $1 $3 }
     | "after" time_spec pexpr          { GUn GOpAfter $2 $3 }
     | "not" pexpr                      { GUn GOpNot NoTime $2 }
     | "always" pexpr                   { GUn GOpAlways NoTime $2 }
     | "next" pexpr                     { GUn GOpNext NoTime $2 }
     | "next" time_spec pexpr           { GUn GOpNext $2 $3 }
     | "finally" pexpr                  { GUn GOpFinally NoTime $2 }
     | "finally" time_spec pexpr        { GUn GOpFinally $2 $3 }
     | pexpr "in" pexpr                  { GBin GOpIn NoTime $1 $3 }
     | pexpr "not" "in" pexpr            { GBin GOpNotIn NoTime $1 $4 }
     | "{" ints "}"                    { GSet $2 }
     | "(" pexpr_list ")"               { case $2 of
                                            [x] -> snd x
                                            xs -> GTuple xs
                                       }
     | "[" pexpr_list "]"               { GArray $2 }
     | var                             { GVar (fst $1) (snd $1) }
     | int                             { GConst $ fromIntegral $1 }
     | pexpr "+" pexpr                   { GBin GOpPlus NoTime $1 $3 }
     | pexpr "-" pexpr                   { GBin GOpMinus NoTime $1 $3 }
     | pexpr "/" pexpr                   { GBin GOpDiv NoTime $1 $3 }
     | pexpr "*" pexpr                   { GBin GOpMult NoTime $1 $3 }
     | "exists" id "=" var ":" pexpr    { GExists $2 (fst $4) (snd $4) $6 }
     | "automaton" "{" many(state) "}" { GAutomaton $3 }
     | pexpr "[" pexpr "]"               { GIndex $1 $3 }
     | enum                            { GEnum $1 }
     | "true"                          { GConstBool True }
     | "false"                         { GConstBool False }
     | id "(" pexpr_list ")"            { GBuiltIn $1 $3 }
     | "#in" pexpr                      { GContext ContextIn $2 }  
     | "#out" pexpr                     { GContext ContextOut $2 }
       
pexpr_list : list(pexpr,",") { $1 }

var : id        { (Nothing,$1) }
    | id "." id { (Just $1,$3) }

ints : list(int,",") { $1 }

connect_decl : "connect" id "." id indices id "." id indices ";" { ConnectDecl $2 $4 $5 $6 $8 $9 }

indices : "[" int "]" indices { $2:$4 }
        |                     { [] }

verify_decl : "verify" "{" formulas "}" { VerifyDecl $3 }

init_decl : "init" id "all"  { ($2,InitAll) }
          | "init" id pexpr  { ($2,InitOne $3) }

state : bool("init") bool("final") "state" id "{" many(state_content) "}" { State $4 $1 $2 $6 }

state_content : "transition" id ";"               { Right ($2,Nothing) }
              | "transition" "[" pexpr "]" id ";" { Right ($5,Just $3) }
              | pexpr ";"                         { Left $1 }

type : "int"                       { Fix $ UnResolvedType' $ Right GTLInt }
     | "bool"                      { Fix $ UnResolvedType' $ Right GTLBool }
     | "byte"                      { Fix $ UnResolvedType' $ Right GTLByte }
     | "float"                     { Fix $ UnResolvedType' $ Right GTLFloat }
     | "enum" "{" list(id,",") "}" { Fix $ UnResolvedType' $ Right $ GTLEnum $3 }
     | "(" list(type,",") ")"      { Fix $ UnResolvedType' $ Right $ GTLTuple $2 }
     | type "^" int                { Fix $ UnResolvedType' $ Right $ GTLArray $3 $1 }
     | id                          { Fix $ UnResolvedType' $ Left $1 }

time_spec : "[" int id "]" { case $3 of
                                "cy" -> TimeSteps $2
                                "s" -> TimeUSecs ($2*1000000)
                                "ms" -> TimeUSecs ($2*1000)
                                "us" -> TimeUSecs $2 }

{
parseError tok = throwError $ "Parse error at: "++show tok
}

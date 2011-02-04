module Language.GTL.ScadeToPromela where

import Language.Scade.Syntax as Sc
import Language.Promela.Syntax as Pr
import Data.Map as Map

convertType :: Sc.TypeExpr -> Pr.Typename
convertType Sc.TypeBool = Pr.TypeBool
convertType Sc.TypeInt = Pr.TypeInt
convertType tp = error $ "Cannot convert type "++show tp

scadeToPromela :: [Sc.Declaration] -> [Pr.Module]
scadeToPromela decls = [ declarationToProcess decl | decl@(UserOpDecl {}) <- decls ]

declarationToProcess :: Sc.Declaration -> Pr.Module
declarationToProcess opdecl
  = let (decls,steps) = equationsToSteps (dataEquations $ userOpContent opdecl)
    in  ProcType { proctypeActive = Nothing
                 , proctypeName = userOpName opdecl
                 , proctypeArguments = [ Declaration { declarationVisible = Nothing
                                                     , declarationType = TypeChan
                                                     , declarationVariables = [ ("chan_"++name var,Nothing,Nothing) | var <- varNames par ] 
                                                     }
                                       | par <- userOpParams opdecl ++ userOpReturns opdecl ]
                 , proctypePriority = Nothing
                 , proctypeProvided = Nothing
                 , proctypeSteps = [StepDecl $ Declaration { declarationVisible = Nothing
                                                           , declarationType = convertType (varType par)
                                                           , declarationVariables = [ (name var,Nothing,Nothing) | var <- varNames par ]
                                                           }
                                   | par <- userOpParams opdecl ++ userOpReturns opdecl
                                   ] ++ [StepDecl decl | decl <- decls]++
                                   [StepStmt (StmtDo
                                              [[StepStmt (StmtReceive ("chan_"++name var) [RecvVar (VarRef (name var) Nothing Nothing)]) Nothing
                                               | par <- userOpParams opdecl, var <- varNames par
                                               ]++steps
                                              ]
                                             ) Nothing
                                   ]
                 }

dataDefToSteps :: DataDef -> ([Pr.Declaration],[Step])
dataDefToSteps def = let (decls,steps) = equationsToSteps (dataEquations def)
                         locs = [ StepDecl $ Declaration Nothing (convertType $ varType var) [(Sc.name vid,Nothing,Nothing) | vid <- varNames var ]
                                | var <- dataLocals def
                                ]
                     in (decls,locs++steps)

equationsToSteps :: [Equation] -> ([Pr.Declaration],[Step])
equationsToSteps [] = ([],[])
equationsToSteps (e:es) = let (r1,r2) = equationsToSteps es
                              (c1,c2) = equationToSteps e
                          in (c1++r1,c2++r2)

equationToSteps :: Equation -> ([Pr.Declaration],[Step])
equationToSteps (StateEquation (StateMachine (Just name) states) _ _)
  = let statemap = Map.fromList (zip (fmap stateName states) [0..])
        init = case [st | st <- states, stateInitial st] of
          [] -> error "No initial state found"
          [is] -> statemap!(stateName is)
          _ -> error "Too many initial states found"
        ifs = [ (rdecls,
                 [StepStmt (StmtSequence $
                            [StepStmt (StmtExpr (ExprAny
                                                  (BinExpr Pr.BinEquals
                                                   (RefExpr (VarRef ("state_"++name) Nothing Nothing))
                                                   (ConstExpr (ConstInt $ statemap!(stateName st)))
                                                  ))) Nothing
                            ]++rsteps
                           ) Nothing
                 ])
              | st <- states, let (rdecls,rsteps) = dataDefToSteps $ stateData st ]
    in ([Declaration Nothing Pr.TypeInt [("state_"++name,Nothing,Just (ConstExpr (ConstInt init)))]]
        ++(concat $ fmap fst ifs),
        [StepStmt (StmtIf $ fmap snd ifs) Nothing])
equationToSteps (SimpleEquation lhs rhs) = ([],buildAssign lhs rhs)
equationToSteps _ = ([],[])

buildAssign :: [LHSId] -> Sc.Expr -> [Step]
buildAssign lhs (IdExpr (Path [var])) = case lhs of
  [Named trg] -> [StepStmt (StmtAssign (VarRef trg Nothing Nothing) (RefExpr $ VarRef var Nothing Nothing)) Nothing]
  _ -> []
buildAssign _ _ = []
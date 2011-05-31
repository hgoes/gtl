module Language.GTL.Target.UPPAAL where

import Language.GTL.Model hiding (getEnums)
import Language.GTL.Types
import Language.GTL.Expression as G
import Language.GTL.Buchi
import Language.UPPAAL.Syntax as U
import Language.GTL.Target.Common

import Data.List (genericLength)
import Data.Map as Map
import Data.Set as Set

translateSpec :: GTLSpec String -> U.Specification
translateSpec spec = translateTarget (buildTargetModel spec (buildInputMap spec) (buildOutputMap spec))

getEnums :: TargetModel -> Map [String] Int
getEnums tm = foldl (\mp x -> case Map.lookup x mp of
                        Nothing -> Map.insert x (Map.size mp) mp
                        Just _ -> mp) Map.empty [ xs | (_,_,GTLEnum xs) <- tmodelVars tm ]

translateTarget :: TargetModel -> U.Specification
translateTarget tm
  = Spec { specImports = Nothing
         , specDeclarations = enum_decls ++ var_decls
         , specTemplates = templates
         , specInstantiation = Nothing
         , specProcesses = [ (pname,pname++"_tmpl",[])
                           | pname <- Map.keys (tmodelProcs tm) ]
         , specSystem = [ pname
                        | pname <- Map.keys (tmodelProcs tm) ]
         }
    where
      all_enums = getEnums tm
      enum_decls = concat [ [ TypeDecl (Type Nothing (TypeScalar (ExprNat (genericLength xs)))) [("enum"++show i,[])] ] ++
                            [ VarDecl (Type Nothing (TypeName ("enum"++show i))) [(x,[],Nothing)]
                            | x <- xs ]
                          | (xs,i) <- Map.toList all_enums ]
      var_decls = [ VarDecl (Type Nothing (convertType all_enums tp))
                    [(varString var,[ExprArray (ExprNat (lvl+1))],Nothing)]
                  | (var,lvl,tp) <- tmodelVars tm ]
      templates = [Template (noPos $ pname++"_tmpl") Nothing [] 
                   (start_loc ++ st_locs)
                   (Just "start") (start_trans++st_trans)
                  | (pname,buchi) <- Map.toList (tmodelProcs tm),
                    let st_locs = [ noPos $ Location { locId = ("l"++show s1++"_"++show s2)
                                                     , locName = Just (noPos $ "l"++show s1++"_"++show s2)
                                                     , locLabels = []
                                                     , locUrgent = False
                                                     , locCommited = False
                                                     , locColor = Nothing
                                                     }
                                  | ((s1,s2),st) <- Map.toList buchi
                                  ],
                    let start_loc = [ noPos $ Location { locId = "start"
                                                       , locName = Just $ noPos "start"
                                                       , locLabels = []
                                                       , locUrgent = True
                                                       , locCommited = False
                                                       , locColor = Nothing
                                                       } ],
                    let start_trans = [ noPos $ Transition Nothing "start" ("l"++show s1++"_"++show s2)
                                        [] [] Nothing
                                      | ((s1,s2),st) <- Map.toList buchi, isStart st ],
                    let st_trans = [ noPos $ Transition { transId = Nothing 
                                                        , transSource = "l"++show s1++"_"++show s2 
                                                        , transTarget = "l"++show t1++"_"++show t2
                                                        , transLabel = translateRestrictions all_enums 0 (fst (vars nst))
                                                        , transNails = []
                                                        , transColor = Nothing
                                                        }
                                   | ((s1,s2),st) <- Map.toList buchi,
                                     (t1,t2) <- Set.toList (successors st), 
                                     let nst = buchi!(t1,t2)
                                     ]
                  ]

translateRestrictions :: Map [String] Int -> Integer -> [([(TargetVar,Integer)],Restriction TargetVar)] -> [Positional Label]
translateRestrictions _ _ [] = []
translateRestrictions enums i ((tvars,restr):xs)
  = (translateRestriction enums i restr) ++
    (translateUpdate i tvars)++
    (translateRestrictions enums (i+1) xs)

translateUpdate :: Integer -> [(TargetVar,Integer)] -> [Positional Label]
translateUpdate i vars = [noPos (Label Assignment [ExprAssign Assign
                                                   (ExprIndex (ExprId (varString var)) (ExprNat j))
                                                   (if j==0
                                                    then ExprId ("tmp"++show i)
                                                    else ExprIndex (ExprId (varString var)) (ExprNat (j-1)))
                                                  | (var,lvl) <- vars, j <- reverse [0..lvl] ])]
  
translateRestriction :: Map [String] Int -> Integer -> Restriction TargetVar -> [Positional Label]
translateRestriction enums i restr
  = [noPos (Label Selection [ExprSelect [("tmp"++show i,Type Nothing (convertType enums (restrictionType restr)))]])
    ,noPos (Label Guard $ 
            [ ExprBinary (if ins then U.BinGTE else U.BinGT) (ExprId ("tmp"++show i)) (translateExpression lower)
            | (ins,lower) <- lowerLimits restr
            ] ++
            [ ExprBinary (if ins then U.BinLTE else U.BinLT) (ExprId ("tmp"++show i)) (translateExpression upper)
            | (ins,upper) <- upperLimits restr
            ] ++
            [ ExprBinary U.BinEq (ExprId ("tmp"++show i)) (translateExpression e)
            | e <- equals restr
            ] ++
            [ ExprBinary U.BinNEq (ExprId ("tmp"++show i)) (translateExpression e)
            | e <- unequals restr
            ]
           )
    ]

translateExpression :: TypedExpr TargetVar -> Expression
translateExpression expr = case getValue expr of
  Var v h -> ExprIndex (ExprId (varString v)) (ExprNat h)
  Value (GTLBoolVal b) -> ExprNat (if b
                                   then 1
                                   else 0)
  Value (GTLIntVal b) -> ExprNat b
  Value (GTLEnumVal x) -> ExprId x
  BinBoolExpr op (Fix l) (Fix r) -> ExprBinary (case op of
                                                   And -> BinAnd
                                                   Or -> BinOr
                                                   Implies -> BinImply) (translateExpression l) (translateExpression r)
  BinRelExpr op (Fix l) (Fix r) -> ExprBinary (case op of
                                                  G.BinLT -> U.BinLT
                                                  G.BinLTEq -> U.BinLTE
                                                  G.BinGT -> U.BinGT
                                                  G.BinGTEq -> U.BinGTE
                                                  G.BinEq -> U.BinEq
                                                  G.BinNEq -> U.BinNEq) (translateExpression l) (translateExpression r)
                                                  

convertType :: Map [String] Int -> GTLType -> TypeId
convertType _ GTLInt = TypeInt Nothing
convertType _ GTLByte = TypeInt (Just (ExprNat 0,ExprNat 255))
convertType _ GTLBool = TypeInt (Just (ExprNat 0,ExprNat 1))
convertType enums (GTLEnum xs) = TypeName ("enum"++show (enums!xs))

varString :: TargetVar -> String
varString (iname,var,idx) = iname++"_"++var++concat [ "_"++show i | i <- idx ]
{-| Provides a UPPAAL verification target.
    UPPAAL is a state-based verification formalism and thus it is quite easy to translate GTL code to it.
 -}
module Language.GTL.Target.UPPAAL where

import Language.GTL.Model hiding (getEnums)
import Language.GTL.Types
import Language.GTL.Expression as G
import Language.GTL.Buchi
import Language.UPPAAL.Syntax as U
import Language.GTL.Target.Common

import Data.List (genericLength,genericReplicate,elemIndex)
import Data.Map as Map
import Data.Set as Set

-- | Translate a GTL specification to a UPPAAL specification.
translateSpec :: GTLSpec String -> U.Specification
translateSpec spec = translateTarget (buildTargetModel spec (buildInputMap spec) (buildOutputMap spec))

-- | Translate a pre-translated TargetModel to a UPPAAL specification.
translateTarget :: TargetModel -> U.Specification
translateTarget tm
  = Spec { specImports = Nothing
         , specDeclarations = var_decls
         , specTemplates = templates
         , specInstantiation = Nothing
         , specProcesses = [ (pname,pname++"_tmpl",[])
                           | pname <- Map.keys (tmodelProcs tm) ]
         , specSystem = [ pname
                        | pname <- Map.keys (tmodelProcs tm) ]
         }
    where
      var_decls = [ VarDecl (Type Nothing (convertType tp))
                    [(varString var,[ExprArray (ExprNat (lvl+1))],case init of
                         Nothing -> Nothing
                         Just iset -> Just $ InitArray $ genericReplicate (lvl+1) $ InitExpr $ translateConstant tp $ unfix $ head $ Set.toList iset)]
                  | (var,lvl,tp,init) <- tmodelVars tm ]
      templates = [Template (noPos $ pname++"_tmpl") Nothing [] 
                   (start_loc ++ st_locs)
                   (Just "start") (start_trans++st_trans)
                  | (pname,buchi) <- Map.toList (tmodelProcs tm),
                    let st_locs = [ {-noPos $ Location { locId = ("l"++show s1++"_"++show s2)
                                                     , locName = Just (noPos $ "l"++show s1++"_"++show s2)
                                                     , locLabels = []
                                                     , locUrgent = False
                                                     , locCommited = False
                                                     , locColor = Nothing
                                                     }
                                  | ((s1,s2),st) <- Map.toList buchi-}
                                  ],
                    let start_loc = [ noPos $ Location { locId = "start"
                                                       , locName = Just $ noPos "start"
                                                       , locLabels = []
                                                       , locUrgent = True
                                                       , locCommited = False
                                                       , locColor = Nothing
                                                       } ],
                    let start_trans = [ {-noPos $ Transition { transId = Nothing
                                                           , transSource = "start"
                                                           , transTarget = "l"++show s1++"_"++show s2
                                                           , transLabel = translateRestrictions 0 (fst (vars st)) ++
                                                                          translateConditions (snd (vars st))
                                                           , transNails = []
                                                           , transColor = Nothing
                                                           }
                                      | ((s1,s2),st) <- Map.toList buchi, isStart st-} ],
                    let st_trans = [ {-noPos $ Transition { transId = Nothing 
                                                        , transSource = "l"++show s1++"_"++show s2 
                                                        , transTarget = "l"++show t1++"_"++show t2
                                                        , transLabel = translateRestrictions 0 (fst (vars nst)) ++
                                                                       translateConditions (snd (vars nst))
                                                        , transNails = []
                                                        , transColor = Nothing
                                                        }
                                   | ((s1,s2),st) <- Map.toList buchi,
                                     (t1,t2) <- Set.toList (successors st), 
                                     let nst = buchi!(t1,t2)-}
                                     ]
                  ]

-- | Translate a list of conditional expressions into edge guards.
translateConditions :: [TypedExpr TargetVar] -> [Positional Label]
translateConditions conds = [noPos (Label Guard [ translateExpression e ])
                            | e <- conds ]

-- | Translate a list of output restrictions into edge updates.
translateRestrictions :: Integer -> [([(TargetVar,Integer)],Restriction TargetVar)] -> [Positional Label]
translateRestrictions _ [] = []
translateRestrictions i ((tvars,restr):xs)
  = (translateRestriction i restr) ++
    (translateUpdate i tvars)++
    (translateRestrictions (i+1) xs)

-- | Assign a temporary variable to a list of output variables.
translateUpdate :: Integer -- ^ Numbering of the variable
                   -> [(TargetVar,Integer)] -- ^ List of output variables including their history level
                   -> [Positional Label]
translateUpdate i vars = [noPos (Label Assignment [ExprAssign Assign
                                                   (ExprIndex (ExprId (varString var)) (ExprNat j))
                                                   (if j==0
                                                    then ExprId ("tmp"++show i)
                                                    else ExprIndex (ExprId (varString var)) (ExprNat (j-1)))
                                                  | (var,lvl) <- vars, j <- reverse [0..lvl] ])]

-- | Translate a single output restriction into a temporary variable that non-deterministically gets assigned the allowed values.
translateRestriction :: Integer -> Restriction TargetVar -> [Positional Label]
translateRestriction i restr
  = [noPos (Label Selection [ExprSelect [("tmp"++show i,Type Nothing (convertType (restrictionType restr)))]])
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

-- | Translate a GTLValue into a UPPAAL expression.
translateConstant :: GTLType -> GTLValue r -> Expression
translateConstant _ (GTLBoolVal b) = ExprNat (if b then 1 else 0)
translateConstant _ (GTLIntVal b) = ExprNat b
translateConstant (GTLEnum xs) (GTLEnumVal x) = let Just i = elemIndex x xs
                                                in ExprNat (fromIntegral i)

-- | Translate a GTL expression into a UPPAAL one.
translateExpression :: TypedExpr TargetVar -> Expression
translateExpression expr = case getValue expr of
  Var v h -> ExprIndex (ExprId (varString v)) (ExprNat h)
  Value val -> translateConstant (getType expr) val
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
  BinIntExpr op (Fix l) (Fix r) -> ExprBinary (case op of
                                                  G.OpPlus -> U.BinPlus
                                                  G.OpMinus -> U.BinMinus
                                                  G.OpMult -> U.BinMult
                                                  G.OpDiv -> U.BinDiv) (translateExpression l) (translateExpression r)
  UnBoolExpr op (Fix e) -> ExprUnary (case op of
                                         G.Not -> U.UnNot) (translateExpression e)
                                                  
-- | Translate a GTL type into a UPPAAL type.
convertType :: GTLType -> TypeId
convertType GTLInt = TypeInt Nothing
convertType GTLByte = TypeInt (Just (ExprNat 0,ExprNat 255))
convertType GTLBool = TypeInt (Just (ExprNat 0,ExprNat 1))
convertType (GTLEnum xs) = TypeInt (Just (ExprNat 0,ExprNat ((genericLength xs)-1)))

-- | Get the UPPAAL name of a variable.
varString :: TargetVar -> String
varString (iname,var,idx) = iname++"_"++var++concat [ "_"++show i | i <- idx ]
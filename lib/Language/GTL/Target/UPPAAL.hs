module Language.GTL.Target.UPPAAL where

import Language.GTL.Model hiding (getEnums)
import Language.GTL.Types
import Language.GTL.Expression
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
                    [(varString iname var idx,[ExprArray (ExprNat (lvl+1))],Nothing)]
                  | ((iname,var,idx),lvl,tp) <- tmodelVars tm ]
      templates = [Template (noPos $ pname++"_tmpl") Nothing [] 
                   (start_loc ++ st_locs)
                   (Just "start") (start_trans++st_trans)
                  | (pname,buchi) <- Map.toList (tmodelProcs tm),
                    let st_locs = [ noPos $ Location { locId = ("l"++show s1++"_"++show s2)
                                                     , locName = Just (noPos $ "l"++show s1++"_"++show s2)
                                                     , locLabels = [ 
                                                                   ]
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
                    let st_trans = [ noPos $ Transition Nothing ("l"++show s1++"_"++show s2) ("l"++show t1++"_"++show t2)
                                     [] [] Nothing
                                   | ((s1,s2),st) <- Map.toList buchi,
                                     (t1,t2) <- Set.toList (successors st) ]
                  ]

convertType :: Map [String] Int -> GTLType -> TypeId
convertType _ GTLInt = TypeInt Nothing
convertType _ GTLByte = TypeInt (Just (ExprNat 0,ExprNat 255))
convertType _ GTLBool = TypeBool
convertType enums (GTLEnum xs) = TypeName ("enum"++show (enums!xs))

varString :: String -> String -> [Integer] -> String
varString iname var idx = iname++"_"++var++concat [ "_"++show i | i <- idx ]
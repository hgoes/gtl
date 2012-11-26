{-# LANGUAGE TypeFamilies #-}
module Language.GTL.Backend.C where

import qualified Data.Map as Map
import Language.GTL.Backend
import Language.GTL.Types
import Language.GTL.DFA
import Language.GTL.Expression
import Language.GTL.Translation
import Language.C
import Language.C.System.GCC (newGCC)
import Language.C.Analysis.AstAnalysis
import Language.C.Analysis.TravMonad
import Language.C.Analysis.SemRep
import Language.C.Data.Ident
import Language.C.Analysis.TypeUtils
import Language.C.Analysis.TypeCheck
import System.FilePath
import Data.List (partition)

data CBackend = CBackend

cTypeToGTL' :: Type -> Maybe GTLType
cTypeToGTL' (DirectType tn _ _) = case tn of
  TyIntegral TyBool -> Just gtlBool
  TyIntegral TyInt -> Just gtlInt
  TyIntegral TyChar -> Just gtlByte
  _ -> Nothing
cTypeToGTL' _ = Nothing

cTypeToGTL :: Type -> GTLType
cTypeToGTL tp = case cTypeToGTL' tp of
  Nothing -> error $ "C-type "++show (pretty tp)++" has no representation in gtl."
  Just t -> t

instance GTLBackend CBackend where
  data GTLBackendModel CBackend = CBackendModel { stateName :: String
                                                , initName :: String
                                                , stepName :: String
                                                , inputVars :: [(String,Type)]
                                                , outputVars :: [(String,Type)]
                                                , headerFiles :: [String]
                                                , sourceFiles :: [String]
                                                }
  backendName _ = "c"
  initBackend _ opts (st:init:step:mods) = do
    files <- mapM (\file -> do
                      res <- parseCFile (newGCC "gcc") Nothing [] file
                      case res of
                        Left err -> error $ "Error while parsing C-component specification: "++show err
                        Right ast -> case runTrav_ (analyseAST ast) of
                          Left errs -> error $ "Error while analyzing C-component specification: "++show errs
                          Right (glob,_) -> return glob
                  ) mods
    let (decls,enums,objdefs,fundefs,tdefs,tags) 
          = foldl (\(decls',enums',objdefs',fundefs',tdefs',tags') glob
                   -> let (ndecls,(nenums,nobjdefs,nfundefs)) = splitIdentDecls False (gObjs glob)
                      in (Map.union decls' ndecls,
                          Map.union enums' nenums,
                          Map.union objdefs' nobjdefs,
                          Map.union fundefs' nfundefs,
                          Map.union tdefs' (gTypeDefs glob),
                          Map.union tags' (gTags glob)))
            (Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty) files
        {-globs = foldl mergeGlobalDecls emptyGlobalDecls files
        (decls,(enums,objdefs,fundefs)) = splitIdentDecls True (gObjs globs)-}
    case [ f | (Ident n _ _,f) <- Map.toList fundefs, n==init ] of
      [FunDef (VarDecl _ _ (FunctionType (FunType rtp pars variadic) _)) _ _] -> case rtp of
        DirectType TyVoid _ _ -> if variadic
                                 then error "init function is variadic."
                                 else (case pars of
                                          [ParamDecl (VarDecl _ _ tp) _] -> case tp of
                                            PtrType (TypeDefType (TypeDefRef (Ident n _ _) _ _) _ _) _ _ -> if n /= st
                                                                                                            then error "init function must have pointer to state type as parameter."
                                                                                                            else return ()
                                            _ -> error "init function must have pointer to state type as parameter."
                                          _ -> error "init function must have exactly one parameter."
                                      )
        _ -> error "init function doesn't return void."
      [] -> error "Init function not found in C-component."
      _ -> error "More than one init function found."
    let inputs = case [ f | (Ident n _ _,f) <- Map.toList fundefs, n==step ] of
          [FunDef (VarDecl _ _ (FunctionType (FunType rtp pars variadic) _)) _ _] -> case rtp of
            DirectType TyVoid _ _ -> if variadic
                                     then error "step function is variadic."
                                     else (case pars of
                                              [] -> error "step function needs at least one parameter."
                                              _ -> let (inps,arg_st) = splitLast pars
                                                   in case arg_st of
                                                     ParamDecl (VarDecl _ _ tp) _ -> case tp of
                                                       PtrType (TypeDefType (TypeDefRef (Ident n _ _) _ _) _ _) _ _
                                                         -> if n /= st
                                                            then error "step function must have pointer to state type as last parameter."
                                                            else fmap (\par -> case par of
                                                                          ParamDecl (VarDecl (VarName (Ident n _ _) _) _ tp) _ -> (n,tp)
                                                                          _ -> error "invalid input type for step function."
                                                                      ) inps
                                                       _ -> error "step function must have pointer to state type as last parameter."
                                                     _ -> error "step function must have pointer to state type as last parameter."
                                          )
            _ -> error "step function doesn't return void."
        outputs = case [ td | (Ident n _ _,td) <- Map.toList tdefs, n==st ] of
          [TypeDef _ tp _ _] -> case tp of
            DirectType (TyComp (CompTypeRef ref StructTag _)) _ _ -> case Map.lookup ref tags of
              Just (CompDef (CompType _ _ members _ _)) -> [ (identToString name,tp) | MemberDecl (VarDecl (VarName name _) _ tp) _ _ <- members ]
              _ -> error "struct definition of state type not found."
          [] -> error "type definition of state not found."
          _ -> error "too many type definitions for state found."
        (hsource,csource) = partition (\fn -> case takeExtension fn of
                                          ".h" -> True
                                          ".hpp" -> True
                                          _ -> False) mods
    return $ CBackendModel { stateName = st
                           , initName = init
                           , stepName = step
                           , inputVars = inputs
                           , outputVars = outputs
                           , headerFiles = hsource
                           , sourceFiles = csource
                           }
  backendGetAliases _ _ = Map.empty
  typeCheckInterface _ backend (inp,outp) = do
    inp' <- mergeTypes inp (fmap cTypeToGTL (Map.fromList $ inputVars backend))
    outp' <- mergeTypes outp (Map.mapMaybe cTypeToGTL' (Map.fromList $ outputVars backend))
    return (inp',outp')
  backendVerify _ backend cy contr locals inits consts opts name = do
    let ba = gtl2ba (Just cy) (foldl1 gand contr)
        dfa = determinizeBA ba
        dfa' = fmap renameDFAStates dfa
    --print ba
    --print dfa
    case dfa' of
      Nothing -> putStrLn "Could not transform Buchi automaton into deterministic automaton" >> return Nothing
      Just ddfa -> do
        let (var_head,var_body) = variableManagement (\tp -> "undef_"++show (pretty tp)++"()") (inputVars backend)
            (shead,sbody) = buildStepFunction (stateName backend) (initName backend) (stepName backend) (fmap fst $ inputVars backend)
            (vhead,vbody) = buildVerificationFunction ddfa
            
            fun = unlines ([ "#include \""++h++"\"" | h <- headerFiles backend ]++
                           ["void verify() {"]++
                           (fmap ("  "++) (concat [var_head,shead,vhead]))++
                           ["  while(1) {"]++
                           (fmap ("    "++) (concat [var_body,sbody,vbody]))++
                           ["  }"
                           ,"}"])
        putStrLn fun
        return Nothing
    return Nothing

stateVarName :: String
stateVarName = "__st"

inputVarName :: String -> String
inputVarName name = "__in_"++name

variableManagement :: (Type -> String) -> [(String,Type)] -> ([String],[String])
variableManagement undef inps
  = ([ show (pretty tp) ++ " " ++ inputVarName name ++ ";" | (name,tp) <- inps ],
     [ inputVarName name ++ " = " ++ undef tp ++ ";" | (name,tp) <- inps ])

buildStepFunction :: String -> String -> String -> [String] -> ([String],[String])
buildStepFunction st init step inps
  = ([st++" "++stateVarName++";"
     ,init++"(&"++stateVarName++");"],
     [step++"("++concat (fmap (\inp -> inp++",") inps)++"&"++stateVarName++");"]
    )

buildVerificationFunction :: DFA [TypedExpr String] Integer -> ([String],[String])
buildVerificationFunction dfa = (["int __vst = "++show (dfaInit dfa)++";"],
                                 ["switch(__vst) {"]++
                                 (concat [ ["case "++show st++":"]++
                                           buildIfCase trans++
                                           ["  break;"]
                                         | (st,trans) <- Map.toList (unTotal $ dfaTransitions dfa)
                                         ])++
                                 ["}"])
  where
    buildIfCase [] = ["  {","    assert(0);","  }"]
    buildIfCase ((cond,trg):cases) = ["  if("++translateExpr (foldl1 gand cond)++") {"
                                     ,"    __vst = "++show trg++";"
                                     ,"  } else"]++buildIfCase cases
    
    translateExpr e = case getValue $ unfix e of
      Var name 0 Input -> inputVarName name
      Var name 0 Output -> stateVarName++"."++name
      Var name lvl Input -> "__in_"++name++"_"++show lvl
      Var name lvl Output -> "__out_"++name++"_"++show lvl
      Value v -> case v of
        GTLIntVal x -> show x
        GTLByteVal x -> show x
        GTLBoolVal x -> if x then "1" else "0"
        GTLFloatVal x -> show x
        GTLEnumVal x -> x
      BinBoolExpr And lhs rhs -> "("++translateExpr lhs++" && "++translateExpr rhs++")"
      BinBoolExpr Or lhs rhs -> "("++translateExpr lhs++" || "++translateExpr rhs++")"
      BinBoolExpr Implies lhs rhs -> "(!"++translateExpr lhs++" || "++translateExpr rhs++")"
      BinRelExpr rel lhs rhs -> "("++translateExpr lhs++(case rel of
                                                            BinLT -> " < "
                                                            BinLTEq -> " <= "
                                                            BinGT -> " > "
                                                            BinGTEq -> " >= "
                                                            BinEq -> " == "
                                                            BinNEq -> " != ")++translateExpr rhs++")"
      UnBoolExpr Not e -> "!"++translateExpr e

splitLast :: [a] -> ([a],a)
splitLast [] = error "splitLast applied to empty list."
splitLast [x] = ([],x)
splitLast (x:xs) = let (ys,y) = splitLast xs
                   in (x:ys,y)
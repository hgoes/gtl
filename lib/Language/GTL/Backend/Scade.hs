{-# LANGUAGE TypeFamilies #-}
module Language.GTL.Backend.Scade where

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import Language.GTL.Backend
import qualified Language.Scade.Syntax as Sc
import Language.GTL.Syntax
import Data.Map as Map
import Data.Typeable

data Scade = Scade deriving (Show)

instance GTLBackend Scade where
  data GTLBackendData Scade = ScadeData String [Sc.Declaration]
  backendName Scade = "scade"
  initBackend Scade [file,name] = do
    str <- readFile file
    return $ ScadeData name (scade $ alexScanTokens str)
  typeCheckInterface Scade (ScadeData name decls) ins outs = do
    let (sc_ins,sc_outs) = scadeInterface name decls
    mp_ins <- scadeTypeMap sc_ins
    mp_outs <- scadeTypeMap sc_outs
    rins <- mergeTypes ins mp_ins
    routs <- mergeTypes outs mp_outs
    return (rins,routs)
  cInterface Scade (ScadeData name decls) = let (inp,outp) = scadeInterface name decls
                                            in CInterface { cIFaceIncludes = [name++".h"]
                                                          , cIFaceStateType = ["outC_"++name]
                                                          , cIFaceInputType = if Prelude.null inp
                                                                              then []
                                                                              else ["inC_"++name]
                                                          , cIFaceStateInit = \[st] -> name++"_reset(&("++st++"))"
                                                          , cIFaceIterate = \[st] inp -> case inp of
                                                               [] -> name++"(&("++st++"))"
                                                               [rinp] -> name++"(&("++rinp++"),&("++st++"))"
                                                          , cIFaceGetInputVar = \[inp] var -> inp++"."++var
                                                          , cIFaceGetOutputVar = \[st] var -> st++"."++var
                                                          , cIFaceTranslateType = scadeTranslateTypeC
                                                          }

scadeTranslateTypeC :: TypeRep -> String
scadeTranslateTypeC rep
  | rep == typeOf (undefined::Int) = "kcg_int"
  | rep == typeOf (undefined::Bool) = "kcg_bool"
  | otherwise = error $ "Couldn't translate "++show rep++" to C-type"

scadeTypeToGTL :: Sc.TypeExpr -> Maybe TypeRep
scadeTypeToGTL Sc.TypeInt = Just (typeOf (undefined::Int))
scadeTypeToGTL Sc.TypeBool = Just (typeOf (undefined::Bool))
scadeTypeToGTL _ = Nothing

scadeTypeMap :: [(String,Sc.TypeExpr)] -> Either String (Map String TypeRep)
scadeTypeMap tps = do
  res <- mapM (\(name,expr) -> case scadeTypeToGTL expr of
                  Nothing -> Left $ "Couldn't convert SCADE type "++show expr++" to GTL"
                  Just tp -> Right (name,tp)) tps
  return $ Map.fromList res

-- | Extract type information from a SCADE model.
--   Returns two list of variable-type pairs, one for the input variables, one for the outputs.
scadeInterface :: String -- ^ The name of the Scade model to analyze
                  -> [Sc.Declaration] -- ^ The parsed source code
                  -> ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)])
scadeInterface name (op@(Sc.UserOpDecl {}):xs)
  | Sc.userOpName op == name = (varNames' (Sc.userOpParams op),varNames' (Sc.userOpReturns op))
  | otherwise = scadeInterface name xs
    where
      varNames' :: [Sc.VarDecl] -> [(String,Sc.TypeExpr)]
      varNames' (x:xs) = (fmap (\var -> (Sc.name var,Sc.varType x)) (Sc.varNames x)) ++ varNames' xs
      varNames' [] = []
scadeInterface name (_:xs) = scadeInterface name xs
scadeInterface name [] = error $ "Couldn't find model "++show name

module Language.GTL.ScadeAnalyzer where

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import qualified Language.Scade.Syntax as Sc
import Language.GTL.Syntax

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

type TypeMap = Map String (String,Map String Sc.TypeExpr,Map String Sc.TypeExpr)

analyzeScadeModel :: FilePath -> String -> IO ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)])
analyzeScadeModel fp name = fmap (scadeInterface name) (parseScade fp)

parseScade :: FilePath -> IO [Sc.Declaration]
parseScade fp = do
  str <- readFile fp
  return $ scade $ alexScanTokens str

scadeInterface :: String -> [Sc.Declaration] -> ([(String,Sc.TypeExpr)],[(String,Sc.TypeExpr)])
scadeInterface name (op@(Sc.UserOpDecl {}):xs)
  | Sc.userOpName op == name = (varNames' (Sc.userOpParams op),varNames' (Sc.userOpReturns op))
  | otherwise = scadeInterface name xs
scadeInterface name (_:xs) = scadeInterface name xs
scadeInterface name [] = error $ "Couldn't find model "++show name

varNames' :: [Sc.VarDecl] -> [(String,Sc.TypeExpr)]
varNames' (x:xs) = (fmap (\var -> (Sc.name var,Sc.varType x)) (Sc.varNames x)) ++ varNames' xs
varNames' [] = []

typeMap :: [Declaration] -> [Sc.Declaration] -> TypeMap
typeMap def scade = Map.fromList $
                    mapMaybe (\decl -> case decl of
                                 Connect _ -> Nothing
                                 Verify _ -> Nothing
                                 Model mdl -> Just (modelName mdl,let (inp,outp) = scadeInterface ((modelArgs mdl)!!0) scade
                                                                  in ((modelArgs mdl)!!0,Map.fromList inp,Map.fromList outp))) def
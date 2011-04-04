{-| Helper module to extract type informations from SCADE models
 -}
module Language.GTL.ScadeAnalyzer(
  TypeMap,
  parseScade,
  scadeInterface,
  typeMap
  ) where

import Language.Scade.Lexer (alexScanTokens)
import Language.Scade.Parser (scade)
import qualified Language.Scade.Syntax as Sc
import Language.GTL.Syntax

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

type TypeMap = Map String (String,Map String Sc.TypeExpr,Map String Sc.TypeExpr)

-- | Parse a SCADE file.
parseScade :: FilePath -> IO [Sc.Declaration]
parseScade fp = do
  str <- readFile fp
  return $ scade $ alexScanTokens str

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

-- | Build a mapping of all models to their interface type informations for a given GTL file.
typeMap :: [Declaration] -- ^ The contents of a GTL file
           -> [Sc.Declaration] -- ^ A scade file
           -> TypeMap
typeMap def scade = Map.fromList $
                    mapMaybe (\decl -> case decl of
                                 Connect _ -> Nothing
                                 Verify _ -> Nothing
                                 Model mdl -> Just (modelName mdl,let (inp,outp) = scadeInterface ((modelArgs mdl)!!0) scade
                                                                  in ((modelArgs mdl)!!0,Map.fromList inp,Map.fromList outp))) def
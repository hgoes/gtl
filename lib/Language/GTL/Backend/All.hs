{-# LANGUAGE TypeFamilies,RankNTypes,ImpredicativeTypes #-}
module Language.GTL.Backend.All where

import Language.GTL.Syntax
import Language.GTL.Backend
import Language.GTL.Backend.Scade
import Data.Map as Map

data AllBackend = AllBackend
                  { allTypecheck :: Map String GTLType -> Map String GTLType -> Either String (Map String GTLType,Map String GTLType)
                  }

initAllBackend :: String -> [String] -> IO (Maybe AllBackend)
initAllBackend name args
  | backendName Scade == name = do
    dat <- initBackend Scade args
    return $ Just $ AllBackend 
      { allTypecheck = typeCheckInterface Scade dat
      }
  | otherwise = return Nothing
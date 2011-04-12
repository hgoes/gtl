{-# LANGUAGE TypeFamilies,RankNTypes,ImpredicativeTypes #-}
module Language.GTL.Backend.All where

import Language.GTL.Expression
import Language.GTL.Backend
import Language.GTL.Backend.Scade
import Data.Map as Map
import Data.Typeable

data AllBackend = AllBackend
                  { allTypecheck :: ModelInterface -> Either String ModelInterface
                  , allCInterface :: CInterface
                  , allVerifyLocal :: Expr String Bool -> IO (Maybe Bool)
                  }

initAllBackend :: String -> [String] -> IO (Maybe AllBackend)
initAllBackend name args
  | backendName Scade == name = do
    dat <- initBackend Scade args
    return $ Just $ AllBackend 
      { allTypecheck = typeCheckInterface Scade dat
      , allCInterface = cInterface Scade dat
      , allVerifyLocal = backendVerify Scade dat
      }
  | otherwise = return Nothing
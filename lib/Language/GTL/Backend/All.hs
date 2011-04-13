{-# LANGUAGE TypeFamilies,RankNTypes,ImpredicativeTypes #-}
{-| Provides a common interface for all backend types.
 -}
module Language.GTL.Backend.All where

import Language.GTL.Expression
import Language.GTL.Backend
import Language.GTL.Backend.Scade
import Data.Map as Map
import Data.Typeable

-- | Essentially a `GTLBackend' with the parameters instantiated, thus eliminating
--   the type variable.
data AllBackend = AllBackend
                  { allTypecheck :: ModelInterface -> Either String ModelInterface
                  , allCInterface :: CInterface
                  , allVerifyLocal :: Expr String Bool -> IO (Maybe Bool)
                  }

-- | Try to initialize the correct backend for a given backend name and arguments.
initAllBackend :: String -- ^ The name of the backend
                  -> [String] -- ^ The arguments with which to initialize the backend
                  -> IO (Maybe AllBackend)
initAllBackend name args
  | backendName Scade == name = do
    dat <- initBackend Scade args
    return $ Just $ AllBackend 
      { allTypecheck = typeCheckInterface Scade dat
      , allCInterface = cInterface Scade dat
      , allVerifyLocal = backendVerify Scade dat
      }
  | otherwise = return Nothing
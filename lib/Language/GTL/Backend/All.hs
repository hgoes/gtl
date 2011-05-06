{-# LANGUAGE TypeFamilies,RankNTypes,ImpredicativeTypes #-}
{-| Provides a common interface for all backend types.
 -}
module Language.GTL.Backend.All where

import Language.GTL.Expression
import Language.GTL.Backend
import Language.GTL.Backend.Scade
import Language.GTL.Backend.None
import Data.Map as Map
import Data.Typeable

-- | Essentially a `GTLBackend' with the parameters instantiated, thus eliminating
--   the type variable.
data AllBackend = AllBackend
                  { allTypecheck :: ModelInterface -> Either String ModelInterface
                  , allCInterface :: CInterface
                  , allVerifyLocal :: Expr String Bool -> IO (Maybe Bool)
                  }

tryInit :: GTLBackend b => b -> String -> [String] -> IO (Maybe AllBackend)
tryInit be name args
  | backendName be == name = do
    dat <- initBackend be args
    return $ Just $ AllBackend
      { allTypecheck = typeCheckInterface be dat
      , allCInterface = cInterface be dat
      , allVerifyLocal = backendVerify be dat
      }
  | otherwise = return Nothing

firstM :: Monad m => [x -> y -> m (Maybe a)] -> x -> y -> m (Maybe a)
firstM (x:xs) p q = do
  r <- x p q
  case r of
    Nothing -> firstM xs p q
    Just rr -> return (Just rr)
firstM [] _ _ = return Nothing

-- | Try to initialize the correct backend for a given backend name and arguments.
initAllBackend :: String -- ^ The name of the backend
                  -> [String] -- ^ The arguments with which to initialize the backend
                  -> IO (Maybe AllBackend)
initAllBackend = firstM [tryInit Scade,tryInit None]

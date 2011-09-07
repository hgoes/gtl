{-# LANGUAGE TypeFamilies,RankNTypes,ImpredicativeTypes #-}
{-| Provides a common interface for all backend types.
 -}
module Language.GTL.Backend.All where

import Language.GTL.Expression
import Language.GTL.Backend
import Language.GTL.Backend.Scade
import Language.GTL.Backend.None

import Misc.ProgramOptions as Opts

-- | Essentially a `GTLBackend' with the parameters instantiated, thus eliminating
--   the type variable.
data AllBackend = AllBackend
                  { allTypecheck :: ModelInterface -> Either String ModelInterface
                  , allCInterface :: CInterface
                  , allVerifyLocal :: Integer -> TypedExpr String -> Opts.Options -> String -> IO (Maybe Bool)
                  }

-- | Try to initialize a given backend with a name and arguments.
--   If it works, it'll return Just with the 'AllBackend' representation.
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

-- | Returns the first result that is not 'Nothing' from a list of functions
--   by applying the arguments to them.
firstM :: Monad m => [x -> y -> m (Maybe a)] -> x -> y -> m (Maybe a)
firstM (x:xs) p q = do
  res <- x p q
  case res of
    Nothing -> firstM xs p q
    Just rr -> return (Just rr)
firstM [] _ _ = return Nothing

-- | Try to initialize the correct backend for a given backend name and arguments.
initAllBackend :: String -- ^ The name of the backend
                  -> [String] -- ^ The arguments with which to initialize the backend
                  -> IO (Maybe AllBackend)
initAllBackend = firstM [tryInit Scade,tryInit None]

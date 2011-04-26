{-# LANGUAGE ScopedTypeVariables #-}
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.PackageDescription
import Data.Version

import Prelude hiding (catch)
import Control.Exception
import System.Process

import Data.Time
import System.Locale
import Data.Maybe

buildEnvHook :: UserHooks -> UserHooks
buildEnvHook hooks = hooks
  { confHook = \args flags -> do
       bi <- confHook hooks args flags
       tag <- catch (do
                        v <- readProcess "git" ["log"] ""
                        let rvers = case lines v of
                              [] -> Nothing
                              (x:xs) -> case words x of
                                ["commit",rv] -> Just rv
                                _ -> Nothing
                        return rvers
                    ) (\(e::IOException) -> return Nothing)
       branch <- catch getBranch (\(e::IOException) -> return Nothing)
       time <- getCurrentTime
       let time_str = formatTime defaultTimeLocale "%c" time
       let nbi = bi { localPkgDescr = addCppOptsPD (["-DBUILD_VERSION="++show (extractVersion bi)]++
                                                    (case tag of
                                                        Nothing -> []
                                                        Just rtag -> ["-DBUILD_TAG="++show rtag])++
                                                    (case branch of
                                                        Nothing -> []
                                                        Just rbranch -> ["-DBUILD_BRANCH="++show rbranch])++
                                                    ["-DBUILD_DATE="++show time_str])
                                      (localPkgDescr bi) }
       return nbi
  }

extractVersion :: LocalBuildInfo -> String
extractVersion bi = showVersion $ pkgVersion $ package $ localPkgDescr bi

addCppOptsPD :: [String] -> PackageDescription -> PackageDescription
addCppOptsPD opt pd = pd { library = fmap (\lib -> lib { libBuildInfo = addCppOptsBI opt (libBuildInfo lib) }) (library pd)
                         , executables = fmap (\exec -> exec { buildInfo = addCppOptsBI opt (buildInfo exec)
                                                             }) (executables pd)
                         }

addCppOptsBI opt bi = bi { cppOptions = opt++(cppOptions bi) }

getBranch :: IO (Maybe String)
getBranch = do
  str <- readProcess "git" ["branch"] ""
  case mapMaybe (\ln -> case ln of
                    '*':' ':name -> Just name
                    _ -> Nothing) (lines str) of
    [branch] -> return $ Just branch
    _ -> return Nothing

main = defaultMainWithHooks $ buildEnvHook simpleUserHooks
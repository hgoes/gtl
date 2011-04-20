{-# LANGUAGE ScopedTypeVariables #-}
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.PackageDescription

import Prelude hiding (catch)
import Control.Exception
import System.Process

import Data.Time
import System.Locale

buildEnvHook :: UserHooks -> UserHooks
buildEnvHook hooks = hooks
  { confHook = \args flags -> do
       bi <- confHook hooks args flags
       vers <- catch (do
                         v <- readProcess "git" ["log"] ""
                         let rvers = case lines v of
                               [] -> "unknown version"
                               (x:xs) -> case words x of
                                 ["commit",rv] -> rv
                                 _ -> "unknown version"
                         return rvers
                     ) (\(e::IOException) -> return "unknown version")
       time <- getCurrentTime
       let time_str = formatTime defaultTimeLocale "%c" time
       let nbi = bi { localPkgDescr = addCppOptsPD ["-DBUILD_VERSION="++show vers
                                                   ,"-DBUILD_DATE="++show time_str
                                                   ] (localPkgDescr bi) }
       return nbi
  }


addCppOptsPD :: [String] -> PackageDescription -> PackageDescription
addCppOptsPD opt pd = pd { library = fmap (\lib -> lib { libBuildInfo = addCppOptsBI opt (libBuildInfo lib) }) (library pd)
                         , executables = fmap (\exec -> exec { buildInfo = addCppOptsBI opt (buildInfo exec)
                                                             }) (executables pd)
                         }

addCppOptsBI opt bi = bi { cppOptions = opt++(cppOptions bi) }

main = defaultMainWithHooks $ buildEnvHook simpleUserHooks
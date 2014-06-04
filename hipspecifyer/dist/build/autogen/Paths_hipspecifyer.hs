module Paths_hipspecifyer (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [1], versionTags = []}
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/moajohansson/Library/Haskell/ghc-7.6.3/lib/hipspecifyer-1/bin"
libdir     = "/Users/moajohansson/Library/Haskell/ghc-7.6.3/lib/hipspecifyer-1/lib"
datadir    = "/Users/moajohansson/Library/Haskell/ghc-7.6.3/lib/hipspecifyer-1/share"
libexecdir = "/Users/moajohansson/Library/Haskell/ghc-7.6.3/lib/hipspecifyer-1/libexec"
sysconfdir = "/Users/moajohansson/Library/Haskell/ghc-7.6.3/lib/hipspecifyer-1/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "hipspecifyer_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "hipspecifyer_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "hipspecifyer_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "hipspecifyer_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "hipspecifyer_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)

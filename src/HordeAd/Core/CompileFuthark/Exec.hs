{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module HordeAd.Core.CompileFuthark.Exec (
  KernelLib,
  buildKernel,
  callKernelFun,
) where

import Prelude

import Control.Exception (finally, onException)
import Control.Monad (when)
import Data.ByteString.Lazy qualified as Lazy
import Data.ByteString.Lazy.Char8 qualified as Lazy8
import Data.IORef
import Foreign (Ptr)
import Foreign.Ptr (FunPtr)
import GHC.IO.Exception (IOErrorType(OtherError))
import System.Directory (removeDirectoryRecursive)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.IO (hPutStr, hPutStrLn, stderr)
import System.IO.Error (mkIOError)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.DynamicLinker
import System.Posix.Temp (mkdtemp)
import System.Process


debugProcs :: Bool; debugProcs = toEnum 1  -- print what commands are run
debugLibLoad :: Bool; debugLibLoad = toEnum 1  -- print when libraries are loaded/unloaded
debugSources :: Bool; debugSources = toEnum 1  -- print compiled Futhark and C sources

-- The IORef wrapper is required for the finalizer to attach properly (see the 'Weak' docs)
data KernelLib = KernelLib !(IORef (FunPtr (Ptr () -> IO ())))

buildKernel :: Lazy.ByteString -> Lazy.ByteString -> String -> IO KernelLib
buildKernel futsource csource funname = do
  template <- (++ "/tmp.hordead.") <$> getTempDir
  path <- mkdtemp template

  when debugSources $ do
    hPutStrLn stderr $ "[horde-ad] Compiling Futhark source:"
    hPutStr stderr $ lineNumbers $ Lazy8.unpack futsource
    hPutStrLn stderr $ "[horde-ad] Compiling C wrapper source:"
    hPutStr stderr $ lineNumbers $ Lazy8.unpack csource

  let run progname args = do
        let printedCmd = progname ++ concatMap ((' ' :) . show) args
        when debugProcs $ hPutStrLn stderr $ "[horde-ad] Running: " ++ printedCmd
        withCreateProcess (proc progname args) { cwd = Just path } $ \cases
          Nothing Nothing Nothing ph ->
            waitForProcess ph >>= \case
              ExitSuccess -> return ()
              ExitFailure code ->
                ioError (mkIOError OtherError ("horde-ad: Failed to call (exit code " ++
                                                 show code ++ "): " ++ printedCmd)
                                   Nothing Nothing)
          _ _ _ _ -> error "impossible"

  dl <- flip finally (removeDirectoryRecursive path) $ do
    Lazy.writeFile (path ++ "/prog.fut") futsource
    run "futhark" ["c", "--library", "prog.fut"]

    Lazy.writeFile (path ++ "/wrapper.c") csource
    run "cc" ["-O3", "-march=native", "-std=c99", "-shared", "-fPIC", "prog.c", "wrapper.c", "-o", "out.so"]

    dl <- dlopen (path ++ "/out.so") [RTLD_LAZY, RTLD_LOCAL]
    when debugLibLoad $ do
      numLoaded <- atomicModifyIORef' numLoadedCounter (\n -> (n + 1, n + 1))
      hPutStrLn stderr $ "[horde-ad] loaded kernel " ++ path ++ " (" ++ show numLoaded ++ " total)"
    return dl

  -- note that it's okay to remove the directory at this point, because we already have the .so open

  let unload = do when debugLibLoad $ do
                    numLeft <- atomicModifyIORef' numLoadedCounter (\n -> (n-1, n-1))
                    hPutStrLn stderr $ "[horde-ad] unloading kernel " ++ path ++ " (" ++ show numLeft ++ " left)"
                  dlclose dl
  ref <- onException (newIORef =<< dlsym dl funname) unload
  _ <- mkWeakIORef ref unload
  return (KernelLib ref)

foreign import ccall "dynamic"
  wrapKernelFun :: FunPtr (Ptr () -> IO ()) -> Ptr () -> IO ()

-- Ensure that keeping a reference to the returned function also keeps the 'KernelLib' alive
{-# NOINLINE callKernelFun #-}
callKernelFun :: KernelLib -> Ptr () -> IO ()
callKernelFun (KernelLib ref) arg = do
  ptr <- readIORef ref
  wrapKernelFun ptr arg

getTempDir :: IO FilePath
getTempDir =
  lookupEnv "TMPDIR" >>= \case
    Just s | not (null s) -> return s
    _ -> return "/tmp"

-- This counter is only used for the debug messages.
{-# NOINLINE numLoadedCounter #-}
numLoadedCounter :: IORef Int
numLoadedCounter = unsafePerformIO $ newIORef 0

lineNumbers :: String -> String
lineNumbers str =
  let lns = lines str
      numlines = length lns
      width = length (show numlines)
      pad s = replicate (width - length s) ' ' ++ s
  in unlines (zipWith (\i ln -> pad (show i) ++ " | " ++ ln) [1::Int ..] lns)

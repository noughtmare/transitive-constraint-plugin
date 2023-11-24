module TransitiveConstraintPlugin (plugin) where

-- import Debug.Trace

import Control.Concurrent
import Control.Monad (guard)
import Data.Traversable (for)
import GHC.Core.Class (Class)
import GHC.Core.InstEnv
import GHC.Iface.Load (loadModuleInterface)
import GHC.IfaceToCore (tcIfaceInst)
import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (initIfaceLcl, initIfaceTcRn)
import System.IO.Unsafe (unsafePerformIO)
import GHC.Tc.Utils.TcType (eqType)

import Sub ()
import SubTrans ()

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = \_ -> Just myTcPlugin
    }

-- When we are running under HLS the initialization might run multiple times
-- and that doesn't seem to work well with the interface loading hack I'm using.
-- So I'm using this global state to persist the loading of the interface.
globalState :: MVar (Class, ClsInst, ClsInst)
globalState = unsafePerformIO newEmptyMVar
{-# NOINLINE globalState #-}

myTcPlugin :: GHC.Tc.Types.TcPlugin
myTcPlugin =
  TcPlugin
    { tcPluginInit = do
        gs <- tcPluginIO (tryReadMVar globalState)
        case gs of
          Nothing -> do
            tr <- findImportedModule (mkModuleName "Sub") NoPkgQual
            tr' <- findImportedModule (mkModuleName "SubTrans") NoPkgQual
            case (tr, tr') of
              (Found _ md, Found _ md') -> do
                clsNm <- lookupOrig md (mkOccName clsName "<=")
                cls <- tcLookupClass clsNm
                iface <- unsafeTcPluginTcM (loadModuleInterface (text "here") md')
                insts <- unsafeTcPluginTcM $ initIfaceTcRn $ initIfaceLcl md' (text "here") NotBoot $ traverse tcIfaceInst $ mi_insts iface
                case insts of
                  [instf, instfgh] -> do
                    let res = (cls, instf, instfgh)
                    _ <- tcPluginIO $ tryPutMVar globalState res
                    pure res
                  _ -> error "failed to find instances"
              _ -> error "failed to find modules"
          Just gs' -> pure gs',
      tcPluginSolve = myTcPluginSolver,
      tcPluginRewrite = const emptyUFM,
      tcPluginStop = const (pure ())
    }

newtype Result = Result {getResult :: TcPluginSolveResult}

instance Semigroup Result where
  Result (TcPluginSolveResult x1 y1 z1) <> Result (TcPluginSolveResult x2 y2 z2) =
    Result (TcPluginSolveResult (x1 ++ x2) (y1 ++ y2) (z1 ++ z2))

instance Monoid Result where
  mempty = Result (TcPluginSolveResult [] [] [])

evTermExpr :: EvTerm -> EvExpr
evTermExpr (EvExpr x) = x
evTermExpr _ = error "This EvTerm is not an EvExpr"

myTcPluginSolver ::
  (Class, ClsInst, ClsInst) ->
  EvBindsVar ->
  [Ct] -> -- Givens
  [Ct] -> -- Wanteds
  TcPluginM TcPluginSolveResult
myTcPluginSolver _ _ _ [] = pure (getResult mempty)
myTcPluginSolver (cls, instf, instfgh) _evb givens wanteds = do
  -- traceM (showSDocUnsafe (ppr (cls, instf, instfgh, givens, wanteds)))

  fmap (getResult . mconcat) . for wanteds $ \ct -> do
    case ct of
      CDictCan{} | cc_class ct == cls, [x,y] <- cc_tyargs ct ->
        case go (evDFunApp (instanceDFunId instf) [y] []) x y y of
          [] -> pure (Result (TcPluginContradiction [ct]))
          (ev : _) -> pure (Result (TcPluginOk [(ev, ct)] []))
      _ -> pure (Result (TcPluginOk [] []))
  where
    go :: EvTerm -> PredType -> PredType -> PredType -> [EvTerm]
    go ev x v y
      | eqType x v = [ev]
      | otherwise = do
          ct <- clsGivens
          [x', y'] <- pure (cc_tyargs ct)
          guard (eqType y' v)
          go (evDFunApp (instanceDFunId instfgh) [x', y', y] [ctEvExpr (ctEvidence ct), evTermExpr ev]) x x' y
    clsGivens = [ct | ct@CDictCan{} <- givens, cc_class ct == cls, [_,_] <- pure (cc_tyargs ct)]


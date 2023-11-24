module TransitiveConstraintPlugin (plugin) where

import Debug.Trace

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
import qualified Data.List as List

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = \_ -> Just transitiveConstraintPlugin
    }

transitiveConstraintPlugin :: GHC.Tc.Types.TcPlugin
transitiveConstraintPlugin =
  TcPlugin
    { tcPluginInit = do
        tr <- findImportedModule (mkModuleName "Sub") NoPkgQual
        case tr of
          Found _ md -> do
            clsNm <- lookupOrig md (mkOccName clsName "<=")
            cls <- tcLookupClass clsNm
            InstEnvs gbl _ _ <- getInstEnvs
            case filter ((== cls) . is_cls) (instEnvElts gbl) of
              [trans, refl] -> pure (cls, refl, trans)
              _ -> error "TransitiveConstraintPlugin: failed to find instances"
          _ -> error "TransitiveConstraintPlugin: failed to find 'Sub' module"
    , tcPluginSolve = transitiveConstraintSolver
    , tcPluginRewrite = const emptyUFM
    , tcPluginStop = const (pure ())
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

transitiveConstraintSolver ::
  (Class, ClsInst, ClsInst) ->
  EvBindsVar ->
  [Ct] -> -- Givens
  [Ct] -> -- Wanteds
  TcPluginM TcPluginSolveResult
transitiveConstraintSolver _ _ _ [] = pure (getResult mempty)
transitiveConstraintSolver (cls, refl, trans) _evb givens wanteds = do
  fmap (getResult . mconcat) . for wanteds $ \ct -> do
    traceM ("clsGivens: " ++ showSDocUnsafe (ppr clsGivens))
    case ct of
      CDictCan{} | cc_class ct == cls, [x,y] <- cc_tyargs ct -> do
        case go (evDFunApp (instanceDFunId refl) [y] []) x y y of
          [] -> do
            traceM ("contradiction: " ++ showSDocUnsafe (ppr ct))
            pure (Result (TcPluginContradiction [ct]))
          (ev : _) -> do
            traceM ("Ok: " ++ showSDocUnsafe (ppr (ev, ct)))
            pure (Result (TcPluginOk [(ev, ct)] []))
      _ -> pure (Result (TcPluginOk [] []))
  where
    go :: EvTerm -> PredType -> PredType -> PredType -> [EvTerm]
    go ev x v y
      | eqType x v = [ev]
      | otherwise = do
          ct <- clsGivens
          [x', y'] <- pure (cc_tyargs ct)
          guard (eqType y' v)
          go (evDFunApp (instanceDFunId trans) [x', y', y] [ctEvExpr (ctEvidence ct), evTermExpr ev]) x x' y
    clsGivens = [ct | ct@CDictCan{} <- givens, cc_class ct == cls, [_,_] <- pure (cc_tyargs ct)]


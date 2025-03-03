module TransitiveConstraintPlugin (plugin) where

import Debug.Trace

import qualified GHC.Iface.Load
-- import Control.Concurrent
import Control.Monad (guard)
import GHC.Core.Class (Class)
import GHC.Core.InstEnv
import GHC.Plugins
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.TcType (eqType)

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = const $ Just $
      TcPlugin
        { tcPluginInit = do
            tr <- findImportedModule (mkModuleName "Sub") NoPkgQual
            case tr of
              Found _ md -> do
                cls <- tcLookupClass =<< lookupOrig md (mkOccName clsName "<=")
                tr2 <- findImportedModule (mkModuleName "SubInstances") NoPkgQual
                case tr2 of
                  Found _ md2 -> do
                    _ <- unsafeTcPluginTcM (GHC.Iface.Load.loadModuleInterface (text "Needed for refl and trans instances") md2)
                    InstEnvs gbl _ _ <- getInstEnvs
                    case filter ((== cls) . is_cls) (instEnvElts gbl) of
                      [trans, refl] -> pure (cls, refl, trans)
                      _ -> error "TransitiveConstraintPlugin: failed to find instances"
                  _ -> error "TransitiveConstraintPlugin: failed to find 'SubInstances' module"
              _ -> error "TransitiveConstraintPlugin: failed to find 'Sub' module"
        , tcPluginSolve = \info evb gs ws -> pure (getResult (solver info evb gs ws))
        , tcPluginRewrite = const emptyUFM
        , tcPluginStop = const (pure ())
        }
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

solver ::
  (Class, ClsInst, ClsInst) ->
  EvBindsVar ->
  [Ct] -> -- Givens
  [Ct] -> -- Wanteds
  Result
solver (cls, refl, trans) _evb givens =
  foldMap $ \ct ->
    -- trace ("clsGivens: " ++ showSDocUnsafe (ppr clsGivens)) $
    case ct of
      CDictCan{} | cc_class ct == cls, [k,x,y] <- cc_tyargs ct ->
        case go (evDFunApp (instanceDFunId refl) [k,y] []) x y y of
          [] ->
            -- trace ("contradiction: " ++ showSDocUnsafe (ppr ct)) $
            Result (TcPluginContradiction [ct])
          (ev : _) ->
            -- trace ("Ok: " ++ showSDocUnsafe (ppr (ev, ct))) $
            Result (TcPluginOk [(ev, ct)] [])
      _ -> Result (TcPluginOk [] [])
  where
    go :: EvTerm -> PredType -> PredType -> PredType -> [EvTerm]
    go ev x v y
      | eqType x v = [ev]
      | otherwise = do
          ct <- clsGivens
          [k, x', y'] <- pure (cc_tyargs ct)
          guard (eqType y' v)
          go (evDFunApp (instanceDFunId trans) [k, x', y', y] [ctEvExpr (ctEvidence ct), evTermExpr ev]) x x' y
    clsGivens = [ct | ct@CDictCan{} <- givens, cc_class ct == cls, [_,_,_] <- pure (cc_tyargs ct)]

-- TODO: If constraint could be solved by disambiguating one or more variables, then try to do that!
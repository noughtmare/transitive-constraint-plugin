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
import GHC.Tc.Utils.TcType (eqType)
import System.IO.Unsafe (unsafePerformIO)

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

  fmap (getResult . mconcat) . for wanteds $ \w -> do
    case w of
      CDictCan _ cls' [x, y] _ | cls' == cls ->
        case go (evDFunApp (instanceDFunId instf) [y] []) x y y of
          [] -> pure (Result (TcPluginContradiction [w]))
          (ev : _) -> pure (Result (TcPluginOk [(ev, w)] []))
      _ -> pure (Result (TcPluginOk [] []))
  where
    go :: EvTerm -> PredType -> PredType -> PredType -> [EvTerm]
    go ev x v y
      | eqType x v = [ev]
      | otherwise = do
          ct@(CDictCan _ _ [x', y'] _) <- clsGivens
          guard (eqType y' v)
          go (evDFunApp (instanceDFunId instfgh) [x', y', y] [ctEvExpr (ctEvidence ct), evTermExpr ev]) x x' y
    clsGivens = [c | c@(CDictCan _ cls' [_, _] _) <- givens, cls' == cls]

-- --     traceM (showSDocUnsafe (ppr (w, givens)))
-- --     case w of
-- --       CDictCan _ cls' [x, y] _
-- --         | cls' == cls
-- --         , Just g <- find (\ct -> cc_class ct == cls && eqType y (cc_tyargs ct !! 1)) givens
-- --         -> -- let x' = cc_tyargs g !! 0 in
-- --            traceM (showSDocUnsafe (ppr (evSelector injId [] []))) *>
-- --              undefined
-- --            -- ev <- newWanted _ (mkClassPred cls [x', y])
-- --            -- trace (showSDocUnsafe (ppr g)) undefined
-- --       _ -> pure mempty
--     -- let clsGivens = filter (\case CDictCan _ cls' [_, _] _ | cls' == cls -> True; _ -> False) givens
--     -- newCts <- go clsGivens [] clsGivens
--     -- traceM (showSDocUnsafe (ppr clsGivens))
--     -- pure (Result (TcPluginOk [] newCts))
--   where
--     go
--
-- --     go xs1 xsn (ct@(CDictCan cc_ev cc_class [arg1, arg2] cc_pend_sc):cts) = do
-- --       xsn' <- traverse (combine ct) (xs1 ++ xsn)
-- --       go xs1 (catMaybes xsn' ++ xsn) cts
-- --     go xs1 xsn (_:cts) = go xs1 xsn cts
-- --     go _ xs _ = pure xs
-- --
-- --     foo ct1 ct2 x y sc = do
-- --       (_, env) <- getEnvs
-- --       ev <-
-- --         newGiven
-- --           evb
-- --           ( CtLoc
-- --               AnnOrigin
-- --               env
-- --               (Just TypeLevel)
-- --               (bumpSubGoalDepth (maxSubGoalDepth (ctLocDepth (ctLoc ct1)) (ctLocDepth (ctLoc ct2))))
-- --           )
-- --           (mkClassPred cls [x, y])
-- --           (trace (showSDocUnsafe (ppr (mkEvScSelectors cls [x, y]))) undefined) -- inj ct1 . inj ct2
-- --       pure (CDictCan ev cls [x, y] sc)
-- --
-- --     combine
-- --       ct1@(CDictCan (CtGiven p1 e1 l1) _ [x1, y1] sc1)
-- --       ct2@(CDictCan (CtGiven p2 e2 l2) _ [x2, y2] sc2)
-- --         | eqType y1 x2 = Just <$> foo ct2 ct1 x1 y2 sc
-- --         | eqType y2 x1 = Just <$> foo ct1 ct2 x2 y1 sc
-- --         where
-- --           sc = if sc1 == sc2 then sc1 else error "cc_pend_sc not equal"
-- --     combine _ _ = pure Nothing

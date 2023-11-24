{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

import Data.Kind
import Sub
import Data.Proxy
import Prelude hiding ((>>=))

data Var env a where
  VZ :: Var (a : env) a
  VS :: Var env a -> Var (b : env) a

deriving instance Show (Var env a)

data Syn env a where
  SynVar :: Var env a -> Syn env a
  SynLam :: Syn (a : env) b -> Syn env (a -> b)
  SynApp :: Syn env (a -> b) -> Syn env a -> Syn env b

deriving instance Show (Syn env a)

data Sem u a where
  SemVar :: u a -> Sem u a
  SemLam :: (forall u'. (u <= u') => u' a -> Sem u' b) -> Sem u (a -> b)
  SemApp :: Sem u (a -> b) -> Sem u a -> Sem u b

injVar :: Spine pre -> Proxy x -> Proxy env -> Var (pre ++ env) a -> Var (pre ++ (x : env)) a
injVar SNil _ _ v = VS v
injVar (SCons s) px penv (VS v) = VS (injVar s px penv v)

instance Var env <= Var (x : env) where
  inj = injVar SNil Proxy Proxy

type family xs ++ ys where
  '[] ++ ys = ys
  (x : xs) ++ ys = x : (xs ++ ys)

data Spine xs where
  SNil :: Spine '[]
  SCons :: Spine xs -> Spine (x : xs)

injSyn :: Spine pre -> Proxy x -> Proxy env -> Syn (pre ++ env) a -> Syn (pre ++ (x : env)) a
injSyn s px penv (SynVar v) = SynVar (injVar s px penv v)
injSyn s px penv (SynLam bdy) = SynLam (injSyn (SCons s) px penv bdy)
injSyn s px penv (SynApp f x) = SynApp (injSyn s px penv f) (injSyn s px penv x)

instance Syn env <= Syn (x : env) where
  inj = injSyn SNil Proxy Proxy

synToSem :: Syn '[] a -> (forall u. Sem u a)
synToSem x0 = go (\case {}) x0
  where
    go :: (forall x. Var env x -> u x) -> Syn env a -> Sem u a
    go env (SynVar x) = SemVar (env x)
    go env (SynApp f x) = SemApp (go env f) (go env x)
    go env (SynLam bdy) = SemLam (\x -> go (\case VZ -> x; VS v -> inj (env v)) bdy)

semToSyn :: (forall u. Sem u a) -> Syn '[] a
semToSyn sem = go sem
  where
    go :: Sem (Var env) a -> Syn env a
    go (SemVar x) = SynVar x
    go (SemApp f x) = SynApp (go f) (go x)
    go (SemLam bdy) = SynLam (go (bdy VZ))

prog1 :: Sem u (b -> a -> b)
prog1 = SemLam (\x -> SemLam (\_ -> SemVar (inj x)))

λ, lam :: (forall u'. (u <= u') => (forall u''. (u' <= u'') => Sem u'' a) -> Sem u' b) -> Sem u (a -> b)
λ f = SemLam (\x -> f (SemVar (inj x)))
-- For those who don't have a Greek keyboard
lam f = λ f

infixl 1 $$
($$) :: Sem u (a -> b) -> Sem u a -> Sem u b
($$) = SemApp

prog2 :: Sem u ((b -> c) -> a -> b -> c)
prog2 = λ\ x -> λ\ _y -> λ\ z -> x $$ z

prog3 :: Sem u (a -> b -> b)
prog3 = (λ\ x -> λ\ _y -> x) $$ λ\ y -> y

-- Free

type SynFree :: ((Type -> Type) -> Type -> Type) -> [Type] -> Type -> Type
data SynFree f env a where
  SynPure :: Var env a -> SynFree f env a
  SynBind :: f (Var env) x -> SynFree f (x : env) a -> SynFree f env a

injSynFree :: HFunctor f => Spine pre -> Proxy x -> Proxy env -> SynFree f (pre ++ env) a -> SynFree f (pre ++ (x : env)) a
injSynFree s px penv (SynPure v) = SynPure (injVar s px penv v)
injSynFree s px penv (SynBind op k) = SynBind (hmap (injVar s px penv) op) (injSynFree (SCons s) px penv k)

-- I thought we could use this to implement bind in a syntax/semantics agnostic way.
-- You could write (forall m'. (m <= m') => ...)
-- That does work but you wouldn't be able to also weaken the u at the same time.
-- So, I don't think this approach really works for what I wanted to do with it.
instance HFunctor f => SynFree f env <= SynFree f (x : env) where
  inj = injSynFree SNil Proxy Proxy


newtype SynF f a = SynF (SynFree f '[] a)

type SemFree :: ((Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Type
data SemFree f u a where
  SemPure :: u a -> SemFree f u a
  SemBind :: f u x -> (forall u'. (u <= u') => u' x -> SemFree f u' a) -> SemFree f u a

(>>=) :: SemFree f u a -> (forall u'. u <= u' => (forall u''. u' <= u'' => u'' a) -> SemFree f u' b) -> SemFree f u b
SemPure x >>= k = k (inj x)
SemBind op k >>= k' = SemBind op (\x -> k (inj x) >>= k')

newtype SemF f a = SemF (forall u'. SemFree f u' a)

type HFunctor :: ((Type -> Type) -> Type -> Type) -> Constraint
class HFunctor h where
  hmap :: (forall x. f x -> g x) -> h f a -> h g a

synFToSemF :: HFunctor f => SynF f a -> SemF f a
synFToSemF (SynF x0) = SemF (go (\case {}) x0) where
  go :: HFunctor f => (forall x. Var env x -> u x) -> SynFree f env a -> SemFree f u a
  go env (SynPure x) = SemPure (env x)
  go env (SynBind op k) = SemBind (hmap env op) (\x -> go (\case VZ -> x; VS v -> inj (env v)) k)

semFToSynF :: SemF f a -> SynF f a
semFToSynF (SemF x0) = SynF (go x0) where
  go :: SemFree f (Var env) a -> SynFree f env a
  go (SemPure x) = SynPure x
  go (SemBind op k) = SynBind op (go (k VZ))

type OpTraverse :: (((Type -> Type) -> Type -> Type) -> Type -> Type) -> Constraint
class OpTraverse h where
  optraverse :: (Applicative m, HFunctor f, HFunctor g) => (forall u' x. f u' x -> m (g u' x)) -> h f a -> m (h g a)

instance OpTraverse SynF where
  optraverse f (SynF x) = SynF <$> syntraverse f x

syntraverse :: 
  (Applicative m, HFunctor f, HFunctor g) =>
  (forall u x. f u x -> m (g u x)) ->
  SynFree f env a -> m (SynFree g env a)
syntraverse _ (SynPure v) = pure (SynPure v)
syntraverse f (SynBind op k) = SynBind <$> f op <*> syntraverse f k

instance OpTraverse SemF where
  optraverse f = fmap synFToSemF . optraverse f . semFToSynF

-- Hefty

-- Put :: Int -> M ()
-- Get :: M Int

-- State  = Int :-> Ret () :+: Ret Int
-- Nondet = M a :-> M a :-> M a
-- Except = 

type SynHefty :: (([Type] -> Type -> Type) -> (Type -> Type) -> Type -> Type) -> [Type] -> Type -> Type
data SynHefty f env a where
  SynPureH :: Var env a -> SynHefty f env a
  SynBindH :: f sub (Var env) x -> () -> SynHefty f (x : env) a -> SynHefty f env a

class HHTraversable h where
  mutraverse :: Applicative f => (forall x. m x -> f (m' x)) -> (forall x. u x -> f (u' x)) -> h m u a -> f (h m' u' a)

traverseSynHefty :: 
  (Applicative n) => -- , forall m. HFunctor (f m), forall m. HFunctor (g m)) =>
  (forall env u x. f (SynHefty f env) u x -> n (g (SynHefty g env) u x)) ->
  SynHefty f env a ->
  n (SynHefty g env a)
traverseSynHefty _ (SynPureH x) = pure (SynPureH x)
traverseSynHefty f (SynBindH op k) = SynBindH <$> f op <*> traverseSynHefty f k

-- newtype SynF f a = SynF (SynFree f '[] a)


-- 

type SemHefty :: ((Type -> Type) -> (Type -> Type) -> Type -> Type) -> (Type -> Type) -> Type -> Type
data SemHefty f u a where
  SemPureH :: u a -> SemHefty f u a
  SemBindH :: f (SemHefty f u) u x -> (forall u'. (u <= u') => u' x -> SemHefty f u' a) -> SemHefty f u a

-- (>>=) :: SemFree f u a -> (forall u'. u <= u' => (forall u''. u' <= u'' => u'' a) -> SemFree f u' b) -> SemFree f u b
-- SemPure x >>= k = k (inj x)
-- SemBind op k >>= k' = SemBind op (\x -> k (inj x) >>= k')
-- 
-- newtype SemF f a = SemF (forall u'. SemFree f u' a)
-- 
-- type HFunctor :: ((Type -> Type) -> Type -> Type) -> Constraint
-- class HFunctor h where
--   hmap :: (forall x. f x -> g x) -> h f a -> h g a
-- 
-- synFToSemF :: HFunctor f => SynF f a -> SemF f a
-- synFToSemF (SynF x0) = SemF (go (\case {}) x0) where
--   go :: HFunctor f => (forall x. Var env x -> u x) -> SynFree f env a -> SemFree f u a
--   go env (SynPure x) = SemPure (env x)
--   go env (SynBind op k) = SemBind (hmap env op) (\x -> go (\case VZ -> x; VS v -> inj (env v)) k)
-- 
-- semFToSynF :: SemF f a -> SynF f a
-- semFToSynF (SemF x0) = SynF (go x0) where
--   go :: SemFree f (Var env) a -> SynFree f env a
--   go (SemPure x) = SynPure x
--   go (SemBind op k) = SynBind op (go (k VZ))
-- 
-- type OpTraverse :: (((Type -> Type) -> Type -> Type) -> Type -> Type) -> Constraint
-- class OpTraverse h where
--   optraverse :: (Applicative m, HFunctor f, HFunctor g) => (forall u' x. f u' x -> m (g u' x)) -> h f a -> m (h g a)
-- 
-- instance OpTraverse SynF where
--   optraverse f (SynF x) = SynF <$> syntraverse f x
-- 
-- syntraverse :: 
--   (Applicative m, HFunctor f, HFunctor g) =>
--   (forall u x. f u x -> m (g u x)) ->
--   SynFree f env a -> m (SynFree g env a)
-- syntraverse _ (SynPure v) = pure (SynPure v)
-- syntraverse f (SynBind op k) = SynBind <$> f op <*> syntraverse f k
-- 
-- instance OpTraverse SemF where
--   optraverse f = fmap synFToSemF . optraverse f . semFToSynF

main :: IO ()
main = do
  print (semToSyn prog1)
  print (semToSyn prog2)
  print (semToSyn (synToSem (semToSyn prog2)))
  print (semToSyn prog3)
 
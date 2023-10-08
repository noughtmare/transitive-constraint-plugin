{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

import Sub

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

instance Var env <= Var (x : env) where
  inj = VS

newtype Forall f a = Forall (forall u. f u a)

synToSem :: Syn '[] a -> Forall Sem a
synToSem x0 = Forall (go (\case {}) x0)
  where
    go :: (forall x. Var env x -> u x) -> Syn env a -> Sem u a
    go env (SynVar x) = SemVar (env x)
    go env (SynApp f x) = SemApp (go env f) (go env x)
    go env (SynLam bdy) = SemLam (\x -> go (\case VZ -> x; VS v -> inj (env v)) bdy)

semToSyn :: Forall Sem a -> Syn '[] a
semToSyn (Forall sem) = go sem
  where
    go :: Sem (Var env) a -> Syn env a
    go (SemVar x) = SynVar x
    go (SemApp f x) = SynApp (go f) (go x)
    go (SemLam bdy) = SynLam (go (bdy VZ))

prog1 :: Forall Sem (b -> a -> b)
prog1 = Forall (SemLam (\x -> SemLam (\_ -> SemVar (inj x))))

var :: (u <= u') => u a -> Sem u' a
var x = SemVar (inj x)

λ :: (forall u'. (u <= u') => u' a -> Sem u' b) -> Sem u (a -> b)
λ f = SemLam f

-- For those who don't have a Greek keyboard
lam :: (forall u'. (u <= u') => u' a -> Sem u' b) -> Sem u (a -> b)
lam f = λ f

infixl 1 $$
($$) :: Sem u (a -> b) -> Sem u a -> Sem u b
($$) = SemApp

prog2 :: Forall Sem ((b -> c) -> a -> b -> c)
prog2 = Forall $ λ \x -> λ \_ -> λ \z -> var x $$ var z

-- >>> semToSyn prog2
-- SynLam (SynLam (SynLam (SynApp (SynVar (VS (VS VZ))) (SynVar VZ))))

prog3 :: Forall Sem (a -> b -> b)
prog3 = Forall $ (λ \x -> λ \_y -> var x) $$ λ \y -> var y

-- >>> semToSyn prog3
-- SynApp (SynLam (SynLam (SynVar (VS VZ)))) (SynLam (SynVar VZ))

main :: IO ()
main = do
  print (semToSyn prog1)
  print (semToSyn prog2)
  print (semToSyn (synToSem (semToSyn prog2)))
  print (semToSyn prog3)

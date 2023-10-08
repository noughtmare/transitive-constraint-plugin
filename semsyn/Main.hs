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

-- Currently unused (WIP)
data SemFree f u a where
  SemPure :: u a -> Sem u a
  SemBind :: f u x -> (forall u'. (u <= u') => u' x -> SemFree f u' a) -> SemFree f u a

main :: IO ()
main = do
  print (semToSyn prog1)
  print (semToSyn prog2)
  print (semToSyn (synToSem (semToSyn prog2)))
  print (semToSyn prog3)

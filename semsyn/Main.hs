{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use id" #-}
{-# HLINT ignore "Redundant bracket" #-}

import Data.Kind
import Sub
import Prelude hiding ((>>=))

type STLChoas :: forall k. (k -> Type -> Type) -> Constraint
class STLChoas f where
  lam :: forall e a b. (forall e'. (f e <= f e') => (forall e''. (f e' <= f e'') => f e'' a) -> f e' b) -> f e (a -> b)
  ($$) :: f e (a -> b) -> f e a -> f e b

infixl 1 $$

-- Syntax

type Ix :: [k] -> k -> Type
data Ix e a where
  Here :: Ix (a : e) a
  There :: !(Ix e a) -> Ix (b : e) a
deriving instance Show (Ix e a)

type DSTLC :: [k] -> k -> Type
data DSTLC e a where
  Var :: Ix e a -> DSTLC e a
  Lam :: DSTLC (a : e) b -> DSTLC e (a -> b)
  App :: DSTLC e (a -> b) -> DSTLC e a -> DSTLC e b
deriving instance Show (DSTLC e a)

eval :: DSTLC e a -> (forall x. Ix e x -> x) -> a
eval (Var v) ev = ev v
eval (Lam x) ev = \y -> eval x (\case Here -> y; There v -> ev v)
eval (App x y) ev = eval x ev (eval y ev)

rename :: (forall x. Ix e x -> Ix e' x) -> DSTLC e a -> DSTLC e' a
rename f (Var v) = Var (f v)
rename f (Lam x) = Lam (rename (\case Here -> Here; There v -> There (f v)) x)
rename f (App x y) = App (rename f x) (rename f y)

subst :: DSTLC e a -> (forall x. Ix e x -> DSTLC e' x) -> DSTLC e' a
subst (Var v) ev = ev v
subst (Lam x) ev = Lam (subst x (\case Here -> Var Here ; There v -> rename There (ev v)))
subst (App x y) ev = App (subst x ev) (subst y ev)

norm :: DSTLC e a -> DSTLC e a
norm (Var v) = Var v
norm (Lam x) = Lam (norm x)
norm (App x y) = case (norm x, norm y) of
  (Lam x', y') -> subst x' (\case Here -> y' ; There v -> Var v)
  (x', y') -> x' $$ y'

data Thin xs ys where
  Keep :: Thin xs ys -> Thin (x : xs) (x : ys)
  Drop :: Thin xs ys -> Thin xs (x : ys)
  Id :: Thin xs xs
  Init :: Thin '[] xs
deriving instance Show (Thin xs ys)

data ThinF f e a = forall e'. ThinF (f e' a) (Thin e' e)
deriving instance (forall e'. Show (f e' a)) => Show (ThinF f e a)

data ThinMerge e1 e2 e = forall e3. ThinMerge (Thin e3 e) (Thin e1 e3) (Thin e2 e3)

mergeThin :: Thin e1 e -> Thin e2 e -> ThinMerge e1 e2 e
mergeThin Id t2 = ThinMerge Id Id t2
mergeThin t1 Id = ThinMerge Id t1 Id
mergeThin Init t2 = ThinMerge t2 Init Id
mergeThin t1 Init = ThinMerge t1 Id Init
mergeThin (Keep t1) (Keep t2) = case mergeThin t1 t2 of
  ThinMerge t t1' t2' -> ThinMerge (Keep t) (Keep t1') (Keep t2')
mergeThin (Keep t1) (Drop t2) = case mergeThin t1 t2 of
  ThinMerge t t1' t2' -> ThinMerge (Keep t) (Keep t1') (Drop t2')
mergeThin (Drop t1) (Keep t2) = case mergeThin t1 t2 of
  ThinMerge t t1' t2' -> ThinMerge (Keep t) (Drop t1') (Keep t2')
mergeThin (Drop t1) (Drop t2) = case mergeThin t1 t2 of
  ThinMerge t t1' t2' -> ThinMerge (Drop t) t1' t2'

apThinIx :: Thin e e' -> Ix e a -> Ix e' a
apThinIx (Keep _) Here = Here
apThinIx (Keep t) (There v) = There (apThinIx t v)
apThinIx (Drop t) v = There (apThinIx t v)
apThinIx Id x = x
apThinIx Init x = case x of {}

apThin :: Thin e e' -> DSTLC e a -> DSTLC e' a
apThin Id x = x
apThin t (Var v) = Var (apThinIx t v)
apThin t (Lam x) = Lam (apThin (Keep t) x)
apThin t (App x y) = App (apThin t x) (apThin t y)

varThin :: Ix e a -> Thin '[a] e
varThin Here = Keep Init
varThin (There v) = Drop (varThin v)

data KeepThin xs y ys where
  KT :: Thin xs' ys -> KeepThin (y : xs') y ys

thinHead :: Thin xs (y : ys) -> Either (Thin xs ys) (KeepThin xs y ys)
thinHead (Keep t) = Right (KT t)
thinHead (Drop t) = Left t
thinHead Id = Right (KT Id)
thinHead Init = Left Init

thin :: DSTLC e a -> ThinF DSTLC e a
thin (Var v) = ThinF (Var Here) (varThin v)
thin (Lam x) =
  case thin x of
    ThinF x' t -> case thinHead t of
      Right (KT t') -> ThinF (Lam x') t'
      Left t' -> ThinF (Lam (apThin (Drop Id) x')) t'
thin (App x y) =
  case (thin x, thin y) of
    (ThinF x' tx, ThinF y' ty) -> case mergeThin tx ty of
      ThinMerge t' tx' ty' -> ThinF (App (apThin tx' x') (apThin ty' y')) t'

instance DSTLC e <= DSTLC (x : e) where
  inj = rename There

instance STLChoas DSTLC where
  lam :: forall e a b. (forall e'. (DSTLC e <= DSTLC e') => (forall e''. (DSTLC e' <= DSTLC e'') => DSTLC e'' a) -> DSTLC e' b) -> DSTLC e (a -> b)
  lam f = Lam (f (inj (Var (Here @_ @e)))) -- TODO: the @e can probably be avoided if the plugin was smarter.
  ($$) = App

type OThoas e a = forall k f (e' :: k). STLChoas f => (forall e'' x. f e' <= f e'' => Ix e x -> f e'' x) -> f e' a

toHOAS :: DSTLC e a -> OThoas e a
toHOAS (Var v) = \g -> g v
toHOAS (Lam x) = \g -> lam \y -> toHOAS x \case Here -> y; There v -> g v
toHOAS (App x y) = \g -> toHOAS x g $$ toHOAS y g

toHOAS0 :: STLChoas f => DSTLC '[] a -> f e' a
toHOAS0 x = toHOAS x \case {}

-- ConstId

newtype ConstId a b = ConstId { unConstId :: b }

instance ConstId a <= ConstId b where
  inj (ConstId x) = ConstId x

instance STLChoas ConstId where
  lam f = ConstId (\x -> unConstId (f (ConstId x)))
  ConstId f $$ ConstId x = ConstId (f x)

-- Examples

prog2 :: STLChoas f => f e ((b -> c) -> a -> b -> c)
prog2 = lam \ x -> lam \ _y -> lam \ z -> x $$ z

prog3 :: STLChoas f => f e (a -> b -> b)
prog3 = (lam \ x -> lam \ _y -> x) $$ (lam \ y -> y)

fromHOAS :: (forall f. STLChoas f => f e a) -> DSTLC e a
fromHOAS x = x

semantic :: (forall f. STLChoas f => f e a) -> a
semantic x = unConstId x

main :: IO ()
main = do
  print (thin prog2)
  print (fromHOAS prog3)
  print (norm prog3)
{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}

{-# LANGUAGE QualifiedDo #-}

import Sub
import Data.Kind
import Data.Coerce

type Sig = ((Type -> Type) -> Type) -> (Type -> Type) -> Type

type Return :: Sig -> Type -> (Type -> Type) -> Type
newtype Return f a u = Return (Free f u a)

type Free :: Sig -> (Type -> Type) -> Type -> Type
data Free f u a = Pure (u a) | Free (f (Return f a) u)

type UFunctor :: Sig -> Constraint
class UFunctor f where
  retmap :: (forall u'. (u <= u') => r u' -> r' u') -> f r u -> f r' u

(>>=) :: 
  UFunctor f =>
  (Free f u a) ->
  (forall u'. (u <= u') => u' a -> Free f u' b) ->
  Free f u b
Pure x >>= k = k x
Free x >>= k = Free (retmap (coerce (Main.>>= k)) x)

type MySig :: Sig
data MySig r u where 
  HsPure :: a -> (forall u'. u <= u' => u' a -> r u') -> MySig r u
  HsApply :: u (a -> b) -> u a -> (forall u'. u <= u' => u' b -> r u') -> MySig r u

instance UFunctor MySig where
  retmap f (HsPure x k) = HsPure x (f . k)
  retmap f (HsApply x y k) = HsApply x y (f . k)

injfree :: u <= u' => Free MySig u a -> Free MySig u' a
injfree (Pure x) = Pure (inj x)
injfree (Free x) = Free (injmysig x)

injmysig :: u <= u' => MySig (Return MySig a) u -> MySig (Return MySig a) u'
injmysig (HsPure x k) = HsPure x (coerce injfree . k)
injmysig (HsApply x y k) = HsApply (inj x) (inj y) (coerce injfree . k)

hsapply :: Free MySig u (a -> b) -> Free MySig u a -> Free MySig u b
hsapply x y = Main.do
  x' <- x
  y' <- injfree y
  Free (HsApply (inj x') y' (coerce Pure))

main = pure ()
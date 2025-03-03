{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE QuantifiedConstraints #-}

module GCDLib where

import qualified Sub
import Data.Kind
import Prelude hiding ((>>=), return, gcd)
import Data.Proxy

type CType = [Type] -> Type

type (<) :: (CType -> CType) -> (CType -> CType) -> Constraint
class f < g where
  inj :: f c e -> g c e
  prj :: g c e -> Maybe (f c e)

type (+) :: (CType -> CType) -> (CType -> CType) -> (CType -> CType)
data (f + g) c e where
  Inl :: f c e -> (f + g) c e
  Inr :: g c e -> (f + g) c e
  deriving Show

instance {-# OVERLAPPING #-} f < (f + g) where
  inj = Inl
  prj (Inl x) = Just x
  prj _ = Nothing

instance f < g => f < (f' + g) where
  inj = Inr . inj
  prj (Inr x) = prj x
  prj _ = Nothing

-- De Bruijn index
type Var :: Type -> [Type] -> Type
data Var a e where
  Here :: Var a (a : e)
  There :: Var a e -> Var a (b : e)
deriving instance Show (Var a e)

newtype Var' e a = Var' (Var a e)

var :: e <= e' => Var a e -> Var a e'
var x = case Sub.inj (Var' x) of Var' y -> y

instance e <= e' => Var' e Sub.<= Var' (a : e') where
  inj x = case Sub.inj x of Var' y -> Var' (There y)

type Length :: [k] -> Type
data Length as where
  Z :: Length '[]
  S :: Length as -> Length (a : as)

class KnownLength as where
  lengthS :: Length as
instance KnownLength '[] where
  lengthS = Z
instance KnownLength as => KnownLength (a : as) where
  lengthS = S lengthS

type (<=) :: [Type] -> [Type] -> Constraint
type e <= e' = Var' e Sub.<= Var' e'

type Vars :: [Type] -> [Type] -> Type
data Vars as e where
  Nil :: Vars '[] e
  (:>) :: Var a e -> Vars as e -> Vars (a : as) e
deriving instance Show (Vars as e)

infixr :>

mapVars :: (forall a. Var a e -> Var a e') -> Vars as e -> Vars as e'
mapVars _ Nil = Nil
mapVars f (x :> xs) = f x :> mapVars f xs

type Free :: (CType -> CType) -> CType -> CType
data Free f c e where
  Pure :: c e -> Free f c e
  Free :: f (Free f c) e -> Free f c e
deriving instance ((forall e'. Show (c e')), forall c' e'. (forall e''. Show (c' e'')) => Show (f c' e')) => Show (Free f c e)

type Boolean :: CType -> CType
data Boolean c e where
  Bool :: Bool -> c (Bool : e) -> Boolean c e
  Ite :: Var Bool e -> c e -> c e -> Boolean c e
deriving instance (forall e'. Show (c e')) => Show (Boolean c e)

true, false :: Boolean < f => Free f (Var Bool) e
true = Free (inj (Bool True (Pure Here)))
false = Free (inj (Bool False (Pure Here)))

ite :: Boolean < f => Var Bool e -> Free f c e -> Free f c e -> Free f c e
ite x t f = Free (inj (Ite x t f))

type State :: Type -> CType -> CType
data State s c e where
  Put :: Var s e -> c e -> State s c e
  Get :: c (s : e) -> State s c e
deriving instance (forall e'. Show (c e')) => Show (State s c e)

get :: State s < f => Free f (Var s) e
get = Free (inj (Get (Pure Here)))

put :: State s < f => Var s e -> Free f (Vars '[]) e
put x = Free (inj (Put x (Pure Nil)))

type Arith :: CType -> CType
data Arith c e where
  Int :: Int -> c (Int : e) -> Arith c e
  Add :: Var Int e -> Var Int e -> c (Int : e) -> Arith c e
  Sub :: Var Int e -> Var Int e -> c (Int : e) -> Arith c e
  Gt :: Var Int e -> Var Int e -> c (Bool : e) -> Arith c e
  Eq :: Var Int e -> Var Int e -> c (Bool : e) -> Arith c e
deriving instance (forall e'. Show (c e')) => Show (Arith c e)

int :: Arith < f => Int -> Free f (Var Int) e
int n = Free (inj (Int n (Pure Here)))

add, sub :: (e1 <= e, e2 <= e, Arith < f) => Var Int e1 -> Var Int e2 -> Free f (Var Int) e
add x y = Free (inj (Add (var x) (var y) (Pure Here)))
sub x y = Free (inj (Sub (var x) (var y) (Pure Here)))

gt, eq :: (Arith < f, e1 <= e, e2 <= e) => Var Int e1 -> Var Int e2 -> Free f (Var Bool) e
gt x y = Free (inj (Gt (var x) (var y) (Pure Here)))
eq x y = Free (inj (Eq (var x) (var y) (Pure Here)))

type (++) :: [k] -> [k] -> [k]
type family xs ++ ys where
  '[] ++ ys = ys
  (x : xs) ++ ys = x : (xs ++ ys)

type Flow :: ([Type] -> Type) -> CType -> CType
data Flow ref c e where
  Block :: (KnownLength as, e <= (as ++ e)) => c (ref as : e) -> c (as ++ e) -> Flow ref c e
  Loop :: (KnownLength as, e <= (as ++ e), e <= (ref as : as ++ e)) => Vars as e -> c (ref as : as ++ e) -> Flow ref c e
  Br  :: Var (ref as) e -> Vars as e -> Flow ref c e
deriving instance (forall e'. Show (c e')) => Show (Flow ref c e)

heres :: forall as e. KnownLength as => Proxy e -> Vars as (as ++ e)
heres Proxy = go (lengthS @as) where
  go :: Length bs -> Vars bs (bs ++ e)
  go Z = Nil
  go (S i) = Here :> mapVars There (go i)

block :: forall as ref f c e. (KnownLength as, e <= (as ++ e), Flow ref < f) => Proxy ref -> (forall e'. e <= e' => Var (ref as) e' -> Free f c e') -> (forall e'. e <= e' => Vars as e' -> Free f c e') -> Free f c e
block _ m n = Free (inj (Block (m Here) (n (heres (Proxy @e)))))

loop :: forall as ref f c e. (KnownLength as, e <= (as ++ e), e <= (ref as : as ++ e), Flow ref < f) => Proxy ref -> Vars as e -> (forall e'. e <= e' => Var (ref as) e' -> Vars as e' -> Free f c e') -> Free f c e
loop _ x m = Free (inj (Loop x (m Here (mapVars There (heres (Proxy @e))))))

br :: (Flow ref < f, e1 <= e) => Var (ref as) e1 -> Vars as e -> Free f c e
br r x = Free (inj (Br (var r) x))

type End :: CType -> CType
data End c a deriving Show

type CFunctor :: (CType -> CType) -> Constraint
class CFunctor f where
  cmap :: (forall e'. (e <= e') => c e' -> c' e') -> f c e -> f c' e

instance CFunctor Arith where
  cmap f (Int n k) = Int n (f k)
  cmap f (Add x y k) = Add x y (f k)
  cmap f (Sub x y k) = Sub x y (f k)
  cmap f (Gt x y k) = Gt x y (f k)
  cmap f (Eq x y k) = Eq x y (f k)

instance CFunctor (State s) where
  cmap f (Put x k) = Put x (f k)
  cmap f (Get k) = Get (f k)

instance (CFunctor f, CFunctor g) => CFunctor (f + g) where
  cmap f (Inl x) = Inl (cmap f x)
  cmap f (Inr x) = Inr (cmap f x)

instance CFunctor (Flow ref) where
  cmap f (Block b k) = Block (f b) (f k)
  cmap f (Loop x k) = Loop x (f k)
  cmap _ (Br r x) = Br r x

instance CFunctor Boolean where
  cmap f (Bool b k) = Bool b (f k)
  cmap f (Ite b y n) = Ite b (f y) (f n)

instance CFunctor End where
  cmap _ x = case x of {}

(>>=) :: CFunctor f => Free f c e -> (forall e'. e <= e' => c e' -> Free f c' e') -> Free f c' e
Pure x >>= k = k x
Free m >>= k = Free (cmap (\x -> x >>= (\y -> k y)) m)

fail :: String -> Free f c e
fail e = error ("Failed to pattern match in do block: " ++ e)

return :: (VFunctor c, e <= e') => c e -> Free f c e'
return x = Pure (vmap var x)

type VFunctor :: CType -> Constraint
class VFunctor c where
  vmap :: (forall a. Var a e -> Var a e') -> c e -> c e'
instance VFunctor (Var a) where
  vmap x = x
instance VFunctor (Vars as) where
  vmap f (x :> xs) = f x :> vmap f xs
  vmap _ Nil = Nil

(.>) :: e <= e' => Var a e -> Vars as e' -> Vars (a : as) e'
x .> xs = var x :> xs
infixr .>
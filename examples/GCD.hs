{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE QuantifiedConstraints #-}

import qualified Sub
import Data.Kind
import Prelude hiding ((>>=), return, gcd)
import Data.Proxy

type CType = [Type] -> Type

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

instance {-# OVERLAPPING #-} e <= e' => Var' e Sub.<= Var' (a : e') where
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
  Cons :: Var a e -> Vars as e -> Vars (a : as) e
deriving instance Show (Vars as e)

mapVars :: (forall a. Var a e -> Var a e') -> Vars as e -> Vars as e'
mapVars _ Nil = Nil
mapVars f (Cons x xs) = Cons (f x) (mapVars f xs)

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

add, sub :: Arith < f => Var Int e -> Var Int e -> Free f (Var Int) e
add x y = Free (inj (Add x y (Pure Here)))
sub x y = Free (inj (Sub x y (Pure Here)))

gt, eq :: Arith < f => Var Int e -> Var Int e -> Free f (Var Bool) e
gt x y = Free (inj (Gt x y (Pure Here)))
eq x y = Free (inj (Eq x y (Pure Here)))

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
  go (S i) = Cons Here (mapVars There (go i))

block :: forall as ref f c e. (KnownLength as, e <= (as ++ e), Flow ref < f) => Proxy ref -> (forall e'. e <= e' => Var (ref as) e' -> Free f c e') -> (forall e'. e <= e' => Vars as e' -> Free f c e') -> Free f c e
block _ m n = Free (inj (Block (m Here) (n (heres (Proxy @e)))))

loop :: forall as ref f c e. (KnownLength as, e <= (as ++ e), e <= (ref as : as ++ e), Flow ref < f) => Proxy ref -> Vars as e -> (forall e'. e <= e' => Var (ref as) e' -> Vars as e' -> Free f c e') -> Free f c e
loop _ x m = Free (inj (Loop x (m Here (mapVars There (heres (Proxy @e))))))

br :: Flow ref < f => Var (ref as) e -> Vars as e -> Free f c e
br r x = Free (inj (Br r x))

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

return :: c e -> Free f c e
return x = Pure x

-- function gcd(a, b)
--     while a ≠ b
--         if a > b
--             a := a − b
--         else
--             b := b − a
--     return a

-- Without plugin:
--
-- gcd :: (CFunctor f, Boolean < f, Flow ref < f, Arith < f) => Proxy ref -> Var Int e -> Var Int e -> Free f (Var Int) e
-- gcd (Proxy @ref) x y =
--   loop (Proxy @ref) (Cons x (Cons y Nil)) $ \_ r (Cons x (Cons y Nil)) ->
--     gt x y >>= \e2 b ->
--     ite b
--       (sub (e2 x) (e2 y) >>= \e3 x ->
--       return (Cons x (Cons (e3$e2 y) Nil)))
--       (sub (e2 y) (e2 x) >>= \e3 y ->
--       return (Cons (e3$e2 x) (Cons y Nil))) >>= \e3 (Cons x (Cons y Nil)) ->
--     eq x y >>= \e4 b ->
--     ite b
--       (return (e4 x))
--       (br (e4$e3$e2 r) (Cons (e4 x) (Cons (e4 y) Nil)))

var :: e <= e' => Var a e -> Var a e'
var x = case Sub.inj (Var' x) of Var' y -> y

gcd :: (CFunctor f, Boolean < f, Flow ref < f, Arith < f) => Proxy ref -> Var Int e -> Var Int e -> Free f (Var Int) e
gcd (Proxy @ref) x0 y0 =
  loop (Proxy @ref) (Cons x0 (Cons y0 Nil)) (\r (Cons x (Cons y Nil)) ->
    gt x y >>= \b ->
    ite b
      (sub (var x) (var y) >>= \x' ->
      return (Cons x' (Cons (var y) Nil)))
      (sub (var y) (var x) >>= \y' ->
      return (Cons (var x) (Cons y' Nil)))
      >>= \(Cons x' (Cons y' Nil)) ->
    eq x' y' >>= \b' ->
    ite b'
      (return (var x'))
      (br (var r) (Cons (var x') (Cons (var y') Nil))))

type Void1 :: [Type] -> Type
data Void1 a

main :: IO ()
main = print
  @(Free (Boolean + (Flow Void1 + (Arith + End))) (Var Int) '[])
  (int 8 >>= \x -> int 12 >>= \y -> gcd (Proxy @Void1) (var x) y)
{-# OPTIONS_GHC -fplugin=TransitiveConstraintPlugin #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE BlockArguments #-}

module Main (main) where

import Prelude hiding ((>>=), gcd, return)
import Data.Kind
import Data.Proxy
import GCDLib as M

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

-- this only works with GHC 9.12 or later
-- otherwise you need to write out the >>= by hand.
gcd :: forall ref -> (CFunctor f, Boolean < f, Flow ref < f, Arith < f, e1 <= e, e2 <= e)
    => Var Int e1 -> Var Int e2 -> Free f (Var Int) e
gcd ref x0 y0 =
  loop (Proxy @ref) (x0 .> y0 .> Nil) \r (x :> y :> Nil) -> M.do
    b <- gt x y
    (x' :> y' :> Nil) <- 
      ite b 
        M.do x' <- sub x y
             return (x' :> y .> Nil)
        M.do y' <- sub y x
             return (x .> y' :> Nil)
    b' <- eq x' y'
    ite b'
      (return x')
      (br r (x' .> y' .> Nil))

type Void1 :: [Type] -> Type
data Void1 a

main :: IO ()
main = print
  @(Free (Boolean + (Flow Void1 + (Arith + End))) (Var Int) '[])
  M.do x <- int 8
       y <- int 12
       gcd Void1 x y
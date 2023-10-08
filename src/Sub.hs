{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Sub where

import Data.Kind (Constraint, Type)

type (<=) :: (Type -> Type) -> (Type -> Type) -> Constraint
class f <= g where
  inj :: f x -> g x

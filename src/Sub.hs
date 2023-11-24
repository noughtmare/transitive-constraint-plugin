{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Sub where

import Data.Kind (Constraint, Type)

type (<=) :: (Type -> Type) -> (Type -> Type) -> Constraint
class f <= g where
  inj :: f x -> g x

-- These are overflapping, but our plugin will resolve the overlap.

instance f <= f where
  inj = id

instance forall f g h. (f <= g, g <= h) => f <= h where
  inj = inj @g @h . inj @f @g
module Sub where

import Data.Kind (Constraint, Type)

type (<=) :: (k -> Type) -> (k -> Type) -> Constraint
class f <= g where
  inj :: f x -> g x

-- -- These are overlapping, but our plugin will resolve the overlap.
-- 
-- instance f <= f where
--   inj = id
-- 
-- instance forall f g h. (f <= g, g <= h) => f <= h where
--   inj = inj @g @h . inj @f @g

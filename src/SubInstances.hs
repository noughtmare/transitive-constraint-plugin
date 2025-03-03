{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SubInstances {-# WARNING "Do not import this module!" #-} where

import Sub

-- These are overlapping, but our plugin will resolve the overlap.

instance  f <= f where
  inj = id

instance forall f g h. (f <= g, g <= h) => f <= h where
  inj = inj @_ @g @h . inj @_ @f @g
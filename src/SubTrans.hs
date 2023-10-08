{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SubTrans where

import Sub

instance f <= f where
  inj = id

instance forall f g h. (f <= g, g <= h) => f <= h where
  inj = inj @g @h . inj @f @g

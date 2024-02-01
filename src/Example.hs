
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS -fplugin RoHsPlugin #-}

module Example where
import Common
import Surface

import GHC.Base

{-
bar2 :: forall z y1 y2.
        -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
        (-- Plus (R '["x" := Integer]) z y1,    -- `Integer` so defaulting doesn't get in the way
         -- Plus (R '["x" := Bool]) z y2,
         -- These three constraint should all be solvable, *given the definitions above*
          (R '["x" := Bool]    ~+~ z) ~ y2
        , (R '["x" := Integer] ~+~ z) ~ y1
        ) =>
        V0 y1 -> V0 y2
bar2 = case0 @"x" (\i -> con0 @"x" (i == zero)) `brn0` inj0
  where zero :: Integer = 0

-- This example fails because
-- Could not deduce ‘(R '["x" := Integer] ~+~ y0) ~ y1
--       from the context: ((R '["x" := Bool] ~+~ z) ~ y2,
--                          (R '["x" := Integer] ~+~ z) ~ y1)
-}

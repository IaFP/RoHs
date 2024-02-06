
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS -fplugin RoHsPlugin -fplugin RoHsCorePlugin #-}
{-# OPTIONS -fforce-recomp #-}

module Example where
import Common
import Surface

-- import GHC.Base

type BigR = R '["Const" := ZeroF Int] ~+~  R '["Add" := TwoF] ~+~ R '["Double" := OneF]

type SmallR = R '["Const" := ZeroF Int] ~+~ R '["Add" := TwoF]

desugar :: (-- These should all be solvable
            All Functor SmallR,
            Plus (R '["Double" := OneF]) SmallR BigR
           ) =>
           Mu (V1 BigR) -> Mu (V1 SmallR)
desugar (Wrap e) = Wrap ((double `brn1` (fmapV desugar . inj1)) e) where
  double = case1 @"Double" (\(C1 x) -> con1 @"Add" (C2 (desugar x) (desugar x)))

{-
GHC currently cannot prove:
  [W] hole{co_a5tT} {0}:: V1 BigR (Mu (V1 BigR))
                          ~# V1 (x_a5tk[tau:1] ~+~ y_a5tn[tau:1]) t_a5tl[tau:1]
-}


{-
bar2 :: forall z y1 y2.
        -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
        (Plus (R '["x" := Integer]) z y1,    -- `Integer` so defaulting doesn't get in the way
         Plus (R '["x" := Bool]) z y2,
         -- These three constraint should all be solvable, *given the definitions above*
         R '["x" := Bool] ~<~ R '["x" := Bool],
         R '["x" := Bool] ~<~ y2,
         z ~<~ y2
        ) =>
        V0 y1 -> V0 y2
bar2 = case0 @"x" (\i -> con0 @"x" (i == zero)) `brn0` inj0
  where zero :: Integer = 0

-- This example fails because
-- Could not deduce ‘(R '["x" := Integer] ~+~ y0) ~ y1
--       from the context: ((R '["x" := Bool] ~+~ z) ~ y2,
--                          (R '["x" := Integer] ~+~ z) ~ y1)
-}

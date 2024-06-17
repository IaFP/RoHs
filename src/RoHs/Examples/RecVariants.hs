{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
-- {-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
{-# OPTIONS -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -fplugin RoHs.Plugin #-}


module RoHs.Examples.RecVariants where


import RoHs.Language.Lib
import RoHs.Examples.Variants


import Data.Proxy
default (Int)

-- cases :: (V1 z (Mu (V1 z)) -> (Mu (V1 z) -> r) -> r) -> Mu (V1 z) -> r
-- cases f = \ (Mk e) -> f e (cases f)

-- brn1 :: (V1 x t -> u) -> (V1 y t -> u) -> (V1 (x ~+~ y) t -> u)

data t ~> u where
  Rec :: (forall y. (z ~<~ y) => V1 z (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u)
      -> Mu (V1 z) ~> u

brnr :: forall v w vw {u}. Plus v w vw => ((Mu (V1 v)) ~> u) -> ((Mu (V1 w)) ~> u) -> ((Mu (V1 vw)) ~> u)
brnr (Rec rfv) (Rec rfw) = Rec rfvw
  where
  rfvw :: forall y. (vw ~<~ y) => (V1 vw (Mu (V1 y))) -> (Mu (V1 y) -> u) -> u
  rfvw = brn1 rfv rfw
  -- rfv @v :: V1 v (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u
  -- rfw @w :: V1 w (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u
  -- brn1 ... :: V1 vw (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u

-- (~$~) :: (Mu (V1 x) ~> t) -> Mu (V1 x) -> t
-- (Rec f) ~$~ (Mk x) = f x (Rec f ~$~)
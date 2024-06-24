{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
-- {-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -fplugin RoHs.Plugin #-}


module RoHs.Examples.RecVariants2 where

import RoHs.Language.Lib
import RoHs.Examples.Variants


default (Int)

-- This is a genralized version of t ~> u to enable arbitrary nested case match
-- The hope is to be able to peek more than once

data t ~> u where
  Rec :: (forall x y. Plus z x y => V1 z (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u)
      -> Mu (V1 z) ~> u

brnr :: forall v w {vw} {u}. Plus v w vw => ((Mu (V1 v)) ~> u) -> ((Mu (V1 w)) ~> u) -> ((Mu (V1 vw)) ~> u)
brnr (Rec rfv) (Rec rfw) = Rec rfvw
  where
  rfvw :: forall z y. Plus vw z y => (V1 vw (Mu (V1 y))) -> (Mu (V1 y) -> u) -> u
  rfvw = brn1 @v @w rfv rfw

-- (~$~) :: (Mu (V1 x) ~> t) -> Mu (V1 x) -> t
-- (Rec f) ~$~ (Mk x) = f x (Rec f ~$~)


type NatPosR = R '[ "zeroP" := Zero (), "inc1" := One]
type NatNegR = R '[ "zeroN" := Zero (), "dec1" := One]


evalZP :: V1 (R '[ "zeroP" := Zero () ]) t -> p -> Int
evalIP :: V1 (R '[ "inc1" := One ]) t -> (t -> Int) -> Int

evalZP e _ = case1 @"zeroP" (\(Z _) -> 0) e
evalIP e' r = case1 @"inc1" (\(O e) -> 1 + r e) e'


evalZN :: V1 (R '[ "zeroN" := Zero ()]) t -> p -> Int
evalIN :: V1 (R '[ "dec1" := One ]) t -> (t -> Int) -> Int

evalZN e _ = case1 @"zeroN" (\(Z _) -> 0) e
evalIN e' r = case1 @"dec1" (\(O e) -> (r e) - 1) e'


mkZP :: R ('[ "zeroP" := Zero () ]) ~<~ z => Mu (V1 z)
mkZP =  Mk (con1 @"zeroP" (Z ()))

mkIP :: R ('[ "inc1" := One ]) ~<~ z => Mu (V1 z) -> Mu (V1 z)
mkIP e =  Mk (con1 @"inc1" (O e))

mkZN :: R ('[ "zeroN" := Zero () ]) ~<~ z => Mu (V1 z)
mkZN =  Mk (con1 @"zeroN" (Z ()))

mkIN :: R ('[ "dec1" := One ]) ~<~ z => Mu (V1 z) -> Mu (V1 z)
mkIN e =  Mk (con1 @"dec1" (O e))


evalP :: NatPosR ~<~ y => V1 NatPosR (Mu (V1 y)) -> (Mu (V1 y) -> Int) -> Int
evalN :: NatNegR ~<~ y => V1 NatNegR (Mu (V1 y)) -> (Mu (V1 y) -> Int) -> Int

evalP = evalZP `brn1` evalIP
evalN = evalZN `brn1` evalIN

-- evalPN = (~$~) ((Rec evalP) `brnr` (Rec evalN))


-- halfP :: NatPosR ~<~ y => V1 NatPosR (Mu (V1 y)) -> (Mu (V1 y) -> Int) -> Int
-- halfP

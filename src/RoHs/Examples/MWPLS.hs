{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UnicodeSyntax #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -fplugin RoHs.Plugin #-}


module RoHs.Examples.MWPLS where

import RoHs.Language.Lib
-- import RoHs.Examples.Basic
-- import RoHs.Examples.Variants


type XCoord = R '[ "x" := Int ]
type YCoord = R '[ "y" := Int ]
type Coord = R '["x" := Int , "y" := Int]

type Color = R '[ "R" := Int , "G" := Int , "B" := Int]

type Pixel = R0 (Coord ~+~ Color)

coord :: R0 Coord
coord =  (labR0 @"x" (22 :: Int)) `cat0` (labR0 @"y" (11 :: Int))

color :: R0 Color
color =  (labR0 @"R" (101 :: Int))
         `cat0`  (labR0 @"B" (102 :: Int))
         `cat0`  (labR0 @"G" (103 :: Int))



p :: Pixel
p = coord `cat0` color


move :: R0 Coord -> R0 Coord
move c = labR0 @"x" (1 + (sel0 @"x" c) :: Int)
              `cat0` (labR0 @"y" (1 + (sel0 @"y" c) :: Int))

transpose' :: forall r z. (Coord ~<~ z, (Coord ~+~ r) ~ z) => R0 z -> R0 z
transpose' c = labR0 @"y" ((sel0 @"x" c) :: Int)
              `cat0` (labR0 @"x" ((sel0 @"y" c) :: Int))
              `cat0` (prj0 @r @z c)

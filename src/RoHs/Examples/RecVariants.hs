{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -fplugin RoHs.Plugin #-}


module RoHs.Examples.RecVariants where

import RoHs.Language.Lib
import RoHs.Examples.Variants


default (Int)

-- cases :: (V1 z (Mu (V1 z)) -> (Mu (V1 z) -> r) -> r) -> Mu (V1 z) -> r
-- cases f = \ (Mk e) -> f e (cases f)

-- brn1 :: (V1 x t -> u) -> (V1 y t -> u) -> (V1 (x ~+~ y) t -> u)

data t ~> u where
  Rec :: (forall y. (z ~<~ y) => V1 z (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u)
      -> Mu (V1 z) ~> u


-- I think i'll have to make this a primitive as i cannot write a core function that
-- takes two dictonary types x ~<~ y and y ~<~ z and compiles it to x ~<~ z by doing the
-- type conversion to/from (Int, [Int]) while type checking
brnr :: forall v w {vw} {u}. Plus v w vw => ((Mu (V1 v)) ~> u) -> ((Mu (V1 w)) ~> u) -> ((Mu (V1 vw)) ~> u)
brnr (Rec rfv) (Rec rfw) = Rec rfvw
  where
  rfvw :: forall y. (vw ~<~ y) => (V1 vw (Mu (V1 y))) -> (Mu (V1 y) -> u) -> u
  rfvw = brn1 @v @w rfv rfw
  -- rfv @v :: V1 v (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u
  -- rfw @w :: V1 w (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u
  -- brn1 ... :: V1 vw (Mu (V1 vw)) -> (Mu (V1 vw) -> u) -> u

(~$~) :: (Mu (V1 x) ~> t) -> Mu (V1 x) -> t
(Rec f) ~$~ (Mk x) = f x (Rec f ~$~)


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



evalP :: NatPosR ~<~ y => V1 NatPosR (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u
evalN :: NatNegR ~<~ y => V1 NatNegR (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u
-- evalP = cases (evalZP `brn1` evalIP)
-- evalN = cases (evalZN `brn1` evalIN)

evalP = undefined
evalN = undefined

evalPN = (~$~) ((Rec evalP) `brnr` (Rec evalN))

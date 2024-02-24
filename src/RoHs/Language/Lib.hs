{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- {-# OPTIONS -fforce-recomp -dcore-lint -ddump-simpl -ddump-ds-preopt -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -O2 -fforce-recomp -dcore-lint -dverbose-core2core -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -fplugin RoHs.Plugin #-}

module RoHs.Language.Lib (
    case0
  , con0
  , sel0

  , labR0
  , unlabR0
  , prj0
  , cat0
  , labV0
  , brn0
  , unlabV0
  , inj0

  -- , con1
  -- , case1

  -- * engineering hell
  , fstC, sndC, unsafeNth, compose, catC, brn, manyIn

  , module RoHs.Language.Types
  ) where

{-
A module for library of operations on rows and variants
It also exports the Primitives, so users must not explicitly import it
-}

import RoHs.Language.Types
import RoHs.Language.Primitives
import Data.Tuple
import Unsafe.Coerce


default (Int, Double)

-- and we can define

con0 :: forall s {t} {z}. R '[s := t] ~<~ z => t -> V0 z
con0 x = inj0 (labV0 @s x)

case0 :: forall s {t} {u}. (t -> u) -> V0 (R '[s := t]) -> u
case0 f = f . unlabV0  -- I am surprised GHC can figure this out... and somewhat concerned about what it's actually figured out

sel0 :: forall s {t} {z}. R '[s := t] ~<~ z => R0 z -> t
sel0 r = unlabR0 @s (prj0 r)


-- Primitives

labR0   :: forall s {t}. t -> R0 (R '[s := t])
unlabR0 :: forall s {t}. R0 (R '[s := t]) -> t
prj0    :: forall y z. y ~<~ z => R0 z -> R0 y
cat0    :: forall {x} {y} {z}. Plus x y z => R0 x -> R0 y -> R0 z
labV0   :: forall s {t}. t -> V0 (R '[s := t])
brn0    :: Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
unlabV0 :: forall s {t}. V0 (R '[s := t]) -> t
inj0    :: forall y z. y ~<~ z => V0 y -> V0 z


labR0    = labR0_I
unlabR0  = unlabR0_I
prj0     = prj0_I
cat0     = cat0_I
labV0    = labV0_I
brn0     = brn0_I
unlabV0  = unlabV0_I
inj0     = inj0_I

-- con1 :: forall s {f} {t} {z}. R '[s := f] ~<~ z => f t -> V1 z t
-- con1 x = inj1 (labV1 @s x)

-- case1 :: forall s {f} {t} {u}. (f t -> u) -> V1 (R '[s := f]) t -> u
-- case1 f = f . unlabV1


fstC :: forall {a}{b}. (a, b) -> a
sndC :: forall {a}{b}. (a, b) -> b
fstC = Prelude.fst
sndC = Prelude.snd

unsafeNth :: forall {a} {b}. Int -> a -> b
unsafeNth 0 x = y where
  MkSolo y = unsafeCoerce x
unsafeNth 1 x = y where
  (_, y) = unsafeCoerce x
unsafeNth 2 x = y where
  (_, _, y) = unsafeCoerce x
unsafeNth 3 x = y where
  (_, _, _, y) = unsafeCoerce x
unsafeNth 4 x = y where
  (_, _, _, _, y) = unsafeCoerce x
unsafeNth 5 x = y where
  (_, _, _, _, _, y) = unsafeCoerce x
unsafeNth 6 x = y where
  (_, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 7 x = y where
  (_, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 8 x = y where
  (_, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 9 x = y where
  (_, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 10 x = y where
  (_, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 11 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 12 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 13 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 14 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 15 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth 16 x = y where
  (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, y) = unsafeCoerce x
unsafeNth _ _ = error "exceeded limit"


compose :: (Int, a) -> (Int, b) -> (Int, c)
-- again, we seem to need to iterate our definition... I'll do only a few cases
-- I am concerned that we're going to stack up `unsafeCoerce`s, and that will
-- lead to underspecified types (and so misbehaving coercions) in the middle...
compose (0, _) _ = (0::Int, unsafeCoerce ())
compose (1, d) (_, e) = (1, unsafeCoerce (MkSolo (unsafeNth i e))) where
  MkSolo i = unsafeCoerce d
compose (2, d) (_, e) = (2, unsafeCoerce (unsafeNth i e, unsafeNth j e))  where
  (i, j) = unsafeCoerce d
compose (3, d) (_, e) = (3, unsafeCoerce (unsafeNth i e, unsafeNth j e, unsafeCoerce k e))  where
  (i, j, k) = unsafeCoerce d
compose (4, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e))  where
  (i0, i1, i2, i3) = unsafeCoerce d
compose (5, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e))  where
  (i0, i1, i2, i3, i4) = unsafeCoerce d
compose (6, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e, unsafeNth i5 e))  where
  (i0, i1, i2, i3, i4, i5) = unsafeCoerce d
compose _ _ = error "compose ran out of patience"

catC :: (Int, a) -> ((Int, c), d) -> ((Int, e), f) -> ((Int, g), h) -- these types are increasingly hilarious
-- 0 and 1 require 0-ary records, ignored per above
catC (2, fs) r p = ((2, unsafeCoerce (0::Int, 1::Int)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p)) where
  get :: (Int, Int) -> ((Int, c), d) -> ((Int, e), f) -> h
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p
  get _      _ _ = error "catC.get ran out of patience"
catC (3, fs) r p = ((3, unsafeCoerce (0::Int, 1::Int, 2::Int)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p, get (unsafeNth 2 fs) r p)) where
  get :: (Int, Int) -> ((Int, c), d) -> ((Int, e), f) -> h
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p
  get _      _ _ = error "catC.get ran out of patience"
catC (4, fs) r p = ((4::Int, unsafeCoerce (0::Int, 1::Int, 2::Int, 3::Int)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p, get (unsafeNth 2 fs) r p, get (unsafeNth 3 fs) r p)) where
  get :: (Int, Int) -> ((Int, c), d) -> ((Int, e), f) -> h
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p
  get _      _ _ = error "catC.get ran out of patience"
catC _ _ _       = error "catC ran out of patience"

field :: forall {c} {d} {e}. Int -> ((Int, c), d) -> e
field n ((_, d), r) = unsafeNth (unsafeNth n d) r

manyIn :: Int -> Int -> (Int, a)
manyIn 2 0 = (1, unsafeCoerce (MkSolo (1::Int)))
manyIn 2 1 = (1, unsafeCoerce (MkSolo (0::Int)))
manyIn 3 0 = (2, unsafeCoerce (1::Int, 2::Int))
manyIn 3 1 = (2, unsafeCoerce (0::Int, 2::Int))
manyIn 3 2 = (2, unsafeCoerce (0::Int, 1::Int))
manyIn 4 0 = (3, unsafeCoerce (1::Int, 2::Int, 3::Int))
manyIn 4 1 = (3, unsafeCoerce (0::Int, 2::Int, 3::Int))
manyIn 4 2 = (3, unsafeCoerce (0::Int, 1::Int, 3::Int))
manyIn 4 3 = (3, unsafeCoerce (0::Int, 1::Int, 2::Int))
manyIn 5 0 = (4, unsafeCoerce (1::Int, 2::Int, 3::Int, 4::Int))
manyIn 5 1 = (4, unsafeCoerce (0::Int, 2::Int, 3::Int, 4::Int))
manyIn 5 2 = (4, unsafeCoerce (0::Int, 1::Int, 3::Int, 4::Int))
manyIn 5 3 = (4, unsafeCoerce (0::Int, 1::Int, 2::Int, 4::Int))
manyIn 5 4 = (4, unsafeCoerce (0::Int, 1::Int, 2::Int, 3::Int))
manyIn _ _ = error "manyIn"

brn :: forall {a} {b} {d} {f} {c}. (Int, a) -> ((Int, b) -> c) -> ((Int, d) -> c) -> ((Int, f) -> c)
brn (_, d) f g (k, v) = if n == (0::Int) then f (j, unsafeCoerce v) else g (j, unsafeCoerce v) where
  (n, j) = unsafeNth k d

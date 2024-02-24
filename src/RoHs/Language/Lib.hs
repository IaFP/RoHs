{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- {-# OPTIONS -fforce-recomp -dcore-lint -ddump-simpl -ddump-ds-preopt -fplugin RoHs.Plugin #-}
{-# OPTIONS -fforce-recomp -dcore-lint -ddump-if-trace -dverbose-core2core -fplugin RoHs.Plugin -fplugin-opt debug #-}

module RoHs.Language.Lib (
    case0
  , con0
  , sel0
  -- , con1
  -- , case1
  , fstC, sndC, unsafeNth, compose
               , module RoHs.Language.Primitives
               , module RoHs.Language.Types
               ) where

{-
A module for library of operations on rows and variants
It also exports the Primitives, so no need for users to explicitly import it again
-}

import RoHs.Language.Types
import RoHs.Language.Primitives
import Data.Tuple
import Unsafe.Coerce


-- and we can define

con0 :: forall s {t} {z}. R '[s := t] ~<~ z => t -> V0 z
con0 x = inj0 (labV0 @s x)

case0 :: forall s {t} {u}. (t -> u) -> V0 (R '[s := t]) -> u
case0 f = f . unlabV0   -- I am surprised GHC can figure this out... and somewhat concerned about what it's actually figured out


sel0 :: forall s {t} {z}. R '[s := t] ~<~ z => R0 z -> t
sel0 r = unlabR0 @s (prj0 r)

-- con1 :: forall s {f} {t} {z}. R '[s := f] ~<~ z => f t -> V1 z t
-- con1 x = inj1 (labV1 @s x)

-- case1 :: forall s {f} {t} {u}. (f t -> u) -> V1 (R '[s := f]) t -> u
-- case1 f = f . unlabV1


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
compose (0, _) _ = (0, unsafeCoerce ())
compose (1, d) (_, e) = (1, unsafeCoerce (MkSolo (unsafeNth i e))) where
  MkSolo i = unsafeCoerce d
compose (2, d) (_, e) = (2, unsafeCoerce (unsafeNth i e, unsafeNth j e))  where
  (i, j) = unsafeCoerce d
compose (3, d) (_, e) = (3, unsafeCoerce (unsafeNth i d, unsafeNth j d, unsafeCoerce k d ))  where
  (i, j, k) = unsafeCoerce d
compose (4, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e))  where
  (i0, i1, i2, i3) = unsafeCoerce d
compose (5, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e))  where
  (i0, i1, i2, i3, i4) = unsafeCoerce d
compose (6, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e, unsafeNth i5 e))  where
  (i0, i1, i2, i3, i4, i5) = unsafeCoerce d

{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS -fforce-recomp -dcore-lint -ddump-simpl -ddump-ds-preopt -fplugin RoHsPlugin #-}

module RoHsLib (con0, case0, con1, case1

               , module RoHsPrimitives
               ) where

{-
A module for library of operations on rows and variants
It also exports the Primitives, so no need for users to explicitly import it again
-}

import Common
import RoHsPrimitives


-- and we can define

con0 :: forall s {t} {z}. R '[s := t] ~<~ z => t -> V0 z
con0 x = inj0 (labV0 @s x)

case0 :: forall s {t} {u}. (t -> u) -> V0 (R '[s := t]) -> u
case0 f = f . unlabV0   -- I am surprised GHC can figure this out... and somewhat concerned about what it's actually figured out

con1 :: forall s {f} {t} {z}. R '[s := f] ~<~ z => f t -> V1 z t
con1 x = inj1 (labV1 @s x)

case1 :: forall s {f} {t} {u}. (f t -> u) -> V1 (R '[s := f]) t -> u
case1 f = f . unlabV1

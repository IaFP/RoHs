{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module RoHs.Language.Types where

import GHC.Base
import Unsafe.Coerce
import Data.Tuple

data Row :: Type -> Type

type family R (assocs :: [Assoc a]) :: Row a

data Assoc :: Type -> Type where
  (:=) :: Symbol -> a -> Assoc a

type Label = Symbol

class (~<~) (a :: Row t) (b :: Row t)
-- probably shouldn't have user instances of this class... :P

-- This is what I really want:
type family (~+~) (a :: Row t) (b :: Row t) = (c :: Row t)
    -- | c a -> b, c b -> a
    where
-- But that's more than just an injective type family.  We can make more
-- progress using the following definition:

class (x ~<~ z, y ~<~ z) => Plus (x :: Row t) (y :: Row t) (z :: Row t)
   | x y -> z,
     x z -> y,
     y z -> x


-- Records ahoy
type family R0 (r :: Row Type) = (q :: Type) | q -> r where
type family R1 (r :: Row (a -> Type)) = (q :: a -> Type) | q -> r where -- term level re


-- Let's repeat the tedium for variants...
type family V0 (r :: Row Type) = (v :: Type) | v -> r where
type family V1 (r :: Row (a -> Type)) = (v :: a -> Type) | v -> r where


-- Okay, let's try Rω again.  Same fundamental problem: we need to replace the use of type-level λs.
type family Each (f :: (a -> b)) (r :: Row a) :: Row b where
  -- I have a feeling that this is not going to work out for me... see the
  -- `constants` example below.  The crux of the issue is that I want to
  -- "axiomatize" `Each f z` with statements like
  --             `y ~<~ z => Each f y ~<~ Each f z`
  -- ... but GHC is (reasonably...) upset at constraints on type synonyms.
  --
  -- Perhaps I could solve this problem by switching `Each` to a constraint-with
  -- -fundep, but that seems hard to use...

class All (cls :: a -> Constraint) (r :: Row a)




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
unsafeNth _ _ = error "unsafeNth exceeded limit"

compose :: (Int, a) -> (Int, b) -> (Int, c)
-- again, we seem to need to iterate our definition... I'll do only a few cases
-- I am concerned that we're going to stack up `unsafeCoerce`s, and that will
-- lead to underspecified types (and so misbehaving coercions) in the middle...
compose (0, _) _ = (0, unsafeCoerce ())
compose (1, d) (_, e) = (1, unsafeCoerce (MkSolo (unsafeNth i e))) where
   MkSolo i = unsafeCoerce d
compose (2, d) (_, e) = (2, unsafeCoerce (unsafeNth i e, unsafeNth j e))  where
   (i, j) = unsafeCoerce d
compose (3, d) (_, e) = (3, unsafeCoerce (unsafeNth i e, unsafeNth j e, unsafeCoerce k e ))  where
   (i, j, k) = unsafeCoerce d
compose (4, d) (_, e) = (4, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e))  where
   (i0, i1, i2, i3) = unsafeCoerce d
compose (5, d) (_, e) = (5, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e))  where
   (i0, i1, i2, i3, i4) = unsafeCoerce d
compose (6, d) (_, e) = (6, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e, unsafeNth i5 e))  where
   (i0, i1, i2, i3, i4, i5) = unsafeCoerce d
compose (7, d) (_, e) = (7, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e, unsafeNth i5 e, unsafeNth i6 e))  where
   (i0, i1, i2, i3, i4, i5, i6) = unsafeCoerce d
compose (8, d) (_, e) = (8, unsafeCoerce (unsafeNth i0 e, unsafeNth i1 e, unsafeNth i2 e, unsafeNth i3 e, unsafeNth i4 e, unsafeNth i5 e, unsafeNth i6 e, unsafeNth i7 e))  where
   (i0, i1, i2, i3, i4, i5, i6, i7) = unsafeCoerce d
compose _ _ = error "compose ran out of patience"

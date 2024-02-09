{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Common where

import GHC.Base

data Row :: Type -> Type where
  R :: [Assoc a] -> Row a

data Assoc :: Type -> Type where
  (:=) :: Symbol -> a -> Assoc a

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

-- But if this is going to *actually* work, we're going to need to step in with
-- some defaulting to actually fix `z`s.


-- Records ahoy
type family R0 :: Row Type -> Type where -- how do the terms which inhabit this type look like
type family R1 :: Row (a -> Type) -> a -> Type where -- term level re


-- Let's repeat the tedium for variants...
type family V0 :: Row Type -> Type where
type family V1 :: Row (a -> Type) -> a -> Type where


-- Okay, let's try Rω again.  Same fundamental problem: we need to replace the use of type-level λs.
type family Each (f :: (a -> b)) (r :: Row a) :: Row b where
  -- I have a feeling that this is not going to work out for me... see the
  -- `constants` example below.  The crux of the issue is that I want to
  -- "axiomatize" `Each f z` with statements like `y ~<~ z => Each f y ~<~ Each
  -- f z`... but GHC is (reasonably...) upset at constraints on type synonyms.
  --
  -- Perhaps I could solve this problem by switching `Each` to a constraint-with
  -- -fundep, but that seems hard to use...

type family All (cls :: a -> Constraint) (r :: Row a) :: Constraint where

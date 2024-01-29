{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Common where

import GHC.Base
import GHC.TypeLits

data Row :: Type -> Type where
  R :: [Assoc a] -> Row a

data Assoc :: Type -> Type where
  (:=) :: Symbol -> a -> Assoc a

-- instance Eq (Assoc a) where
--   (s := _) == (s' := _) = sameSymbol s s'

-- instance Ord (Assoc a) where
--   (s := x) <= (s' := y) = s <= s'

class (~<~) (a :: Row t) (b :: Row t)
  -- probably shouldn't have user instances of this class... :P

-- This is what I really want:
type family (~+~) (a :: Row t) (b :: Row t) = (c :: Row t)
    -- | c a -> b, c b -> a
    where
-- But that's more than just an injective type family.  We can make more
-- progress using the following definition:

class Plus (x :: Row t) (y :: Row t) (z :: Row t) | x y -> z, x z -> y, y z -> x

-- But if this is going to *actually* work, we're going to need to step in with
-- some defaulting to actually fix `z`s.

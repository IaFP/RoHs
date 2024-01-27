module Internal where

import Data.Tuple
import Unsafe.Coerce

---------------------------------------------------------------------------------
-- Starting point: tuples are like arrays, let's trust our bounds checking

unsafeNth :: Int -> a -> b
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

--------------------------------------------------------------------------------
-- Evidence

-- The evidence for a *ground* constraint
--
--    R '[s0 := t0, ..., sk := tk] ~<~ R '[s'0 := t'0, ..., s'l := t'l]
--
-- is a k-ary tuple of the indices of each `si` in the `s'j`s.

-- Concern: do we need to know the *sizes* of evidence to implement generic
-- operations?  For example, we might want to have a general composition
-- operator `(r0 ~<~ r1) -> (r1 ~<~ r2) -> (r0 ~<~ r2)`... but how can we know
-- how big a record to generate?

-- Eventual concern 2: We'll need to know the *sizes* of row types *in general*
-- to be able to implement `ana` and `syn`.

-- For now, let's assume that evidence is a pair (k, r) where r is the k-tuple
-- as above.  Or, perhaps we want a k+1 tuple (k, i0, .., ik)... would this
-- actually make a difference?

compose :: (Int, a) -> (Int, b) -> (Int, c)
-- again, we seem to need to iterate our definition... I'll do only a few cases
-- I am concerned that we're going to stack up `unsafeCoerce`s, and that will be
-- somehow a bad thing...
compose (0, _) _ = (0, unsafeCoerce ())
compose (1, d) (_, e) = (1, unsafeCoerce (MkSolo (unsafeNth i d))) where
  MkSolo i = unsafeCoerce d
compose (2, d) (_, e) = (2, unsafeCoerce (unsafeNth i d, unsafeNth j d))  where
  (i, j) = unsafeCoerce d
compose (3, d) (_, e) = (3, unsafeCoerce (unsafeNth i d, unsafeNth j d, unsafeCoerce ))  where
  (i, j, k) = unsafeCoerce d

---------------------------------------------------------------------------------
-- Records
--
-- A 

--------------------------------------------------------------------------------
-- Variants
--
-- 


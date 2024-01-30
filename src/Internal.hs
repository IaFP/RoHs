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

-- Examples

e1 :: (Int, (Int, Int)) -- (R '["y" := Bool, "z" := Int]) ~<~ (R '["x" := Int, "y" := Bool, "z" := Int, "w" := String])
e1 = (2, (1, 2))

e2 :: (Int, Solo Int) -- (R '["y" := Bool]) ~<~ (R '["y" := Bool, "z" := Int])
e2 = (1, MkSolo 0)

e2' :: (Int, Solo Int) -- (R '["z" := Int]) ~<~ (R '["y" := Bool, "z" := Int])
e2' = (1, MkSolo 1)

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

-- The evidence for a *ground* constraint 
--
--   R '[s0 := t0, ..., sj := tj] ~+~ R '[s0' := t0', ..., sk' := tk'] ~ R '[s0'' := t0'', ..., sl'' := tl'']
--
-- is supposed to be an invertable function from the si'' to the si + si'.
--
-- My current theory is: we represent that function as a pair (l, r) where r is
-- an l-ary tuple, each entry of which is a pair (0, i) or (1, j).

-- Examples

e3 :: (Int, ((Int, Int), (Int, Int))) -- (R '["y" := Bool]) ~+~ (R '["z" := Int]) ~ (R '["y" := Bool, "z" := Int])
e3 = (2, ((0, 0), (1, 0)))

e3' :: (Int, ((Int, Int), (Int, Int))) --  (R '["z" := Int]) ~+~ (R '["y" := Bool]) ~ (R '["y" := Bool, "z" := Int])
e3' = (2, ((1, 0), (0, 0)))

e4 :: (Int, ((Int, Int), (Int, Int), (Int, Int), (Int, Int))) -- (R '["y" := Bool, "z" := Int]) ~+~ (R '["x" := Int, "w" := String]) ~ (R '["x" := Int, "y" := Bool, "z" := Int, "w" := String])
e4 = (4, ((1, 0), (0, 0), (0, 1), (1, 1)))


---------------------------------------------------------------------------------
-- Records
--
-- So there are a couple of ways we could do records.  Approach (1) would be to
-- represent an n-ary record as an n-tuple; the 0th element is in position 0,
-- and so forth.  The nice thing about this is that it's simple.  The not-nice
-- thing is that projection becomes a *linear* operation, which has to copy each
-- cell of the input record  Approach (2) would be to store a lookup table in
-- each record; projection would then just be composition of lookup tables.

-- Upon starting to implement approach 1, I discovered another problem---`prj`
-- gets duplicated for each size of record.  I'm bored of that gimmick, so let's
-- just start with approach 2.


-- TODO: what about 0-ary records?  Ignoring for now, I suspect...


prj :: (Int, a) -> ((Int, c), d) -> ((Int, e), d)
prj d (e, r) = (compose d e, r)

field :: Int -> ((Int, c), d) -> e
field n ((_, d), r) = unsafeNth (unsafeNth n d) r

field0 :: ((Int, c), d) -> e    -- essentially unlabel for records...
field0 = field 0

cat :: (Int, a) -> ((Int, c), d) -> ((Int, e), f) -> ((Int, g), h) -- these types are increasingly hilarious
-- 0 and 1 require 0-ary records, ignored per above
cat (2, fs) r p = ((2, unsafeCoerce (0, 1)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p)) where
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p
cat (3, fs) r p = ((3, unsafeCoerce (0, 1, 2)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p, get (unsafeNth 2 fs) r p)) where
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p
cat (4, fs) r p = ((4, unsafeCoerce (0, 1, 2, 3)), unsafeCoerce (get (unsafeNth 0 fs) r p, get (unsafeNth 1 fs) r p, get (unsafeNth 2 fs) r p, get (unsafeNth 3 fs) r p)) where
  get (0, n) r _ = field n r
  get (1, n) _ p = field n p



-- Umm right, let's see if anything does anything
-- Also maybe we should be flattening the end of this structure...

r1 :: ((Int, (Int, Int, Int, Int)), (Int, Bool, Int, String))    -- R0 (R '["x" := Int, "y" := Bool, "z" := Int, "w" := String])
r1 = ((4, (0, 1, 2, 3)), (1, True, 2, "Foo"))

r2 :: ((Int, (Int, Int)), (Int, Bool))                 -- R0 (R '["y" := Bool, "z" := Int])   c.f. Apoorv, can we just sort field names...
r2 = ((2, (1, 0)), (3, False))

-- examples

x1 :: Int
x1 = field0 r1

x2 :: Bool
x2 = field0 r2

-- okay containment

x3 :: Bool
x3 = field0 (prj e1 r1)

x4 :: Int
x4 = field0 (prj e2' r2)

x5 :: Int
x5 = field0 (prj (compose e2' e1) r1)

r3 :: ((Int, Solo Int), Solo Bool)
r3 = ((1, MkSolo 0), MkSolo True)

r4 :: ((Int, Solo Int), Solo Int)
r4 = ((1, MkSolo 0), MkSolo 14)

r5 :: ((Int, (Int, Int)), (Bool, Int))
r5 = cat e3 r3 r4

x5_0 :: Bool; x5_1 :: Int
(x5_0, x5_1) = (field 0 r5, field 1 r5)

r5' :: ((Int, (Int, Int)), (Bool, Int))
r5' = cat e3' r4 r3

x5'_0 :: Bool; x5'_1 :: Int
(x5'_0, x5'_1) = (field 0 r5', field 1 r5')

r6 :: ((Int, (Int, Int)), (String, Int))
r6 = ((2, (1, 0)), ("Bar", 42))

r7 :: ((Int, (Int, Int, Int, Int)), (Int, Bool, Int, String))
r7 = cat e4 (cat e3 r3 r4) r6

x7_0 :: Int; x7_1 :: Bool; x7_2 :: Int; x7_3 :: String
(x7_0, x7_1, x7_2, x7_3) = (field 0 r7, field 1 r7, field 2 r7, field 3 r7)


--------------------------------------------------------------------------------
-- Variants
--
-- 


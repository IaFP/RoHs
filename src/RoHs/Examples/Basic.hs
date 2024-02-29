{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHsPlugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -ddump-ds -ddump-simpl -dverbose-core2core -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -dcore-lint -ddump-ds -ddump-simpl -dverbose-core2core -fplugin RoHs.Plugin #-}
{-# OPTIONS -fforce-recomp -dcore-lint -fplugin RoHs.Plugin #-}

module RoHs.Examples.Basic where

import RoHs.Language.Lib

import Data.Proxy

default (Int)

singleton_foo_Int :: R0 (R '["x" := Int]); singleton_foo_Int = labR0 @"x" 1

singleton_foo_Bool :: R0 (R '["y" := Bool])
singleton_foo_Bool  = labR0 @"y" True

-- See if we can do anything
foo :: R0 (R '["x" := Int] ~+~ (R '["y" := Bool]))
foo = singleton_foo_Int `cat0` singleton_foo_Bool

bar :: (V0 (R '["false" := Bool] ~+~  R '["true" := Int])) -> Int
bar = case0 @"true" id `brn0` case0 @"false" (\b -> if b then 0 else 1)

slice_foo_id :: R0 (R '["y" := Bool, "x" := Int])
slice_foo_id = prj0 foo

slice_foo :: R0 (R '["y" := Bool])
slice_foo = prj0 foo

unwrap_slice_foo :: Bool
unwrap_slice_foo = unlabR0 @"y" slice_foo

-- Demonstrates the (first features of the) source plugin: source plugin adds
-- needed `Plus` constraint.
foo1 :: R0 x -> R0 y -> R0 (x ~+~ y)
foo1 r s = r `cat0` s

-- (1) foo :: R0 (R '["x" := Int, "x" := Bool])) -- user written

-- (2) foo :: R0 (R '["x" := Int] ~+~ (R '["y" := Bool])) -- src plugin

-- (3) foo :: R0 (R '["x" := Int] ~+~ (R '["y" := Bool]))
-- tc-plugin checks for this Plus (R '["x" := Int]) R ('["y" := Bool]) (R '["x" := Int] ~+~ (R '["y" := Bool]))
foo_works :: Plus (R '["x" := Int]) ((R '["y" := Bool])) z => R0 z
foo_works =  (labR0 @"x" (1::Int)) `cat0` (labR0 @"y" (False::Bool))

--

bar1 ::(V0 (R '["false" := Bool] ~+~ R '["true" := Int])) -> Int
bar1 = case0 @"true" id `brn0` case0 @"false" (\b -> if b then 0 else 1)

bar1' ::(V0 (R '["y" := Bool] ~+~ R '["x" := Int])) -> Int
bar1' = case0 @"x" id `brn0` case0 @"y" (\b -> if b then 0 else 1)

answer_to_everything :: Int
answer_to_everything = bar1' (inj0 (labV0 @"x" (42::Int)))

-- qqqqq :: _
qqqqq = brn0 (case0 @"x" id) (case0 @"y" (\b -> if b then 0 else 1))

-- This is a *less* compelling argument against than I thought, but still
-- concerned about the type argument to inj0.
-- bar2 :: forall z y.
--         -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
--         (R '["x" := Bool] ~+~ z ~ y,
--          -- These three constraint should all be solvable, *given the definition above*
--          R '["x" := Bool] ~<~ R '["x" := Bool],
--          R '["x" := Bool] ~<~ y,
--          z ~<~ y) =>
--         V0 (R '["x" := Int] ~+~ z) -> V0 y

--        inj0 @z

bar2 :: forall z y1 y2.
        -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
        (Plus (R '["x" := Integer]) z y1,    -- `Integer` so defaulting doesn't get in the way
         Plus (R '["x" := Bool]) z y2) =>
        V0 y1 -> V0 y2
bar2 = case0 @"x" (\i -> con0 @"x" (i == zero)) `brn0` inj0
  where zero :: Integer = 0

test_foo :: Bool -> Bool
test_foo b = (xcase `brn0` ycase) (con0 @"X" b) where
  xcase = case0 @"X" not
  ycase = case0 @"Y" id


showV :: forall z. All Show z => V0 z -> String
showV = anaA0 @Show (const show)

showV1 :: forall z. All Show z => V0 z -> String
showV1 = anaA0 @Show f where
  f _ x = show x

-- But apparently adding the type signature will make `f` no longer have the
-- right type.  I am concerned that I am missing something fundamental here...

--   f :: forall s y u. (Plus (R '[s := u]) y z,
--                       R '[s := u] ~<~ z,
--                       y ~<~ z,
--                       Show u) =>
--                       u -> String
--   f = show

-- constants :: forall t z.
--              (forall s f u z. R '[s := u] ~<~ z => R '[s := f u] ~<~ Each f z) =>
--              V0 z -> V0 (Each ((->) t) z)
-- constants = ana0 f where
--   f x = con0 (\y -> x)

eqV :: forall z. All Eq z => V0 z -> V0 z -> Bool
eqV v w = anaA0 @Eq g w where
  g :: forall s y t. (Plus (R '[s := t]) y z, Eq t)
                  =>  Proxy s -> t -> Bool
  g _ x = (case0 @s (\y -> x == y) `brn0` const False) v

eqV' :: V0 (R '["x" := Int, "y" := Bool]) -> V0 (R '["x" := Int, "y" := Bool]) -> Bool
eqV' = eqV

fmapV :: forall a b z. All Functor z => (a -> b) -> V1 z a -> V1 z b
fmapV f = anaA1 @Functor g where

  -- Without the `Proxy s` argument, `g` types fine but doesn't play well as n
  -- argument to `anaA1`.... !!??

  -- Can't get away without the type annotation here... even if I try to pattern
  -- match on the proxy.  Let's pretend I understand anything.
  g :: forall s y f. (Plus (R '[s := f]) y z, Functor f)
                  => Proxy s -> f a -> V1 z b
  g _ x = con1 @s (fmap f x)

-- This should be enough to do something dumb.  Let's try....
data Z k a = Z k
  deriving Functor
data O a    = O a
  deriving Functor
data T a    = T a a
  deriving Functor

newtype Mu f = Mk {unwrap :: f (Mu f)}

type BigR = R '["Const" := Z Int] ~+~  R '["Add" := T] ~+~ R '["Double" := O]
type SmallR = R '["Const" := Z Int] ~+~ R '["Add" := T]


desugar' :: forall bigr smallr.
           (-- These are essentially part of the type
            Plus (R '["Double" := O]) smallr bigr,
            All Functor smallr,
            R '["Add" := T] ~<~ smallr
           ) =>
           Mu (V1 bigr) -> Mu (V1 smallr)
desugar' (Mk e) = Mk ((double `brn1` (fmapV desugar' . inj1)) e) where
  double = case1 @"Double" (\(O x) -> con1 @"Add" (T (desugar' x) (desugar' x)))

desugar :: Mu (V1 BigR) -> Mu (V1 SmallR)
-- Here's a very explicit type...
-- desugar = desugar'
desugar (Mk e) = Mk ((double `brn1` (fmapV desugar . inj1)) e) where
  double = case1 @"Double" (\(O x) -> con1 @"Add" (T (desugar x) (desugar x)))


three :: Mu (V1 SmallR)
three = Mk (con1 @"Add" (T (Mk (con1 @"Const" (Z (1::Int))))
                           (Mk (con1 @"Const" (Z (2::Int))))))


constCase :: forall {k} {u} {a :: k} {p}. V0 (R '["Const" := Z u a]) -> p -> u
addCase :: Num u => V0 (R '["Add" := T t]) -> (t -> u) -> u
dblCase :: forall {k} {u} {t} {a :: k}. Num u
        => V0 (R '["Double" := Z t a]) -> (t -> u) -> u
negCase :: Num u => V0 (R '["Negate" := O t]) -> (t -> u) -> u


constCase e r = case0 @"Const" (\(Z n) -> n) e
addCase   e r = case0 @"Add"   (\(T e1 e2) -> r e1 + r e2) e
dblCase   e r = case0 @"Double" (\(Z e) -> r e + r e) e
negCase   e r = case0 @"Negate" (\(O e) -> - r e) e


-- evals (Mk e) = (constCase `brn1` addCase) e where
--   constCase = case0 @"Const" (\(Z n) -> n)
--   addCase   = case0 @"Add"   (\(T e1 e2) -> evals e1 + evals e2)


cases :: ((Mu f -> t) -> f (Mu f) -> t) -> Mu f -> t
cases f (Mk e) = f (cases f) e


-- evals' :: Mu (V1 SmallR) -> Int
-- evals' = cases (constCase `brn1` addCase)

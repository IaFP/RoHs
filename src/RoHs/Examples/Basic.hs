{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}

module RoHs.Examples.Basic where

import RoHs.Language.Lib

import Data.Proxy

default (Int)

singleton_foo_Int :: R0 (R '["x" := Int])
singleton_foo_Int = labR0 @"x" 1

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

-- This should be enough to do something dumb.  Let's try....


data Zero t e = Z t     deriving Functor
data One e    = O e     deriving Functor
data Two e    = T e e   deriving Functor

data Mu f     = Mk (f (Mu f))

instance Show t => Show (Zero t e) where
  show (Z t) =  "Z " ++ show t

-- instance All Functor z => Functor (V1 z) where
--   fmap f v = anaA1 @Functor (\_ d -> fmap f d) v

fmapV :: All Functor z => (a -> b) -> V1 z a -> V1 z b
fmapV f = anaA1 @Functor (\(_ :: Proxy s) d -> con1 @s (fmap f d))

-- recursive injection

injR :: (y ~<~ z, All Functor y) => Mu (V1 y) -> Mu (V1 z)
injR (Mk e) = Mk (inj1 (fmapV injR e))

-- expressions

-- We seem to need type synonyms to be declared in sorted order... need to track
-- down why.
--
type SmallR = R ["Const" := Zero Int, "Add" := Two]
type BigR   = R ["Double" := One, "Add" := Two, "Const" := Zero Int]

-- type SmallR = R ["Add" := Two, "Const" := Zero Int]
-- type BigR = R ["Add" := Two, "Const" := Zero Int, "Double" := One]

-- constructors

mkC :: R '["Const" := Zero Int] ~<~ z => Int -> Mu (V1 z)
mkC n = Mk (con1 @"Const" (Z n))

mkA :: R '["Add" := Two] ~<~ z => Mu (V1 z) -> Mu (V1 z) -> Mu (V1 z)
mkA e1 e2 = Mk (con1 @"Add" (T e1 e2))

mkD :: R '["Double" := One] ~<~ z => Mu (V1 z) -> Mu (V1 z)
mkD e = Mk (con1 @"Double" (O e))

-- examples
oneC :: Mu (V1 (R '["Const" := Zero Int]))
oneC = (mkC 1)

zeroC :: Mu (V1 (R '["Const" := Zero Int]))
zeroC = (mkC 0)


threeS :: Mu (V1 SmallR)
threeS = mkA (mkC 1) (mkC 2)

threeB :: Mu (V1 BigR)
threeB = mkA (mkC 1) (mkC 2)

fourB :: Mu (V1 BigR)
fourB = mkD (mkC 2)


fourS :: Mu (V1 SmallR)
fourS = desugar fourB -- without the type annotation GHC type checker generates a weird core which doesn't core-lint

-- folds

-- check order compared to paper, paper is wrong
cases :: (V1 z (Mu (V1 z)) -> (Mu (V1 z) -> r) -> r) -> Mu (V1 z) -> r
cases f (Mk e) = let x = cases f in f e x

foldV :: All Functor z => (V1 z r -> r) -> Mu (V1 z) -> r
foldV f (Mk e) = f (fmapV (foldV f) e)

class MyShow a where
  myShow :: a -> String
  myShow2 :: a -> String

instance MyShow Int where
    myShow _ = "A"
    myShow2 a = show a
-- showing

showC :: V1 (R '["Const" := Zero Int]) t -> p -> String
showA :: V1 (R '["Add" := Two]) t -> (t -> String) -> String
showD :: V1 (R '["Double" := One]) t -> (t -> String) -> String

showC e _ = case1 @"Const"  (\(Z n) -> show n) e
showA e r = case1 @"Add"    (\(T e1 e2) -> "(" ++ r e1 ++ " + " ++ r e2 ++ ")") e
showD e' r = case1 @"Double" (\(O e) -> "(2 * " ++ r e ++ ")") e'

-- eta expanding so GHC is okay with the Show constraint from showC.

showS :: Mu (V1 SmallR) -> String
showB :: Mu (V1 BigR) -> String

showS = cases (showC `brn1` showA)
showB = cases (showC `brn1` (showD `brn1` showA))

-- evaluating
evalC :: V1 (R '["Const" := Zero Int]) t -> p -> Int
evalA :: V1 (R '["Add" := Two]) t -> (t -> Int) -> Int
evalD :: V1 (R '["Double" := One]) t -> (t -> Int) -> Int

evalC e _ = case1 @"Const"  (\(Z (n :: Int)) -> n) e
evalA e r = case1 @"Add"    (\(T e1 e2) -> r e1 + r e2) e
evalD e' r = case1 @"Double" (\(O e) -> 2 * r e) e'


evalS :: Mu (V1 SmallR) -> Int
evalB :: Mu (V1 BigR) -> Int

evalS   = cases (evalA `brn1` evalC)
evalB   = cases ((evalA `brn1` evalD) `brn1` evalC)

-- desugaring

desugar :: (R '["Add" := Two] ~<~ y, All Functor (R '["Double" := One] ~+~ y)) => Mu (V1 (R '["Double" := One] ~+~ y)) -> Mu (V1 y)
desugar = foldV (desD `brn1` (Mk . inj1)) where
  -- desD :: V1 (R '["Double" := One]) (Mu (V1 z)) -> Mu (V1 z)
  desD = case1 @"Double" (\(O e) -> mkA e e)

numFour :: Int
numFour = evalB fourB

showFour :: String
showFour = showB fourB

evalOneC :: Int
evalOneC = cases evalC oneC

showOneC :: String
showOneC = cases showC oneC

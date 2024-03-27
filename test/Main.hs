
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}


-- Make sure you have `cabal configure --enable-tests` before running this
-- {-# OPTIONS -fforce-recomp -ddump-ds -ddump-simpl -dsuppress-module-prefixes -dsuppress-idinfo -dsuppress-coercions -fplugin RoHs.Plugin #-}

{-# OPTIONS  -fforce-recomp -ddump-tc-trace -fplugin RoHs.Plugin #-}

module Main where

import RoHs.Language.Lib

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Test.Tasty.SmallCheck as SC
-- import Test.Tasty.QuickCheck as QC


main :: IO (())
main = defaultMain tests

tests :: TestTree
tests = testGroup "TestSuite" [ units, properties, expectFail fails ]

rec1 :: R0 (R '["x" := Int])
rec1 = labR0 @"x" (1::Int)

rec2 :: R0 (R '["y" := Bool])
rec2 = labR0 @"y" (True::Bool)


-- Same labels should give an error
-- same_labels :: R0 (R '["x" := Int] ~+~ (R '["x" := Bool]))
-- same_labels = s1 `cat0` s2

-- curried_labs :: forall z.  R0 z -> R0 (R '["x" := Int] ~+~ z)
-- curried_labs y = s1 `cat0` y

-- should_fail = curried_lables s3

-- row_int_bool :: R0 (R '["x" := Int, "y" := Bool])
-- row_int_bool = s1 `cat0` s3



properties :: TestTree
properties = testGroup "Properties Testsuite"
  [ SC.testProperty "unlabR0 . labR0 = id" $
      \ (x :: Int) -> (unlabR0 @"x" (labR0 @"x" x) == x)
  , SC.testProperty "Records are commutative" $
      \ (x :: Int) (y :: Int) -> let r1 :: R0 (R '["x" := Int, "y" := Int ]) = (labR0 @"y" y) `cat0` (labR0 @"x" x) in
                                   let r2 :: R0 (R '["y" := Int, "x" := Int ]) = (labR0 @"x" x) `cat0` (labR0 @"y" y) in
                                     (==) @Int (unlabR0 @"x" (prj0 r1)) (unlabR0 @"x" (prj0 r2))
  ]

units :: TestTree
units = testGroup "Unit Testsuite"
  [ testCase "Row unlabel after label is identity" $
      (unlabR0 @"x" (labR0 @"x" (1 :: Int))) @?= 1

  , testCase "concat is commutative" $
      (@?=) @Int (unlabR0 @"x" (prj0 $ cat0 rec1 rec2)) (unlabR0 @"x" (prj0 $ cat0 rec2 rec1))

  ]


fails :: TestTree
fails = testGroup "Fail Testsuite"
  [ testCase "Same label error" $
        (@?=) @Int (unlabR0 @"x" (prj0 $ rec1 `cat0` rec1)) 1
  ]

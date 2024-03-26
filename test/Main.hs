
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}


-- Make sure you have `cabal configure --enable-tests` before running this
-- TODO: move the test to its own module so that building it doesn't make the whole cabal
-- process crash
-- {-# OPTIONS -fforce-recomp -ddump-ds -ddump-simpl -dsuppress-module-prefixes -dsuppress-idinfo -dsuppress-coercions -fplugin RoHs.Plugin #-}

{-# OPTIONS  -fforce-recomp -fplugin RoHs.Plugin #-}

module Main where

import RoHs.Language.Lib
-- import RoHs.Examples.Basic

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.ExpectedFailure
import Test.Tasty.SmallCheck as SC
import Test.Tasty.QuickCheck as QC


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "TestSuite" [ units, properties ]


rec_lab_Int :: Int ->  R0 (R '["x" := Int])
rec_lab_Int x = labR0 @"x" x

rec_unlab_Int :: R0 (R '["x" := Int]) -> Int
rec_unlab_Int r = unlabR0 @"x" r

-- s1 :: R0 (R '["x" := Int])
-- s1 = labR0 @"x" (1::Int)

-- s2 :: R0 (R '["x" := Bool])
-- s2 = labR0 @"x" (True::Bool)

-- s3 :: R0 (R '["y" := Bool])
-- s3 = labR0 @"y" (True::Bool)

-- s4 :: R0 (R '["w" := Bool])
-- s4 = labR0 @"w" (True::Bool)

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
      \ (x :: Int) -> (rec_unlab_Int (rec_lab_Int x) == x)
  ]

units :: TestTree
units = testGroup "Unit Testsuite"
  [ testCase "Row unlabel after label is identity" $
      (unlabR0 @"x" (labR0 @"x" (1 :: Int))) @?= 1
  ]

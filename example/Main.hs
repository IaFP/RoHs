{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}

module Main where

import RoHs.Language.Lib
import RoHs.Examples.Variants
import RoHs.Examples.RecVariants1


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

main :: IO ()
main = do putStrLn $ "The ultimate answer: " ++ show answer_to_everything
          putStrLn $ ((Rec showVar) `brnr` (Rec showLam)) ~$~ idLam
          putStrLn $ idstr
          putStrLn $ showTerm appId

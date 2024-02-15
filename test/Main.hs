
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -ddump-simpl -ddump-ds-preopt -fplugin RoHsPlugin #-}
-- {-# OPTIONS -fforce-recomp -fplugin RoHsPlugin #-}


module Main where

import Common
import RoHsLib


s1 :: R0 (R '["x" := Int])
s1 = labR0 @"x" (1::Int)

s2 :: R0 (R '["x" := Bool])
s2 = labR0 @"x" (True::Bool)

-- Same labels should give an error
same_labels :: R0 (R '["x" := Int] ~+~ (R '["x" := Bool]))
same_labels = s1 `cat0` s2


main :: IO ()
main = putStrLn "Test suite not yet implemented."

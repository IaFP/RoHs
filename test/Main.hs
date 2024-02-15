
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}


-- Make sure you have `cabal configure --enable-tests` before running this
-- TODO: move the test to its own module so that building it doesn't make the whole cabal
-- process crash
{-# OPTIONS -fforce-recomp -fplugin RoHs.Plugin #-}
module Main where

import RoHs.Language.Lib

s1 :: R0 (R '["x" := Int])
s1 = labR0 @"x" (1::Int)

s2 :: R0 (R '["x" := Bool])
s2 = labR0 @"x" (True::Bool)

-- Same labels should give an error
-- same_labels :: R0 (R '["x" := Int] ~+~ (R '["x" := Bool]))
-- same_labels = s1 `cat0` s2

curried_lables :: forall z s t. (z ~ R '[s := t]) =>  R0 z -> R0 (R '["x" := Int] ~+~ z)
curried_lables y = s1 `cat0` y

should_fail = curried_lables s2


main :: IO ()
main = putStrLn "Test suite not yet implemented."

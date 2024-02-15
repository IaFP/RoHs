
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}

-- Make sure you have `cabal configure --enable-tests` before running this
-- TODO: move the test to its own module so that building it doesn't make the whole cabal
-- process crash
module Main where


main :: IO ()
main = putStrLn "Test suite not yet implemented."

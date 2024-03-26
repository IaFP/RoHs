
{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# OPTIONS -ddump-tc-trace -fforce-recomp -fplugin RoHs.Plugin #-}


module IllTyped.RowConcat (main) where

import RoHs.Language.Lib

s1 :: R0 (R '["x" := Int])
s1 = labR0 @"x" (1::Int)


err = unlabR0 @"y" s1 -- type error

{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -fplugin RoHs.Plugin #-}


module RoHs.Examples.Variants where

import RoHs.Language.Lib

import Data.Proxy
default (Int)


-- This should be enough to do something dumb.  Let's try....


data Zero t e = Z t     deriving Functor
data One e    = O e     deriving Functor
data Two e    = T e e   deriving Functor

newtype Mu f     = Mk (f (Mu f))

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

-- fourS :: Mu (V1 SmallR)
fourS = desugar fourB

-- folds

-- check order compared to paper, paper is wrong
cases :: (V1 z (Mu (V1 z)) -> (Mu (V1 z) -> r) -> r) -> Mu (V1 z) -> r
cases f (Mk e) = f e (cases f)

foldV :: All Functor z => (V1 z r -> r) -> Mu (V1 z) -> r
foldV f (Mk e) = f (fmapV (foldV f) e)

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
  desD = case1 @"Double" (\(O e) -> mkA e e)

numFour :: Int
numFour = evalB fourB

showFour :: String
showFour = showB fourB

evalOneC :: Int
evalOneC = cases evalC oneC

showOneC :: String
showOneC = cases showC oneC

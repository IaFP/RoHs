{-# LANGUAGE AllowAmbiguousTypes, DataKinds, TypeFamilies #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-ds -dverbose-core2core -dsuppress-module-prefixes -fplugin RoHs.Plugin #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
{-# OPTIONS_GHC -fplugin RoHs.Plugin #-}

module RoHs.Examples.Paper where

import Data.Proxy
import RoHs.Language.Types
import RoHs.Language.Lib

-- Examples that I claim to work in the paper
-- and some other ones that occur to me as I'm writing them

-- "Booleans"

type BoolR      = R ["True" := (), "False" := ()]

true :: V0 BoolR
true = inj0 (labV0 @"True" ())

notR :: V0 BoolR -> V0 BoolR
notR = case0 @"True"  (\() -> con0 @"False" ()) `brn0`
       case0 @"False" (\() -> con0 @"True" ())

type NullR      = R '["NULL" := ()]
type BoolOrNull = BoolR ~+~ NullR

true' :: V0 BoolOrNull
true' = con0 @"True" ()

true'' :: V0 BoolOrNull
true'' = inj0 true

-- This is the type we should have:
-- notR' :: BoolOrNull ~<~ z => V0 BoolOrNull -> V0 z
notR' :: (BoolR ~<~ z, NullR ~<~ z) => V0 BoolOrNull -> V0 z
notR' = (inj0 . notR) `brn0`    -- the paper is missing the call to inj
        case0 @"NULL" (\() -> con0 @"NULL" ())

showBR :: V0 BoolR -> String
showBR = case0 @"True"  (\() -> "True") `brn0`
         case0 @"False" (\() -> "False")

showBN :: V0 BoolOrNull -> String
showBN = showBR `brn0`
         case0 @"NULL" (\() -> "NULL")

-- functors and fixed points

data Zero t e = Z t     deriving Functor
data One e    = O e     deriving Functor
data Two e    = T e e   deriving Functor

data Mu f     = Mk (f (Mu f))

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

threeS :: Mu (V1 SmallR)
threeS = mkA (mkC 1) (mkC 2)

threeB :: Mu (V1 BigR)
threeB = mkA (mkC 1) (mkC 2)

fourB :: Mu (V1 BigR)
fourB = mkD (mkC 2)


-- fourS :: Mu (V1 SmallR)
fourS = desugar @SmallR fourB -- without the type annotation GHC type checker generates a weird core which doesn't core-lint

-- folds

-- check order compared to paper, paper is wrong
cases :: (V1 z (Mu (V1 z)) -> (Mu (V1 z) -> r) -> r) -> Mu (V1 z) -> r
cases f (Mk e) = f e (cases f)

foldV :: All Functor z => (V1 z r -> r) -> Mu (V1 z) -> r
foldV f (Mk e) = f (fmapV (foldV f) e)

class Show a => MyShow a where
  myShow :: a -> String

instance MyShow Int where
    myShow a = "A" ++ show a
-- showing

showC e _ = case1 @"Const"  (\(Z n) -> myShow n) e
showA e r = case1 @"Add"    (\(T e1 e2) -> "(" ++ r e1 ++ " + " ++ r e2 ++ ")") e
showD e' r = case1 @"Double" (\(O e) -> "(2 * " ++ r e ++ ")") e'

-- eta expanding so GHC is okay with the Show constraint from showC.
showS e = cases (showC `brn1` showA) e
showB e = cases (showC `brn1` (showD `brn1` showA)) e

-- evaluating

evalC e _ = case1 @"Const"  (\(Z (n :: Int)) -> n) e
evalA e r = case1 @"Add"    (\(T e1 e2) -> r e1 + r e2) e
evalD e' r = case1 @"Double" (\(O e) -> 2 * r e) e'

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

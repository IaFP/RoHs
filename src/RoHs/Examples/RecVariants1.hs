{-# LANGUAGE ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UnicodeSyntax #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -ddump-rn-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -ddump-tc-trace -fforce-recomp -dcore-lint -ddump-ds -O0 -dasm-lint -dcmm-lint -ddump-asm-native -ddump-exitify -fplugin RoHs.Plugin -fplugin-opt debug #-}
{-# OPTIONS -dcore-lint -O0 -fplugin RoHs.Plugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-rn-trace -dcore-lint -O0 -ddump-tc-trace -ddump-simpl -ddump-ds-preopt -dverbose-core2core -dsuppress-module-prefixes -dno-suppress-type-applications -ddump-cmm -fprint-typechecker-elaboration -fplugin RoHs.Plugin #-}


module RoHs.Examples.RecVariants1 where

import RoHs.Language.Lib
import RoHs.Examples.Variants


default (Int)

-- This works for one level of unwrapping a knot tied extensiblke variant

data t ~> u where
  Rec :: (forall y. z ~<~ y => V1 z (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u)
      -> Mu (V1 z) ~> u


brnr :: forall v w {vw} {u}. Plus v w vw => ((Mu (V1 v)) ~> u) -> ((Mu (V1 w)) ~> u) -> ((Mu (V1 vw)) ~> u)
brnr (Rec rfv) (Rec rfw) = Rec rfvw
  where
  rfvw :: forall y. vw ~<~ y => (V1 vw (Mu (V1 y))) -> (Mu (V1 y) -> u) -> u
  rfvw = brn1 @v @w rfv rfw

(~$~) :: (Mu (V1 x) ~> t) -> Mu (V1 x) -> t
(Rec f) ~$~ (Mk x) = f x (Rec f ~$~)

-- Example 1.
-- Combining Zero, Suc, with Zero, Pred

type NatPosR = R '[ "zeroP" := Zero (), "inc1" := One]
type NatNegR = R '[ "zeroN" := Zero (), "dec1" := One]


evalZP :: V1 (R '[ "zeroP" := Zero () ]) t -> p -> Int
evalIP :: V1 (R '[ "inc1" := One ]) t -> (t -> Int) -> Int

evalZP e _ = case1 @"zeroP" (\(Z ()) -> 0) e
evalIP e' r = case1 @"inc1" (\(O e) -> 1 + r e) e'


evalZN :: V1 (R '[ "zeroN" := Zero ()]) t -> p -> Int
evalIN :: V1 (R '[ "dec1" := One ]) t -> (t -> Int) -> Int

evalZN e _ = case1 @"zeroN" (\(Z ()) -> 0) e
evalIN e' r = case1 @"dec1" (\(O e) -> (r e) - 1) e'


mkZP :: R ('[ "zeroP" := Zero () ]) ~<~ z => Mu (V1 z)
mkZP =  Mk (con1 @"zeroP" (Z ()))

mkIP :: R ('[ "inc1" := One ]) ~<~ z => Mu (V1 z) -> Mu (V1 z)
mkIP e =  Mk (con1 @"inc1" (O e))

mkZN :: R ('[ "zeroN" := Zero () ]) ~<~ z => Mu (V1 z)
mkZN =  Mk (con1 @"zeroN" (Z ()))

mkIN :: R ('[ "dec1" := One ]) ~<~ z => Mu (V1 z) -> Mu (V1 z)
mkIN e =  Mk (con1 @"dec1" (O e))


evalP :: NatPosR ~<~ y => V1 NatPosR (Mu (V1 y)) -> (Mu (V1 y) -> Int) -> Int
evalN :: NatNegR ~<~ y => V1 NatNegR (Mu (V1 y)) -> (Mu (V1 y) -> Int) -> Int

evalP = evalZP `brn1` evalIP
evalN = evalZN `brn1` evalIN

evalPN :: Mu (V1 (NatPosR ~+~ NatNegR)) -> Int
evalPN = (~$~) ((Rec evalP) `brnr` (Rec evalN))


toNat :: Int -> Mu (V1 NatPosR)
toNat 0 = mkZP
toNat k = mkIP (toNat (k-1))


-- Example 2.
-- Untyped Lambda Calculus
type LamCR = R '[ "var" := Zero Int, "lam" := One, "app" := Two ]

type VarR = R '[ "var" := Zero Int ]
type AppR = R '[ "app" := One ]
type LamR = R '[ "app" := One ]

mkVar :: VarR ~<~ z => Int -> Mu (V1 z)
mkVar i = Mk (con1 @"var" (Z i))

mkLam :: forall x z. ( All Functor x, R '["lam" := One] ~<~ z, x ~<~ z)
      => Mu (V1 x) -> Mu (V1 z)
mkLam e = Mk (con1 @"lam" (O e'))
  where e' = injR @x @z e

mkApp :: forall x y z. (All Functor x, All Functor y,
          (R '["app" := Two] ~<~ z, x ~<~ z, y ~<~ z)) => Mu (V1 x) -> Mu (V1 y) -> Mu (V1 z)
mkApp e1 e2 = Mk (con1 @"app" (T e1' e2'))
  where e1' = injR @x @z e1
        e2' = injR @y @z e2


showVar :: V1 (R '["var" := Zero Int]) t -> p -> String
showVar e _ = case1 @"var" (\(Z (i::Int)) -> show i) e

showLam :: V1 (R '["lam" := One]) t -> (t -> String) -> String
showLam e r = case1 @"lam" (\(O b) -> "(\\ " ++ r b ++ ")") e

showApp :: V1 (R '["app" := Two]) t -> (t -> String) -> String
showApp e r = case1 @"app" (\(T fn a) -> (r fn)  ++ " " ++ (r a)) e

-- showTerm :: Mu (V1 LamCR) -> String
showTerm x = ((Rec showVar) `brnr` (Rec showLam) `brnr` (Rec showApp)) ~$~ x

-- showLamR :: Mu (V1 (R '["var" := Zero Int, "lam" := One])) -> String
showLamR x = ((Rec showVar) `brnr` (Rec showLam)) ~$~ x

type Env t = (Int -> V1 LamCR t)

extend :: Env t -> Env t
extend env = \ i -> env (i + 1)

evalVar :: V1 (R '["var" := Zero Int]) t -> p -> Env t -> V1 LamCR t
evalVar e _ env = case1 @"var" (\(Z (i::Int)) -> env i) e

evalLam :: V1 (R '["lam" := One]) (V1 LamCR t) -> (Env t -> V1 LamCR t -> V1 LamCR t) -> Env t -> V1 LamCR t
evalLam e r env = case1 @"lam" (\(O body) -> r (extend env) body) e

evalApp :: V1 (R '["app" := Two]) t -> (Env t -> V1 LamCR t -> V1 LamCR t) -> Env t -> V1 LamCR t
evalApp e r env = case1 @"app" (\(T fn a) -> undefined) e

var :: forall z. (VarR ~<~ z) => Mu (V1 z)
var = mkVar 0

idLam :: forall z. (All Functor z, R '["var" := Zero Int, "lam" := One] ~<~ z) => Mu (V1 z)
idLam = mkLam (mkVar @z 0)


-- idLamInst = idLam @(R '["var" := Zero Int, "lam" := One])

appId :: forall z. (All Functor z, LamCR ~<~ z) => Mu (V1 z)
appId = mkApp (idLam @z) (var @z)


idstr :: String
idstr = showLamR idLam

varstr :: String
varstr = (Rec showVar) ~$~ (mkVar 42)

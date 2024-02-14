{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fprint-explicit-kinds -fplugin RoHsPlugin #-}
-- {-# OPTIONS -fforce-recomp -ddump-tc-trace -dcore-lint -fplugin RoHsPlugin #-}
-- {-# OPTIONS -fforce-recomp -dcore-lint -fplugin RoHsPlugin #-}

-- For now do not run the plugin on the primitives file,
-- becuase they are well, primitives
module RoHsPrimitives where

import Common

import Data.Proxy

-- All the named declarations are the
-- primitives of the Row language.
-- They primitives are defined as undefined
-- They will be replaced by the actual
-- implementation in the core pass using
-- the core plugin


-- There are 2 ways of doing this, i'm not sure which path to take:
--   1. Should we replace the bindings and emit a core file which can be linked to the
--      use site correctly? or,
--   2. Should we replace each occurance in the use site should be replaced by the right semantic core


-- For now i'm chosing option 2 as I suspect their may be information that i can leverage
-- to manipulate the dictonaries.


-- Well this is potentially annoying...
{-# NoINLINE labR0 #-}
labR0 :: forall s {t}. t -> R0 (R '[s := t])
labR0 = undefined

unlabR0 :: R0 (R '[s := t]) -> t
unlabR0 = undefined

prj0 :: forall z y. z ~<~ y => R0 y -> R0 z
prj0 = undefined

-- cat0 :: R0 y -> R0 z -> R0 (y ~+~ z)
cat0 :: Plus y z x => R0 y -> R0 z -> R0 x
cat0 _ _ = undefined

-- Sigh...

labR1 :: forall s {f} {t}. f t -> R1 (R '[s := f]) t
labR1 = undefined

unlabR1 :: R1 (R '[s := f]) t -> f t
unlabR1 = undefined

prj1 :: z ~<~ y => R1 y t -> R1 z t
prj1 = undefined

-- cat1 :: R1 y t -> R1 z t -> R1 (y ~+~ z) t
cat1 :: Plus y z x => R1 y t -> R1 z t -> R1 x t
cat1 _ _ = undefined

sel0 :: forall s {t} {z}. R '[s := t] ~<~ z => R0 z -> t
-- Perhaps we can use some of these at least...
sel0 r = unlabR0 @s (prj0 r)

labV0 :: forall s {t}. t -> V0 (R '[s := t])
labV0 = undefined

labV1 :: forall s {f} {t}. f t -> V1 (R '[s := f]) t
labV1 = undefined

unlabV0 :: V0 (R '[s := t]) -> t
unlabV0 = undefined

unlabV1 :: V1 (R '[s := f]) t -> f t
unlabV1 = undefined

inj0 :: y ~<~ z => V0 y -> V0 z
inj0 = undefined

inj1 :: y ~<~ z => V1 y t -> V1 z t
inj1 = undefined

-- brn0 :: (V0 x -> t) -> (V0 y -> t) -> V0 (x ~+~ y) -> t
brn0 :: Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
brn0 = undefined

-- brn1 :: (V1 x t -> u) -> (V1 y t -> u) -> V1 (x ~+~ y) t -> u
brn1 :: Plus x y z => (V1 x t -> u) -> (V1 y t -> u) -> V1 z t -> u
brn1 = undefined

-- and we can define

con0 :: forall s {t} {z}. R '[s := t] ~<~ z => t -> V0 z
con0 x = inj0 (labV0 @s x)

case0 :: forall s {t} {u}. (t -> u) -> V0 (R '[s := t]) -> u
case0 f = f . unlabV0   -- I am surprised GHC can figure this out... and somewhat concerned about what it's actually figured out

con1 :: forall s {f} {t} {z}. R '[s := f] ~<~ z => f t -> V1 z t
con1 x = inj1 (labV1 @s x)

case1 :: forall s {f} {t} {u}. (f t -> u) -> V1 (R '[s := f]) t -> u
case1 f = f . unlabV1


ana0 :: forall z t.
        (forall s y {u}. (Plus (R '[s := u]) y z) => u -> t) ->
        V0 z -> t
ana0 _ = undefined

anaE0 :: forall phi {z} {t}.
         (forall s y {u}. (Plus (R '[s := u]) y z) => phi u -> t) ->
         V0 (Each phi z) -> t
anaE0 _ = undefined

anaA0 :: forall c {z} {t}.
         All c z =>
         (forall s y {u}. (Plus (R '[s := u]) y z, c u) =>
                           Proxy s -> u -> t)  -- Assuming I'll need proxies for same reason as below
      -> V0 z -> t
anaA0 _ = undefined

anaA1 :: forall c {z} {t} {u}.
         All c z =>
         (forall s y {f}. (Plus (R '[s := f]) y z, c f)
                        => Proxy s -> f u -> t) -- Proxy!? see `fmapV` below
      -> V1 z u -> t
anaA1 _ = undefined

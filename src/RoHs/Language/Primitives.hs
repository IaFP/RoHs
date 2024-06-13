{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# LANGUAGE TypeFamilyDependencies #-}

-- For now do not run the plugin on the primitives file,
-- becuase they are well, primitives
module RoHs.Language.Primitives where

import RoHs.Language.Types

import Data.Proxy

-- All the named declarations are the
-- primitives of the Row language.
-- They primitives are defined as undefined
-- They will be replaced by the actual
-- implementation in the core pass using
-- the core plugin.


-- The client should not import this file.
-- They should depend on the `RoHs.Language.Lib` module


-- Well this is potentially annoying...
{-# INLINE labR0_I #-}
labR0_I :: forall s {t}. t -> R0 (R '[s := t])
labR0_I = undefined

{-# INLINE unlabR0_I #-}
unlabR0_I :: forall s {t}. R0 (R '[s := t]) -> t
unlabR0_I = undefined

{-# INLINE prj0_I #-}
prj0_I :: forall y z. y ~<~ z => R0 z -> R0 y
prj0_I = undefined

{-# INLINE cat0_I #-}
-- cat0 :: R0 y -> R0 z -> R0 (y ~+~ z)
cat0_I :: forall {x} {y} {z}. Plus x y z => R0 x -> R0 y -> R0 z
cat0_I = undefined


syn0_I :: forall c {z} {u}.
         All c z =>
         (forall {s} {y} {u}. (Plus (R '[s := u]) y z, R '[s := u] ~<~ z, y ~<~ z, c u)
                            =>  Proxy s -> u)
      -> R0 z
syn0_I = undefined  -- We don't know how to make this work yet.
                   -- JGM says The types don't work out in Haskell. Need to check where exactly it fails

{-# INLINE labV0_I #-}
labV0_I :: forall s {t}. t -> V0 (R '[s := t])
labV0_I = undefined

{-# INLINE brn0_I #-}
-- brn0 :: (V0 x -> t) -> (V0 y -> t) -> V0 (x ~+~ y) -> t
brn0_I :: Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
brn0_I = undefined

{-# INLINE unlabV0_I #-}
unlabV0_I :: forall s {t}. V0 (R '[s := t]) -> t
unlabV0_I = undefined

{-# INLINE inj0_I #-}
inj0_I :: forall y z. y ~<~ z => V0 y -> V0 z
inj0_I = undefined

{-# INLINE anaA0_I #-}
anaA0_I :: forall {c} {z} {t}.
           All c z
        => (forall {s} {y} {u}. (Plus (R '[s := u]) y z, R '[s := u] ~<~ z, y ~<~ z, c u)
                            =>  Proxy s -> u -> t)  -- Assuming I'll need proxies for same reason as below
        -> V0 z -> t
anaA0_I _ = undefined


-- {-# INLINE ana0_I #-}
-- ana0_I :: forall z t.
--         (forall s y {u}. (Plus (R '[s := u]) y z) => u -> t) ->
--         V0 z -> t
-- ana0_I _ = undefined

-- {-# INLINE anaE0_I #-}
-- anaE0_I :: forall phi {z} {t}.
--          (forall s y {u}. (Plus (R '[s := u]) y z) => phi u -> t) ->
--          V0 (Each phi z) -> t
-- anaE0_I _ = undefined


-- Sigh...
labR1_I :: forall s {f} {t}. f t -> R1 (R '[s := f]) t
labR1_I = undefined

unlabR1_I :: R1 (R '[s := f]) t -> f t
unlabR1_I = undefined

prj1_I :: z ~<~ y => R1 y t -> R1 z t
prj1_I = undefined

-- cat1 :: R1 y t -> R1 z t -> R1 (y ~+~ z) t
cat1_I :: Plus y z x => R1 y t -> R1 z t -> R1 x t
cat1_I _ _ = undefined

labV1_I :: forall s {f} {t}. f t -> V1 (R '[s := f]) t
labV1_I = undefined

unlabV1_I :: V1 (R '[s := f]) t -> f t
unlabV1_I = undefined


inj1_I :: y ~<~ z => V1 y t -> V1 z t
inj1_I = undefined

-- brn1 :: (V1 x t -> u) -> (V1 y t -> u) -> V1 (x ~+~ y) t -> u
brn1_I :: Plus x y z => (V1 x t -> u) -> (V1 y t -> u) -> V1 z t -> u
brn1_I = undefined

anaA1_I :: forall c {z} {t} {u}.
         All c z =>
         (forall s y {f}. (Plus (R '[s := f]) y z, R '[s := f] ~<~ z, y ~<~ z, c f)
                        => Proxy s -> f u -> t) -- Proxy!? see `fmapV` below
      -> V1 z u -> t
anaA1_I _ = undefined

{-# LANGUAGE AllowAmbiguousTypes, ConstraintKinds, DataKinds, QuantifiedConstraints, TypeApplications, TypeFamilyDependencies #-}
{-# LANGUAGE FunctionalDependencies #-}  -- because TypeFamilyDependencies doesn't really do what I'd like yet...
{-# LANGUAGE ImpredicativeTypes #-}  -- but was this applied before?  Otherwise, I'm not sure why my definitions ever typed...
{-# OPTIONS -fplugin RoHsPlugin #-}

module Surface where

import Data.Proxy
import GHC.Base

data Row :: Type -> Type where
  R :: [Assoc a] -> Row a

data Assoc :: Type -> Type where
  (:=) :: Symbol -> a -> Assoc a

class (~<~) (a :: Row t) (b :: Row t)
  -- probably shouldn't have user instances of this class... :P

-- This is what I really want:
type family (~+~) (a :: Row t) (b :: Row t) = (c :: Row t)
    -- | c a -> b, c b -> a
    where

-- But that's more than just an injective type family.  We can make more
-- progress using the following definition:

class Plus (x :: Row t) (y :: Row t) (z :: Row t) | x y -> z, x z -> y, y z -> x

-- But if this is going to *actually* work, we're going to need to step in with
-- some defaulting to actually fix `z`s.

-- Records ahoy

data R0 :: Row Type -> Type
data R1 :: Row (a -> Type) -> a -> Type

-- See if we can do anything

foo :: R0 (R '["x" := Int, "y" := Bool])
foo = undefined

-- Well this is potentially annoying...

labR0 :: forall s {t}. t -> R0 (R '[s := t])
labR0 = undefined

unlabR0 :: R0 (R '[s := t]) -> t
unlabR0 = undefined

prj0 :: forall z y. z ~<~ y => R0 y -> R0 z
prj0 = undefined

-- cat0 :: R0 y -> R0 z -> R0 (y ~+~ z)
cat0 :: Plus y z x => R0 y -> R0 z -> R0 x
cat0 r s = undefined

-- Sigh...

labR1 :: forall s {f} {t}. f t -> R1 (R '[s := f]) t
labR1 = undefined

unlabR1 :: R1 (R '[s := f]) t -> f t
unlabR1 = undefined

prj1 :: z ~<~ y => R1 y t -> R1 z t
prj1 = undefined

-- cat1 :: R1 y t -> R1 z t -> R1 (y ~+~ z) t
cat1 :: Plus y z x => R1 y t -> R1 z t -> R1 x t
cat1 r s = undefined

sel0 :: forall s {t} {z}. R '[s := t] ~<~ z => R0 z -> t
-- Perhaps we can use some of these at least...

sel0 r = unlabR0 @s (prj0 r)

-- Let's repeat the tedium for variants...

data V0 :: Row Type -> Type
data V1 :: Row (a -> Type) -> a -> Type

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

--

bar :: -- (R '["true" := Int] ~+~ R '["false" := Bool] ~ R '["true" := Int, "false" := Bool]) =>
       -- This constraint should be solvable
       Plus (R '["true" := Int]) (R '["false" := Bool]) (R '["true" := Int, "false" := Bool]) =>
       V0 (R '["true" := Int, "false" := Bool]) -> Int
bar = case0 @"true" id `brn0` case0 @"false" (\b -> if b then 0 else 1)

bar1 :: -- (R '["true" := Int] ~+~ R '["false" := Bool] ~ R '["false" := Bool, "true" := Int]) =>
       -- This constraint should be solvable
       Plus (R '["true" := Int]) (R '["false" := Bool]) (R '["false" := Bool, "true" := Int]) =>
       V0 (R '["false" := Bool, "true" := Int]) -> Int
bar1 = case0 @"true" id `brn0` case0 @"false" (\b -> if b then 0 else 1)

-- This is a *less* compelling argument against than I thought, but still
-- concerned about the type argument to inj0.
-- bar2 :: forall z y.
--         -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
--         (R '["x" := Bool] ~+~ z ~ y,
--          -- These three constraint should all be solvable, *given the definition above*
--          R '["x" := Bool] ~<~ R '["x" := Bool],
--          R '["x" := Bool] ~<~ y,
--          z ~<~ y) =>
--         V0 (R '["x" := Int] ~+~ z) -> V0 y
-- bar2 = case0 @"x" (\(i :: Int) -> con0 @"x" (i == 0)) `brn0`
--        inj0 @z

bar2 :: forall z y1 y2.
        -- Bit of a run-around here because GHC doesn't like `z ~<~ x ~+~ y` constraints
        (Plus (R '["x" := Integer]) z y1,    -- `Integer` so defaulting doesn't get in the way
         Plus (R '["x" := Bool]) z y2,
         -- These three constraint should all be solvable, *given the definitions above*
         R '["x" := Bool] ~<~ R '["x" := Bool],
         R '["x" := Bool] ~<~ y2,
         z ~<~ y2) =>
        V0 y1 -> V0 y2
bar2 = case0 @"x" (\i -> con0 @"x" (i == 0)) `brn0` inj0

-- Okay, let's try Rω again.  Same fundamental problem: we need to replace the use of type-level λs.

type family Each :: (a -> b) -> Row a -> Row b where
  -- I have a feeling that this is not going to work out for me... see the
  -- `constants` example below.  The crux of the issue is that I want to
  -- "axiomatize" `Each f z` with statements like `y ~<~ z => Each f y ~<~ Each
  -- f z`... but GHC is (reasonably...) upset at constraints on type synonyms.
  --
  -- Perhaps I could solve this problem by switching `Each` to a constraint-with
  -- -fundep, but that seems hard to use...

type family All :: (a -> Constraint) -> Row a -> Constraint where

ana0 :: forall z t.
        (forall s y {u}. (Plus (R '[s := u]) y z,
                          R '[s := u] ~<~ z,
                          y ~<~ z) =>
                          u -> t) ->
        V0 z -> t
ana0 _ = undefined

anaE0 :: forall phi {z} {t}.
         (forall s y {u}. (Plus (R '[s := u]) y z,
                           R '[s := u] ~<~ z,
                           y ~<~ z) =>
                           phi u -> t) ->
         V0 (Each phi z) -> t
anaE0 _ = undefined

anaA0 :: forall c {z} {t}.
         All c z =>
         (forall s y {u}. (Plus (R '[s := u]) y z,
                           R '[s := u] ~<~ z,
                           y ~<~ z,
                           c u) =>
                           Proxy s -> u -> t) ->  -- Assuming I'll need proxies for same reason as below
         V0 z -> t
anaA0 _ = undefined

anaA1 :: forall c {z} {t} {u}.
         All c z =>
         (forall s y {f}. (Plus (R '[s := f]) y z,
                           R '[s := f] ~<~ z,
                           y ~<~ z,
                           c f) =>
                           Proxy s -> f u -> t) ->   -- Proxy!? see `fmapV` below
         V1 z u -> t
anaA1 _ = undefined

--

boo :: forall z. All Show z => V0 z -> String
boo = anaA0 @Show (const show)

boo1 :: forall z. All Show z => V0 z -> String
boo1 = anaA0 @Show f where
  f _ x = show x

-- But apparently adding the type signature will make `f` no longer have the
-- right type.  I am concerned that I am missing something fundamental here...

--   f :: forall s y u. (Plus (R '[s := u]) y z,
--                       R '[s := u] ~<~ z,
--                       y ~<~ z,
--                       Show u) =>
--                       u -> String
--   f = show

-- constants :: forall t z.
--              (forall s f u z. R '[s := u] ~<~ z => R '[s := f u] ~<~ Each f z) =>
--              V0 z -> V0 (Each ((->) t) z)
-- constants = ana0 f where
--   f x = con0 (\y -> x)

eqV :: forall z. All Eq z => V0 z -> V0 z -> Bool
eqV v w = anaA0 @Eq g w where

  g :: forall s y t. (Plus (R '[s := t]) y z, 
                      R '[s := t] ~<~ z,
                      y ~<~ z,
                      Eq t) =>
                     Proxy s -> t -> Bool
  g _ x = (case0 @s (\y -> x == y) `brn0` const False) v


fmapV :: forall a b z. All Functor z => (a -> b) -> V1 z a -> V1 z b
fmapV f = anaA1 @Functor g where

  -- Without the `Proxy s` argument, `g` types fine but doesn't play well as n
  -- argument to `anaA1`.... !!??

  -- Can't get away without the type annotation here... even if I try to pattern
  -- match on the proxy.  Let's pretend I understand anything.
  g :: forall s y f. (Plus (R '[s := f]) y z,
                      R '[s := f] ~<~ z,
                      y ~<~ z,
                      Functor f) =>
                     Proxy s -> f a -> V1 z b
  g _ x = con1 @s (fmap f x)

-- This should be enough to do something dumb.  Let's try....

data ZeroF k a = C0 k
  deriving Functor
data OneF a    = C1 a
  deriving Functor
data TwoF a    = C2 a a
  deriving Functor

type BigR = R '["Const" := ZeroF Int, "Add" := TwoF, "Double" := OneF]

type SmallR = R '["Const" := ZeroF Int, "Add" := TwoF]

newtype Mu f = Wrap {unwrap :: f (Mu f)}

-- Here's a very explicit type...
desugar :: (-- These should all be solvable
            All Functor SmallR,
            Plus (R '["Double" := OneF]) SmallR BigR,
            R '["Add" := TwoF] ~<~ SmallR,
            SmallR ~<~ SmallR) =>
           Mu (V1 BigR) -> Mu (V1 SmallR)
desugar (Wrap e) = Wrap ((double `brn1` (fmapV desugar . inj1)) e) where
  double = case1 @"Double" (\(C1 x) -> con1 @"Add" (C2 (desugar x) (desugar x)))

-- Of course, I don't want to fix the entire row.
desugar' :: forall bigr smallr.
           (-- These are essentially part of the type
            Plus (R '["Double" := OneF]) smallr bigr,
            All Functor smallr,
            R '["Add" := TwoF] ~<~ smallr,
            -- This should be solvable
            smallr ~<~ smallr) =>
           Mu (V1 bigr) -> Mu (V1 smallr)
desugar' (Wrap e) = Wrap ((double `brn1` (fmapV desugar' . inj1)) e) where
  double = case1 @"Double" (\(C1 x) -> con1 @"Add" (C2 (desugar' x) (desugar' x)))

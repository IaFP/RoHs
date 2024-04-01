I've been trying to figure out how to express *extensible* recursive functions over *extensible* data types.

# The motivation

We don't have to look far to find a motivating example. We currently have to write desugaring something like:

```haskell
desugar :: (R '["Add" := Two] ~<~ y, All Functor (R '["Double" := One] ~+~ y)) =>
           Mu (V1 (R '["Double" := One] ~+~ y)) -> Mu (V1 y)

desugar = foldV (desD `brn1` (Mk . inj1)) where

  -- desD :: V1 (R '["Double" := One]) (Mu (V1 z)) -> Mu (V1 z)
  desD = case1 @"Double" (\(O e) -> mkA e e)
```

Where, crucially, `foldV` is handling the recursion and the branching operator is only combining (non-recursive...) cases *inside* the fixed point type constructor.

How might we want to write this? My fantasy is something like:

```haskell
desugar = (desD `brnr` idx) where
  desD (X'Double e) = X'Add (desD e) (desD e)
```

In particular, rather than having to wrap the recursion at the top level, we should be able to combine individual recursive functions to get a larger recursive function. To be clear, the complication here is what happens in recursive calls: the recursive calls to `desD` may need to be handled by the `idx` in the top level `brnr`. 

Wait a minute. Why do we need an *extensible* identity function `idx`? 

# The problem

Let's put the base cases aside for a moment—I'd started focusing there, and I think that was a mistake. The type of `brnr` above needs to be:

```haskell
brnr :: (Mu (Σ x) -> t) -> (Mu (Σ y) -> t) -> Mu (Σ (x ~+~ y)) -> t
```

That is: we take an eliminator for recursive `x` variants and an eliminator for recursive `y` variants, and build an eliminator for recursive `x ~+~ y` variants. This is what we would "expect" from the  development of variant eliminators in Rose.

Now, let's think about how this has to work, in terms of the example above. Suppose we have

```haskell
desugar (X'Double (X'Add (X'Double (X'Const 1)) (X'Double (X'Const 2))))
```

that is:

```haskell
(desD `brnr` idx) (X'Double (X'Add (X'Double (X'Const 1)) (X'Double (X'Const 2))))
```

"Clearly" the `desD` case should apply. But note the treatment of recursion: just because we use `desD` at the top level does not mean we can use `desD` all the way down. Instead, we should get something like:

```haskell
X'Add ((desD `brnr` idx) (X'Add (X'Double (X'Const 1)) (X'Double (X'Const 2))))
      ((desD `brnr` idx) (X'Add (X'Double (X'Const 1)) (X'Double (X'Const 2))))
```

So far so possible: presumably in translating `desD`, we take note of the recursive calls so that we can extend them later. (This part was the focus of my previous excitement.) But now let's consider the next step. `X'Add` isn't handled by `desD`, so should be handled by the "default" case. But we still need to make recursive calls within that case! We want:

```haskell
X'Add (X'Add ((desD `brnr` idx) (X'Double (X'Const 1))) 
             ((desD `brnr` idx) (X'Double (X'Const 2)))))
      (X'Add ((desD `brnr` idx) (X'Double (X'Const 1))) 
             ((desD `brnr` idx) (X'Double (X'Const 2)))))
```

But we certainly wouldn't get this behavior from a definition of `idx` that read:

```haskell
idx x = x
```

There's no recursion to extend!

## A side puzzle

In Rω (well, extended with pattern matching and fixed points, but that part is boring), I know how to write the extensible version of `id`:

$$
\begin{aligned}
\mathrm{idx} &: \forall z. \mathrm M (\Sigma z) \to \mathrm M (\Sigma z) \\
\mathrm{idx} \, (\mathrm {In} \, e) &= \mathrm{In} \, (\mathrm{ana} \, (\lambda \, l \, x. \, \mathrm{con} \, l \, (\mathrm{idx} \, x)) \, e)
\end{aligned}
$$
However, it is not so immediately obvious how to write this in RoHs. In particular, in Haskell, the only version of `ana` that has made a lot of sense so far is the version that abstracts over a type class constraint for each constructor. Here we really don't need such a thing...

# The tedious solution

Okay, fine, here's the beginnings of a Haskell solution, in terms of an explicit fixed point combinator.

```haskell
data t ~> u where
  Recursive :: (forall y. (z ~<~ y) => z (Mu (V1 y)) -> (Mu (V1 y) -> u) -> u) ->
               Mu (V1 z) ~> u
```

The `z ~<~ y` constraint may or may not be necessary. At the very least, it allows us to write unproductive code:

```haskell
Recursive (\x f -> f (In (inj1 x)))
```

but perhaps it has real uses as well.

```haskell
brnr :: (Mu (V1 x) ~> t) -> (Mu (V1 y) ~> t) -> (Mu (V1 (x ~+~ y)) ~> t)
Recursive f `brnr` Recursive g = Recursive (f `brn1` g)
```

When I put this together in my sandbox (based on my type family encoding), establishing `w ~<~ x` and `w ~<~ y` from `w ~<~ (x ~+~ y)` is not so easy, but I think the plugin should not struggle here.

```haskell
(~$~) :: (Mu (V1 x) ~> t) -> Mu (V1 x) -> t
Recursive f ~$~ Fix x = f x (Recursive f ~$~)
```

Having to use `~$~` explicitly is not great.

# Some research questions

**Does the explicit version work?** 

This at least starts by implementing the above with the plugin and seeing what types.

**Can we desugar to the explicit version?**

Having to write uses of `Recursive` directly sucks. How would this work as a target of desugaring?

One problem is identifying *where* the desugaring should apply. Any pattern match on an extensible constructor? If so, we need a simultaneous solution to the problem of spreading `~$~`s.

**Are there useful extensible functions outside the domain of this encoding?**

In particular, what if you need pattern matching on multiple levels of extensible data.

Alex proposes something like the following:

```haskell
data X'Nat = X'Zero | X'Succ X'Nat

half :: X'Nat -> X'Nat
half X'Zero = X'Zero
half (X'Succ X'Zero) = X'Succ X'Zero
half (X'Succ (X'Succ n)) = X'Succ (half n)
```

extended by a case for `X'Pred`. But new challenges emerge... it's "clearly" not enough to combine the above with

```
halfp :: X'Pred -> X'Pred
halfp (X'Pred (X'Pred n)) = X'Pred (halfp n)
```

as that doesn't leave us with cases for `X'Pred (X'Succ n)` and so forth.


#research #idea #rows 
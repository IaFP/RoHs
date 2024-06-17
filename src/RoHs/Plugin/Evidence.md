The Evidence Story
=================


- The type class instances stores some evidence about the rows in question
  We have two important type classes in our system:

  2. `class x ~<~ y`
  2. `Plus x y z`


- The "is subset of" predicate, represented by the typeclass `x ~<~ y`:

  The evidence for this type class an (instance) is a function that converts a row `y` into `x`.
  For example, the evidence for the type class:

		(R '["y" := Bool, "z" := Int]) ~<~ (R '["x" := Int, "y" := Bool, "z" := Int, "w" := String])

	is the function that can transform the row

	    R '["x" := Int, "y" := Bool, "z" := Int, "w" := String]`


	into the row

        R '["y" := Bool, "z" := Int].

	All the rows are represented as an appropriate System FC term, as we are implementing the system as a GHC plugin.

	The actual representation of `x ~<~ y` is a tuple `(n, [k_i])`
	where `n` is the size of `x`, and each `k_i` maps `k`th element of `y` into `x`



- The row concatenation predicate, represented by the typeclass `Plus x y z`:

  The evidence for this typeclass is a function, which when given `z` can map the individual labels into
  the exact position of the source rows. More concretely, the evidence for the typeclass:

		Plus (R '["y" := Bool, "z" := Int])
		     (R '["x" := Int, "w" := String])
			 (R '["x" := Int, "y" := Bool, "w" := String, "z" := Int, ])

  is a function which tells us where does the label `"x"` comes from and where does the label `"z"` come from.


Before we can actually delve into the representation of the functions, we first need to fix the representation of the rows.
This is done by the core plugin in `RoHs.Plugin.Core`. We are with in the type structure of GHC.
The type `(R '["x" := Bool, y := Int])` has several components:

 - `R` is a closed type family with no equations. Thus, there can be no ground types (except $\bot$) which it in can inhabit.
   The plugin can, fortunately, do this job of populating the type and also, checking that the term does belong to the type.
   It is a higher kinded type so that it can store the information of the labels and their types.

- This brings us to the second component: `'[ x := t, y := u ]` a collection of labels and its associated type.
  Although it is represented using a (promoted) list, we want to be able to simulate order independence.
  i.e. `'[ x := t, y := u]` and `[y := u , x := t]` are just $\alpha$ equivalent types




### Manipulating (~<~) dictonaries

The `(r1 ~<~ r2)` predicate build the injection function. So it tells us which index from `y` is mapped to which index in `x`
Thus for:

	r2 = [ x := t, y := t', w := u, z := u']
	r1 = [ x := t, z := u' ]


The evidence will look like

	r2 ~<~ r1 = (2, (1, 4))


The first compoment `2` tells how big `r1` is and then gives a tuple of indices (of the length of the first tuple) which can build `r2`
by given `r1`


At core level, the (simplified) term will look like

	$d_r2~<~r1 :: r2 ~<~ r1
	$d_r2~<~r1 = (2, (1, 4))


This dictonary is built by the type checker plugin, if indeed it has all the necessary information available.
<!-- The core however, may not have access to the actual row types during type checking, so we need to build function, which when -->
<!-- instantiated with the right input rows (and types), builds the appropriate tuple. -->

Now the `prj0` will take in `$d_r2~<~r1` as its first input, and the `r1` as its second input, and return `r2` as its output.

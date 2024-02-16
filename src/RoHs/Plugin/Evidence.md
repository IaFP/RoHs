The Evidence Story
=================


- The type class instances stores some evidence about the rows in question
  We have two important type classes in our system:

  2. `class x ~<~ y`
  2. `Plus x y z`


- The "is subset of" predicate, represented by the typelcass `x ~<~ y`:

  The evidence for this type class an (instance) is a function that converts a row `y` into `x`.
  For example, the evidence for the type class:

		(R '["y" := Bool, "z" := Int]) ~<~ (R '["x" := Int, "y" := Bool, "z" := Int, "w" := String])

	is the function that can transform the row

	    R '["x" := Int, "y" := Bool, "z" := Int, "w" := String]`


	into the row

        R '["y" := Bool, "z" := Int].

	All the rows are represented as an appropriate System FC term, as we are implmenting the system as a GHC plugin.


- The row concatination predicate, represented by the typeclass `Plus x y z`:

  The evidence for this typeclass is a function, which when given `z` can map the individual labels into
  the exact position of the source rows. More concretely, the evidence for the typeclass:

		Plus (R '["y" := Bool, "z" := Int])
		     (R '["x" := Int, "w" := String])
			 (R '["x" := Int, "y" := Bool, "w" := String, "z" := Int, ])

  is a function which tells us where does the label `"x"` comes from and where does the label `"z"` come from.

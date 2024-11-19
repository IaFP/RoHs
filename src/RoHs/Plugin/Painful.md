Manually expanding meta programs as ghci is too opaque

The testcase that fails:

```Haskell
(Rec showVar) ~$~ (mkVar 0)
```


```Haskell

  (Rec showVar) ~$~ (mkVar 0)

= { def (~$~), mkVar }

	showVar (con1 @"var" (Z 0)) (\ x -> (Rec showVar) ~$~ x) -- fails with loaded `showVar`, redefining showVar works as expected

= { def showVar, ignores the second argument }

	(case1 @"var" (\Z i -> show i)) (con1 @"var" (Z 0)) -- works okay

= { def case1 }

    (\Z i -> show i)) (unlabV1 @"var" (con1 @"var" (Z 0))) -- works okay
```


```Haskell
	showLamR (idLam @(R '["var" := Zero Int, "lam" := One]))
= { def showLamR }
	((Rec showVar) `brnr` (Rec showLam)) ~$~ (idLam @(R '["var" := Zero Int, "lam" := One]))
	
= { }
	((Rec showVar) `brnr` (Rec showLam)) ~$~ (idLam @(R '["var" := Zero Int, "lam" := One]))


```


```Haskell
idLam = mkLam (mkVar @VarR 0)
      = mkLam z $dAllF 

```

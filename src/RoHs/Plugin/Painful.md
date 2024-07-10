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


```
BCO_toplevel_E0 :: IO [()]
[LclId] =
    \u []
        let {
          it_swbl :: String
          [LclId] =
              \u []
                  let {
                    sat_swbq :: V1 (R '["var" ':= Zero Int]) Any
                    [LclId] =
                        \u []
                            let {
                              sat_swbo :: Int
                              [LclId] =
                                  I#! [0#]; } in
                            let {
                              sat_swbp :: Zero Int Any
                              [LclId] =
                                  Z! [sat_swbo]; } in
                            let {
                              sat_swbm :: Int
                              [LclId] =
                                  I#! [-1#]; } in
                            let {
                              sat_swbn :: R '["var" ':= Zero Int] ~<~ R '["var" ':= Zero Int]
                              [LclId] =
                                  (,)! [sat_swbm ()];
                            } in  con1 sat_swbn sat_swbp;
                  } in  showVar sat_swbq id; } in
        let {
          sat_swbu :: IO [()]
          [LclId] =
              \u []
                  let {
                    sat_swbt :: [()]
                    [LclId] =
                        :! [it_swbl []];
                  } in  returnIO sat_swbt; } in
        let {
          sat_swbs :: IO ()
          [LclId] =
              \u []
                  case $fShowList $fShowChar of sat_swbr {
                  __DEFAULT -> print sat_swbr it_swbl;
                  };
        } in  thenIO sat_swbs sat_swbu;


"0"
```

module RoHs.Plugin.Semantics where

import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Core.Type
import GHC.Core.Multiplicity
import GHC.Core.Utils

import GHC.Plugins

import RoHs.Plugin.CoreUtils

type PrimMap = [(FastString, (ModGuts, Type) -> CoreM CoreExpr)]

fstC :: (a, b) -> a
fstC = Prelude.fst
sndC :: (a, b) -> b
sndC = Prelude.snd

labR0Core, unlabR0Core, prj0Core, cat0Core, labV0Core, unlabV0Core, inj0Core, ana0Core, brn0Core :: (ModGuts, Type) -> CoreM CoreExpr

primMap :: PrimMap
primMap = [ (fsLit "labR0" ,   labR0Core)    -- :: forall s {t}. t -> R0 (R '[s := t])
          , (fsLit "unlabR0",  unlabR0Core)  -- :: forall s t. R0 (R '[s := t]) -> t
          , (fsLit "prj0",     prj0Core)     -- :: forall z y. z ~<~ y => R0 y -> R0 z
          , (fsLit "cat0",     cat0Core)     -- :: forall y z x. Plus y z x => R0 y -> R0 z -> R0 x


          , (fsLit "labV0",    labV0Core)    -- :: forall s {t}. t -> V0 (R '[s := t])
          , (fsLit "brn0",     brn0Core)     -- :: forall x y z t. Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
          , (fsLit "unlabV0",  unlabV0Core)  -- unlabV0 :: forall s {t}. V0 (R '[s := t]) -> t
          , (fsLit "inj0",     inj0Core)
          , (fsLit "ana0",     ana0Core)
          , (fsLit "anaE0",    mkIdCore)
          , (fsLit "anaA0",    mkIdCore)
          ]

-- unlabR0Core  = mkIdCore
-- unlabV0Core = mkIdCore
-- labV0Core = mkIdCore
-- inj0Core = mkIdCore
ana0Core = mkIdCore
brn0Core = mkIdCore
-- prj0Core = mkIdCore

mkIdCore :: (ModGuts, Type) -> CoreM CoreExpr
mkIdCore (_, oType) = return $ Cast (mkCoreLams [a, x] (Var x)) (mkCastCo idTy oType)
  where
    xn :: Name
    xn = mkName 0 "x_{gen}"


    an :: Name
    an = mkName 1 "a_{gen}"

    a :: TyVar
    a = mkTyVar an liftedTypeKind

    -- x :: a
    x :: Id
    x = mkLocalId xn manyDataConTy (mkTyVarTy a)

    -- \forall a. a -> a
    idTy :: Type
    idTy = mkForAllTy (mkForAllTyBinder Inferred a) $ mkVisFunTy manyDataConTy (mkTyVarTy a) (mkTyVarTy a)

-- :: forall x y z t. Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
-- brn0Core (mgs, oType)
--   | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [x, y, z, t]
--   , (tys, resultTy) <- splitFunTys ty          -- ty = t -> V0 (R '[s := t])
--   = do { let brn0Core :: CoreExpr
--              brn0Core = mkCoreLams (tyVars ++ [d, f, g, z]) (mkCoreTup []) (mkCastCo bodyTy resultTy)

--              bodyTy =

--              debug_msg = text "brn0Core" <+> vcat [ text "Type" <+> ppr oType
--                                                    , text "TyBnds"   <+> ppr tyVars
--                                                    , text "argTys"    <+> ppr tys
--                                                    , text "resultTy" <+> ppr resultTy
--                                                    , ppr brn0Core ]
--        ; debugTraceMsg debug_msg
--        ; return brn0Core

--        }


-- forall s {t}. t -> V0 (R '[s := t])
labV0Core (_, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [s, t]
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty -- ty = t -> V0 (R '[s := t])
  = do {
         let labV0Fun :: CoreExpr
             labV0Fun = mkCoreLams [tyVars !! 0, tyVars !! 1, t] (Cast body co)

             tn = mkName 1 "t"

             t = mkLocalId tn manyDataConTy argTy

             l = mkCoreInt 0

             co = mkCastCo (mkTupleTy Boxed [intTy, argTy]) resultTy

             body = mkCoreTup [l, (Var t)]

             debug_msg = text "labV0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr labV0Fun ]
       ; debugTraceMsg debug_msg
       ; return labV0Fun
       }
  | otherwise = pprPanic "shouldn't happen labV0Core" (ppr oType)
-- unlabV0 :: forall s {t}. V0 (R '[s := t]) -> t
unlabV0Core (mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                 -- tys [s, t]
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty -- ty = V0 (R '[s := t]) -> t
  = do { sndId <- findId mgs "sndC"

       ; let unlabV0Fun :: CoreExpr
             unlabV0Fun = mkCoreLams (tyVars ++ [vId]) (Cast body co)

             vn = mkName 2 "v0"
             vId = mkLocalId vn manyDataConTy argTy

             co = mkCastCo anyType resultTy

             v = Cast (Var vId) (mkCastCo argTy (mkTupleTy Boxed [intTy, anyType]))

             body = mkCoreApps (Var sndId) [Type intTy, Type anyType, v]

             debug_msg = text "unlabV0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr unlabV0Fun ]
       ; debugTraceMsg debug_msg
       ; return unlabV0Fun

       }
 | otherwise = pprPanic "shouldn't happen unlabV0Core" (ppr oType)

labR0Core  (_, oType) -- :: forall s {t}. t -> R0 (R '[s := t])
  | (tyVars, ty) <- splitForAllTyVars oType                 -- tys [s, t]
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty -- ty = t -> R0 (R '[s := t])
  = do { let lab0Fun :: CoreExpr
             lab0Fun = mkCoreLams (tyVars ++ [t]) (Cast body co)


             tn = mkName 1 "t"
             t =  mkLocalId tn manyDataConTy argTy


             bodyTy =  mkTupleTy Boxed [intTy, mkTupleTy Boxed [intTy], mkTupleTy Boxed [argTy]]
             body = mkCoreTup [ mkCoreInt 1, mkCoreInt 0   -- ( (1, (0))
                              , Var t                                              -- , t
                              ]                                                                -- )

             co = mkCastCo bodyTy resultTy
             debug_msg = text "labR0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr lab0Fun ]

       ; debugTraceMsg debug_msg
       ; return lab0Fun }
  | otherwise = pprPanic "shouldn't happen labR0Core" (ppr oType)

-- unlabR0Core ::  Type -> CoreM CoreExpr
unlabR0Core  (_, oType)   -- oType = forall s t. R0 (R '[s := t]) -> t
  | (tys, ty) <- splitForAllTyCoVars oType      -- tys      = [s, t]
  , (_vis, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty  -- ty = R0 (R '[s := t]) -> t
  = do { -- snd <- findId ("snd")
       ; let
             unlabR0Fun :: CoreExpr
             unlabR0Fun = mkCoreLams (tys ++ [r]) (Cast body co)

             rn = mkName 2 "r"
             r = mkLocalId rn manyDataConTy argTy

             body :: CoreExpr
             body = App (mkCoreTup []) (Cast (Var r) (co')) -- mkCoreInt 42

             co = mkCastCo anyType resultTy
             co' = mkCastCo argTy (mkTupleTy Boxed [intTy, mkListTy intTy, mkListTy anyType])
             debug_msg = text "unlabR0Core" <+> vcat [ text "Type:" <+> ppr oType
                                                     , text "tys:" <+> ppr tys
                                                     , text "argTy:" <+> ppr argTy
                                                     , text "resultTy:" <+> ppr resultTy
                                                     , ppr unlabR0Fun
                                                     ]

       ; debugTraceMsg debug_msg
       ; return unlabR0Fun
       }
  | otherwise = pprPanic "shouldn't happen unlabR0Core" (ppr oType)


-- prj0Core :: Type -> CoreM CoreExpr
prj0Core  (_, oType) -- forall z y. z ~<~ y => R0 y -> R0 z
  | (tys, ty) <- splitForAllTyCoVars oType      -- tys      = [y, z]
  , (_invsFun, (_:_:dTy:ty_body:_)) <- splitTyConApp ty  -- ty       = d => R0 y -> R0 z
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp (ty_body)  -- ty_body  = [R0 y -> R0 z]
  = do { let prjFun :: CoreExpr
             prjFun = mkCoreLams (tys ++ [d, ry]) (Cast body co)
    --  \ d@(3, (1,3,4)) (r) -> (r !! 1, r !! 3, r !! 4)
    -- The !! is justified as it was computed during type checking
    -- The types match because, again, it was justified during type checking
             dn, ryn :: Name
             dn = mkName 2 "$dz~<~y"
             ryn = mkName 3 "ry"

             -- z, y :: CoreBndr
             d, ry :: CoreBndr -- Can be TyVar or Id
             -- z = mkTyVar zn (idType $ tys !! 0)
             -- y = mkTyVar yn (idType $ tys !! 1)
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn  manyDataConTy argTy

             n = 1
             co = mkCastCo bodyTy resultTy

             n' = 2
             co' = mkCastCo dTy (mkTupleTy Boxed [intTy, mkTupleTy Boxed (replicate n' intTy)])

             bodyTy = mkTupleTy Boxed [intTy, mkTupleTy Boxed (replicate n intTy), mkTupleTy Boxed [intTy]]

             body :: CoreExpr
             -- Need a match here
             -- match d ry with
             body = mkSingleAltCase (Cast (Var d) co') d (DataAlt (tupleDataCon Boxed 2)) [] (mkCoreTup [])


             debug_msg = text "prj0Core" <+> vcat [ text "Type:" <+> ppr oType
                                                  , text "dTy:" <+> ppr dTy
                                                  , text "argTy:" <+> ppr argTy
                                                  , text "resultTy:" <+> ppr resultTy
                                                  , ppr prjFun ]

       ; debugTraceMsg debug_msg
       ; return prjFun }
  | otherwise = pprPanic "shouldn't happen prj0Core" (ppr oType)

-- cat0Core :: Type -> CoreM CoreExpr
cat0Core  (mgs, oType)                               -- :: oType = forall x y z. Plus x y z => R0 x -> R0 y -> R0 z
  |  (tys, ty) <- splitForAllTyCoVars oType              -- tys = [x, y ,z]
  ,  (_invsFun, (_:_:dplusTy:ty_body)) <- splitTyConApp ty   -- ty  = Plus x y z => R0 x -> R0 y -> R0 z
  ,  (vTys, resultTy) <- splitFunTys (ty_body !! 0)  -- ty_body  = [R0 x -> R0 y -> R0 z]
  = do { let cat0Fun :: CoreExpr
             cat0Fun = mkCoreLams (tys ++ [dplus, rx, ry]) (Cast body (mkCastCo bodyTy resultTy))

             rxTy = vTys !! 0
             ryTy = vTys !! 1

             dn    = mkName 3 "$dplus"
             dplus = mkLocalId dn manyDataConTy dplusTy

             rxn, ryn :: Name
             rxn = mkName 4 "rx"
             ryn = mkName 5 "ry"

             rx, ry :: CoreBndr
             rx = mkLocalId rxn manyDataConTy (scaledThing rxTy)
             ry = mkLocalId ryn manyDataConTy (scaledThing ryTy)

             n = 2

             zTys = [intTy, boolTy]

             bodyTy = mkTupleTy Boxed [intTy, mkTupleTy Boxed (replicate n intTy), mkTupleTy Boxed zTys ]
             body = mkCoreTup []

             debug_msg = text "cat0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "tys"   <+> ppr tys
                                                   , text "dty" <+> ppr dplusTy
                                                   , text "argTy"    <+> ppr vTys
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr cat0Fun
                                                   ]
       ; debugTraceMsg debug_msg
       ; mkIdCore (mgs, oType)
       }
  | otherwise = pprPanic "shouldn't happen cat0Core" (ppr oType)


-- inj0Core :: Type -> CoreM CoreExpr
-- injections go from smaller rows to bigger rows
inj0Core  (mgs, oType) -- forall y z. y ~<~ z => V0 y -> V0 z
  | (tys, ty) <- splitForAllTyCoVars oType                          -- tys      = [y, z]
  , (_invsFun, (_:_:dTy:ty_body:_)) <- splitTyConApp ty             -- ty       = d => V0 z -> V0 y
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp (ty_body)  -- ty_body  = [V0 y -> V0 z]
  = do { fstCoreId <- findId mgs "fstC"
       ; sndCoreId <- findId mgs "sndC"
       ; unsafeCoerceNthCoreId <- findId mgs "unsafeNth"

       ; let injFun :: CoreExpr
             injFun = mkCoreLams (tys ++ [d,ry]) (Cast body co)


       -- The types match because, again, it was justified during type checking

             dn, ryn :: Name
             dn = mkName 2 "$dz~<~y"
             ryn = mkName 3 "ry"

             d, ry :: CoreBndr -- Can be TyVar or Id
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn manyDataConTy argTy

             v = Cast (Var ry) (mkCastCo argTy (mkTupleTy Boxed [intTy, anyType]))

             n = mkCoreApps (Var fstCoreId) [Type intTy, Type anyType,  v]

             s = mkCoreApps (Var sndCoreId) [Type intTy, Type anyType
                                            , Cast (Var d) (mkCastCo dTy $ mkTupleTy Boxed [intTy, anyType])]

             co = mkCastCo bodyTy resultTy

             bodyTy = mkTupleTy Boxed [intTy, anyType]
             body :: CoreExpr
             body = mkCoreApps (Var unsafeCoerceNthCoreId) [Type anyType, Type (mkTupleTy Boxed [intTy, anyType]),  n, s]

             debug_msg = text "inj0Core" <+> vcat [ text "Type:" <+> ppr oType
                                                  , text "dTy:" <+> ppr dTy
                                                  , text "argTy:" <+> ppr argTy
                                                  , text "resultTy:" <+> ppr resultTy
                                                  , ppr injFun ]

       ; debugTraceMsg debug_msg
       ; return injFun }
  | otherwise = pprPanic "shouldn't happen inj0Core" (ppr oType)

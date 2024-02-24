module RoHs.Plugin.Semantics where

import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Core.Type
import GHC.Core.Multiplicity
import GHC.Core.Utils

import GHC.Plugins

import RoHs.Plugin.CoreUtils

type PrimMap = [(FastString, (ModGuts, Type) -> CoreM CoreExpr)]

labR0Core, unlabR0Core, prj0Core, cat0Core, labV0Core, unlabV0Core, inj0Core, ana0Core, brn0Core :: (ModGuts, Type) -> CoreM CoreExpr

primMap :: PrimMap
primMap = [ (fsLit "labR0_I" ,   labR0Core)    -- :: forall s {t}. t -> R0 (R '[s := t])
          , (fsLit "unlabR0_I",  unlabR0Core)  -- :: forall s t. R0 (R '[s := t]) -> t
          , (fsLit "prj0_I",     prj0Core)     -- :: forall z y. z ~<~ y => R0 y -> R0 z
          , (fsLit "cat0_I",     cat0Core)     -- :: forall y z x. Plus y z x => R0 y -> R0 z -> R0 x


          , (fsLit "labV0_I",    labV0Core)    -- :: forall s {t}. t -> V0 (R '[s := t])
          , (fsLit "brn0_I",     brn0Core)     -- :: forall x y z t. Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
          , (fsLit "unlabV0_I",  unlabV0Core)  -- unlabV0 :: forall s {t}. V0 (R '[s := t]) -> t
          , (fsLit "inj0_I",     inj0Core)     --
          , (fsLit "ana0_I",     ana0Core)
          ]

ana0Core = mkIdCore

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
brn0Core (mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [x, y, z, t]
  , (tys, resultTy) <- splitFunTys ty                        -- ty = t -> V0 (R '[s := t])
  , [dPlusTy, argfTy, arggTy, argvzTy] <- fmap scaledThing tys
  = do { brnId <- findId mgs "brn"


        ; let brn0Core :: CoreExpr
              brn0Core = mkCoreLams (tyVars ++ [d, vfx, vgy, vz]) body


              dn, vfxn, vgyn, vzn :: Name
              dn = mkName 0 "dplus"
              vfxn = mkName 1 "vxf"
              vgyn = mkName 2 "vyg"
              vzn  = mkName 3 "vzg"

              d, vfx, vgy, vz :: CoreBndr
              d = mkLocalId dn manyDataConTy dPlusTy
              vfx = mkLocalId vfxn manyDataConTy argfTy
              vgy = mkLocalId vgyn manyDataConTy arggTy
              vz =  mkLocalId vzn manyDataConTy argvzTy

              dRepTy = mkTupleTy Boxed [intTy, anyType]
              dVRepTy = mkTupleTy Boxed [intTy, anyType]

              body = mkCoreApps (Var brnId)
                                [ Type anyType, Type anyType, Type anyType, Type anyType, Type resultTy
                                , Cast (Var d) (mkCastCo dPlusTy dRepTy)
                                , Cast (Var vfx) (mkCastCo argfTy (repackageArg dVRepTy argfTy))
                                , Cast (Var vgy) (mkCastCo arggTy (repackageArg dVRepTy arggTy))
                                , Cast (Var vz) (mkCastCo argvzTy dVRepTy)
                                ]

              debug_msg = text "brn0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTys"    <+> ppr tys
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr brn0Core ]
       ; debugTraceMsg debug_msg
       ; return brn0Core

       }


-- forall s {t}. t -> V0 (R '[s := t])
labV0Core (_, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [s, t]
  , (argTys, resultTy) <- splitFunTys ty                    -- ty = t -> V0 (R '[s := t])
  , [argTy] <- fmap scaledThing argTys
  = do {
         let labV0Fun :: CoreExpr
             labV0Fun = mkCoreLams (tyVars ++ [t]) (Cast body co)

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
  , (tys, resultTy) <- splitFunTys ty -- ty = t -> R0 (R '[s := t])
  , [argTy] <- fmap scaledThing tys
  = do { let lab0Fun :: CoreExpr
             lab0Fun = mkCoreLams (tyVars ++ [t]) (Cast body co)

             tn = mkName 1 "t"
             t =  mkLocalId tn manyDataConTy argTy


             rowRepTy = mkTupleTy Boxed [ mkTupleTy Boxed [intTy, mkTupleTy Boxed [intTy]], argTy]

             body = mkCoreTup [ mkCoreTup [ mkCoreInt 1
                                          , mkCoreTup [mkCoreInt 0] ]   -- ( (1, (0))
                              , mkCoreTup [Var t]                                  -- , t
                              ]                                         -- )

             co = mkCastCo rowRepTy resultTy
             debug_msg = text "labR0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr lab0Fun ]

       ; debugTraceMsg debug_msg
       ; return lab0Fun }
  | otherwise = pprPanic "shouldn't happen labR0Core" (ppr oType)

-- unlabR0Core ::  Type -> CoreM CoreExpr
unlabR0Core  (mgs, oType)   -- oType = forall s t. R0 (R '[s := t]) -> t
  | (tys, ty) <- splitForAllTyVars oType      -- tys      = [s, t]
  , (_vis, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty  -- ty = R0 (R '[s := t]) -> t
  = do { unsafeNthId <- findId mgs "unsafeNth"
       ; let
             unlabR0Fun :: CoreExpr
             unlabR0Fun = mkCoreLams (tys ++ [rId]) body

             rn = mkName 2 "r0"
             rId = mkLocalId rn manyDataConTy argTy

             rTy = mkTupleTy Boxed [intTy, intTy, resultTy]

             co = mkCastCo argTy rTy
             r = Cast (Var rId) co

             index = mkCoreInt 3

             body :: CoreExpr
             body = mkCoreApps (Var unsafeNthId) [Type rTy, Type resultTy, index, r]

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
prj0Core  (mgs, oType) -- forall z y. z ~<~ y => R0 y -> R0 z
  | (tyVars, ty) <- splitForAllTyVars oType      -- tys      = [y, z]
  , (tys, resultTy) <- splitFunTys ty  -- ty       = d => R0 y -> R0 z
  , [dTy, argTy] <- fmap scaledThing tys
  = do { composeId <- findId mgs "compose"
       ; fstId <- findId mgs "fstC"
       ; sndId <- findId mgs "sndC"

       ; let prjFun :: CoreExpr
             prjFun = mkCoreLams (tyVars ++ [d, ry]) (Cast body co)
    --  \ d@(3, (1,3,4)) (r) -> (r !! 1, r !! 3, r !! 4)
    -- The !! is justified as it was computed during type checking
    -- The types should match because, again, it was justified during type checking
             dn, ryn :: Name
             dn = mkName 2 "$dz~<~y"
             ryn = mkName 3 "ry"

             d, ry :: CoreBndr -- Can be TyVar or Id
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn  manyDataConTy argTy

             dRepTy = mkTupleTy Boxed [intTy, anyType]

             rowRepTy = mkTupleTy Boxed [mkTupleTy Boxed [intTy, anyType], anyType]

             co = mkCastCo rowRepTy resultTy

             body :: CoreExpr
             -- Need a match here
             -- match d ry with

             arg_row =  Cast (Var ry) (mkCastCo argTy rowRepTy)

             fer = mkCoreApps (Var fstId) [Type dRepTy, Type anyType, arg_row]
             ser = mkCoreApps (Var sndId) [Type dRepTy, Type anyType, arg_row]

             body = mkCoreTup [ mkCoreApps (Var composeId) [ Type anyType
                                                           , Type anyType
                                                           , Type anyType
                                                           , Cast (Var d) (mkCastCo dTy dRepTy)
                                                           , fer
                                                           ]
                              , ser
                              ]

              -- prj d (e, r) -> (compose d e, r)
              -- prj = \ d er -> (compose d fst er, snd er)

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
  |  (tyVars, ty) <- splitForAllTyVars oType         -- tys = [x, y ,z]
  , (tys, resultTy) <- splitFunTys ty       -- ty  = Plus x y z => R0 x -> R0 y -> R0 z
  ,  [dplusTy, argxTy, argyTy] <- fmap scaledThing tys      -- ty_body  = [R0 x, R0 y]
  = do { catId <- findId mgs "catC"

       ; let cat0Fun :: CoreExpr
             cat0Fun = mkCoreLams (tyVars ++ [dplus, rx, ry]) (Cast body (mkCastCo rowRepTy resultTy))

             dRepTy = mkTupleTy Boxed [intTy, anyType]
             rowRepTy = mkTupleTy Boxed [mkTupleTy Boxed [intTy, anyType], anyType]

             dn    = mkName 3 "$dplus"
             dplus = mkLocalId dn manyDataConTy dplusTy

             rxn, ryn :: Name
             rxn = mkName 4 "rx"
             ryn = mkName 5 "ry"

             rx, ry :: CoreBndr
             rx = mkLocalId rxn manyDataConTy argxTy
             ry = mkLocalId ryn manyDataConTy argyTy

             body = mkCoreApps (Var catId) [ Type anyType, Type anyType, Type anyType, Type anyType, Type anyType, Type anyType, Type anyType
                                           , Cast (Var dplus) (mkCastCo dplusTy dRepTy)
                                           , Cast (Var rx) (mkCastCo argxTy rowRepTy)
                                           , Cast (Var ry) (mkCastCo argyTy rowRepTy)
                                           ]

             debug_msg = text "cat0Core" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "tys"   <+> ppr tys
                                                   , text "dty" <+> ppr dplusTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr cat0Fun
                                                   ]
       ; debugTraceMsg debug_msg
       ; return cat0Fun
       }
  | otherwise = pprPanic "shouldn't happen cat0Core" (ppr oType)

-- inj0Core :: Type -> CoreM CoreExpr
-- injections go from smaller rows to bigger rows
inj0Core  (mgs, oType) -- forall y z. y ~<~ z => V0 y -> V0 z
  | (tys, ty) <- splitForAllTyVars oType                          -- tys      = [y, z]
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

module RoHs.Plugin.Semantics where

import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Core.Type
import GHC.Core.TyCo.Rep

import GHC.Plugins

import RoHs.Plugin.CoreUtils

labRCore, unlabRCore, prjCore, catCore, labVCore, unlabVCore, injCore, ana1Core, ana0Core, brnCore
  :: (RoHsPluginOptions, ModGuts, Type) -> CoreM CoreExpr


primMap :: PrimMap
primMap = [ (fsLit "labR0_I" ,   labRCore)    -- :: forall s {t}. t -> R0 (R '[s := t])
          , (fsLit "unlabR0_I",  unlabRCore)  -- :: forall s t. R0 (R '[s := t]) -> t
          , (fsLit "prj0_I",     prjCore)     -- :: forall z y. z ~<~ y => R0 y -> R0 z
          , (fsLit "cat0_I",     catCore)     -- :: forall y z x. Plus y z x => R0 y -> R0 z -> R0 x
          -- , (fsLit "syn0_I",     undefined)      -- :: (forall s y {u}. All c z
          --                                     -- => (Plus (R '[s := u]) y z, R '[s := u] ~<~ z, y ~<~ z, c u) => Proxy s -> u) -> R0 z


          , (fsLit "labV0_I",    labVCore)    -- :: forall s {t}. t -> V0 (R '[s := t])
          , (fsLit "brn0_I",     brnCore)     -- :: forall x y z t. Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
          , (fsLit "unlabV0_I",  unlabVCore)  -- :: forall s {t}. V0 (R '[s := t]) -> t
          , (fsLit "inj0_I",     injCore)     -- :: forall y z. y ~<~ z => V0 y -> V0 z
          , (fsLit "anaA0_I",    ana0Core)     -- :: forall c {z} {t}. All c z
                                               --      => (forall s y {u}. (Plus (R '[s := u]) y z, c u) =>  Proxy s -> u -> t)
                                               --      -> V0 z -> t

          , (fsLit "labR1_I", labRCore)
          , (fsLit "unlabR1_I", unlabRCore)
          , (fsLit "prj1_I", prjCore)
          , (fsLit "cat1_I", catCore)
          , (fsLit "labV1_I", labVCore)
          , (fsLit "unlabV1_I", unlabVCore)
          , (fsLit "inj1_I", injCore)
          , (fsLit "brn1_I", brnCore)

          , (fsLit "anaA1_I", ana1Core)
          ]


-- :: forall c {z} {t}. All c z
--      => (forall s y {u}. (Plus (R '[s := u]) y z, R '[s := t] ~<~ z, y ~<~ z, c u) =>  Proxy s -> u -> t)
--      -> V0 z -> t
ana0Core (opts, mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType     -- tyVars = [c, z, t]
  , (tys, resultTy) <- splitFunTys ty           -- [forall ... , V0 z], t
  , [dAllTy, fTy, vzTy] <- fmap scaledThing tys
  = do { fstId <- findId mgs "fstC"
       ; sndId <- findId mgs "sndC"
       ; oneIn <- findId mgs "oneIn"
       ; manyIn <- findId mgs "manyIn"
       ; plusE <- findId mgs "plusE"
       ; unsafeNth <- findId mgs "unsafeNth"
       ; us <- getUniquesM
       ; let ana0Fun = mkCoreLams (tyVars ++ [dId, fId, vId]) body

             dn, fn, vn :: Name
             dn = mkName (us !! 0) "$dAll"
             fn = mkName (us !! 1) "f"
             vn = mkName (us !! 2) "vz"

             dId = mkLocalId dn  manyDataConTy dAllTy
             fId = mkLocalId fn  manyDataConTy fTy
             vId = mkLocalId vn  manyDataConTy vzTy

             dAllRepTy = mkTupleTy1 Boxed [intTy, anyType]
             vRepTy = mkTupleTy1 Boxed [intTy, anyType]

             dAllrep = Cast (Var dId) (mkCastCo dAllTy dAllRepTy)
             vrep = Cast (Var vId) (mkCastCo vzTy vRepTy)

             (f_tyVars, f_plusdTy, f_leq1, f_leq2, cuTy, proxyTy, _) = decomp fTy
             f_tyVarsTy = fmap (anyTypeOfKind . idType) f_tyVars
             subst = zipTvSubst f_tyVars f_tyVarsTy

             -- This is ugly, but meh.
             body :: CoreExpr
             body = mkCoreApps (Var fId)
                      (fmap Type f_tyVarsTy
                      ++ [ Cast (mkCoreApps (Var plusE)  [ Type anyType
                                                     , (mkCoreApps (Var fstId) [ Type intTy
                                                                               , Type anyType
                                                                               , dAllrep])
                                                     , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]])
                       (mkCastCo (substTy subst dAllRepTy) (substTy subst f_plusdTy))
                     , Cast (mkCoreApps (Var oneIn)  [ Type anyType
                                                     , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]])
                       (substCo subst $ mkCastCo dAllRepTy f_leq1) -- leq1
                     , Cast (mkCoreApps (Var manyIn) [ Type anyType
                                                     , mkCoreApps (Var fstId) [Type intTy, Type anyType, dAllrep]
                                                     , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]
                                                     ]) (substCo subst $ mkCastCo dAllRepTy f_leq2) -- leq2
                     , Cast (mkCoreApps (Var unsafeNth) [ Type anyType
                                                        , Type anyType
                                                        , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]
                                                        , mkCoreApps (Var sndId) [Type intTy, Type anyType, dAllrep]])
                       (substCo subst $ mkCastCo anyType cuTy)
                     , Cast (mkCoreTup []) (substCo subst $ mkCastCo (mkTupleTy1 Boxed []) proxyTy)-- not used so making this up
                     , mkCoreApps (Var sndId) [Type intTy, Type anyType, vrep]])

             debug_msg = text "ana0Fun" <+> vcat [ text "Type" <+> ppr oType
                                                 , text "TyBnds"   <+> ppr tyVars
                                                 , text "argTys"    <+> ppr tys
                                                 , text "resultTy" <+> ppr resultTy
                                                 , text "decompTy" <+> (ppr $ decomp fTy)
                                                 , ppr ana0Fun
                                                 ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return ana0Fun

       }

  | otherwise = pprPanic "shouldn't happen ana0Core" (ppr oType)

decomp :: Type -> ([TyVar], Type, Type, Type, Type, Type, Type)
decomp fTy | (f_tyVars, f_ty) <- splitForAllTyVars fTy
           , (f_tys, _) <- splitFunTys f_ty
           , [f_plusdTy, f_leq1, f_leq2, cuTy, proxy, u] <- fmap scaledThing f_tys
           = (f_tyVars, f_plusdTy, f_leq1, f_leq2, cuTy, proxy, u)
           | otherwise = error "decomp in ana0Core"


-- :: forall x y z t. Plus x y z => (V0 x -> t) -> (V0 y -> t) -> V0 z -> t
brnCore (opts, mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [x, y, z, t]
  , (tys, resultTy) <- splitFunTys ty                        -- ty = t -> V0 (R '[s := t])
  , [dPlusTy, argfTy, arggTy, argvzTy] <- fmap scaledThing tys
  = do { brnId <- findId mgs "brn"
       ; us <- getUniquesM

        ; let brnFun :: CoreExpr
              brnFun = mkCoreLams (tyVars ++ [d, vfx, vgy, vz]) body


              dn, vfxn, vgyn, vzn :: Name
              dn = mkName (us !! 0) "dplus"
              vfxn = mkName (us !! 1) "vxf"
              vgyn = mkName (us !! 2) "vyg"
              vzn  = mkName (us !! 3) "vzg"

              d, vfx, vgy, vz :: CoreBndr
              d = mkLocalId dn manyDataConTy dPlusTy
              vfx = mkLocalId vfxn manyDataConTy argfTy
              vgy = mkLocalId vgyn manyDataConTy arggTy
              vz =  mkLocalId vzn manyDataConTy argvzTy

              dRepTy = mkTupleTy1 Boxed [intTy, anyType]
              dVRepTy = mkTupleTy1 Boxed [intTy, anyType]

              body = mkCoreApps (Var brnId)
                                [ Type anyType, Type anyType, Type anyType, Type anyType, Type resultTy
                                , Cast (Var d) (mkCastCo dPlusTy dRepTy)
                                , Cast (Var vfx) (mkCastCo argfTy (repackageArg dVRepTy argfTy))
                                , Cast (Var vgy) (mkCastCo arggTy (repackageArg dVRepTy arggTy))
                                , Cast (Var vz) (mkCastCo argvzTy dVRepTy)
                                ]

              debug_msg = text "brnFun" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTys"    <+> ppr tys
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr brnFun ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return brnFun

       }
  | otherwise = pprPanic "shouldn't happen brn0Core" (ppr oType)

-- forall s {t}. t -> V0 (R '[s := t])
labVCore (opts, _, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                  -- tyVars = [s, t]
  , (argTys, resultTy) <- splitFunTys ty                    -- ty = t -> V0 (R '[s := t])
  , [argTy] <- fmap scaledThing argTys
  = do { us <- getUniquesM

       ; let labV0Fun :: CoreExpr
             labV0Fun = mkCoreLams (tyVars ++ [t]) body

             tn = mkName (us !! 1) "t"
             t = mkLocalId tn manyDataConTy argTy

             co = mkCastCo (mkTupleTy1 Boxed [intTy, argTy]) resultTy
             body = Cast (mkCoreTup [mkCoreInt 0, (Var t)]) co

             debug_msg = text "labVCore" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr labV0Fun ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return labV0Fun
       }
  | otherwise = pprPanic "shouldn't happen labVCore" (ppr oType)
-- unlabV0 :: forall s {t}. V0 (R '[s := t]) -> t
unlabVCore (opts, mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType                 -- tys [s, t]
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty -- ty = V0 (R '[s := t]) -> t
  = do { sndId <- findId mgs "sndC"
       ; us <- getUniquesM
       ; let unlabV0Fun :: CoreExpr
             unlabV0Fun = mkCoreLams (tyVars ++ [vId]) (Cast body co)

             vn = mkName (us !! 2) "v0"

             vId = mkLocalId vn manyDataConTy argTy

             co = mkCastCo anyType resultTy

             v = Cast (Var vId) (mkCastCo argTy (mkTupleTy1 Boxed [intTy, anyType]))

             body = mkCoreApps (Var sndId) [Type intTy, Type anyType, v]

             debug_msg = text "unlabVCore" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr unlabV0Fun ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return unlabV0Fun
       }
 | otherwise = pprPanic "shouldn't happen unlabVCore" (ppr oType)

labRCore  (opts, _, oType) -- :: forall s {t}. t -> R0 (R '[s := t])
  | (tyVars, ty) <- splitForAllTyVars oType                 -- tys [s, t]
  , (tys, resultTy) <- splitFunTys ty -- ty = t -> R0 (R '[s := t])
  , [argTy] <- fmap scaledThing tys
  = do { us <- getUniquesM
       ; let lab0Fun :: CoreExpr
             lab0Fun = mkCoreLams (tyVars ++ [t]) (Cast body co)

             tn = mkName (us !! 1) "t"
             t =  mkLocalId tn manyDataConTy argTy

             rowRepTy = mkTupleTy1 Boxed [ mkTupleTy1 Boxed [intTy, mkTupleTy1 Boxed [intTy]], mkTupleTy1 Boxed [argTy]]

             body = mkCoreTup [ mkCoreTup [ mkCoreInt 1
                                          , mkCoreBoxedTuple [mkCoreInt 0] ]   -- ( (1, (0))
                              , mkCoreBoxedTuple [Var t]                       -- , (t)
                              ]                                                -- )

             co = mkCastCo rowRepTy resultTy
             debug_msg = text "labRCore" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "TyBnds"   <+> ppr tyVars
                                                   , text "argTy"    <+> ppr argTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr lab0Fun ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return lab0Fun }
  | otherwise = pprPanic "shouldn't happen labRCore" (ppr oType)

-- unlabRCore ::  Type -> CoreM CoreExpr
unlabRCore (opts, mgs, oType)   -- oType = forall s t. R0 (R '[s := t]) -> t
  | (tys, ty) <- splitForAllTyVars oType      -- tys      = [s, t]
  , (_vis, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty  -- ty = R0 (R '[s := t]) -> t
  = do { unsafeNthId <- findId mgs "unsafeNth"
       ; us <- getUniquesM
       ; let unlabR0Fun :: CoreExpr
             unlabR0Fun = mkCoreLams (tys ++ [rId]) body

             rn = mkName (us !! 2) "r0"
             rId = mkLocalId rn manyDataConTy argTy

             repTy = mkTupleTy1 Boxed [mkTupleTy1 Boxed [intTy, mkTupleTy1 Boxed [intTy]], mkTupleTy1 Boxed [resultTy]]

             co = mkCastCo argTy repTy
             r = Cast (Var rId) co

             index = mkCoreInt 1

             body :: CoreExpr
             body = mkCoreApps (Var unsafeNthId)
               [ Type (mkTupleTy1 Boxed [resultTy])
               , Type resultTy
               , mkCoreInt 0
               , mkCoreApps (Var unsafeNthId) [Type repTy, Type (mkTupleTy1 Boxed [resultTy]), index, r]
               ]



             debug_msg = text "unlabRCore" <+> vcat [ text "Type:" <+> ppr oType
                                                     , text "tys:" <+> ppr tys
                                                     , text "argTy:" <+> ppr argTy
                                                     , text "resultTy:" <+> ppr resultTy
                                                     , ppr unlabR0Fun
                                                     ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return unlabR0Fun
       }
  | otherwise = pprPanic "shouldn't happen unlabRCore" (ppr oType)


prjCore (opts, mgs, oType) -- forall z y. z ~<~ y => R0 y -> R0 z
  | (tyVars, ty) <- splitForAllTyVars oType      -- tys      = [y, z]
  , (tys, resultTy) <- splitFunTys ty  -- ty       = d => R0 y -> R0 z
  , [dTy, argTy] <- fmap scaledThing tys
  = do { composeId <- findId mgs "compose"
       ; fstId <- findId mgs "fstC"
       ; sndId <- findId mgs "sndC"
       ; us <- getUniquesM

       ; let prjFun :: CoreExpr
             prjFun = mkCoreLams (tyVars ++ [d, ry]) (Cast body co)
    -- The !! is justified as it was computed during type checking
    -- The types should match because, again, it was justified during type checking
             dn, ryn :: Name
             dn = mkName (us !! 2) "$dz~<~y"
             ryn = mkName (us !! 3) "ry"

             d, ry :: CoreBndr -- Can be TyVar or Id
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn  manyDataConTy argTy

             dRepTy = mkTupleTy1 Boxed [intTy, anyType]

             rowRepTy = mkTupleTy1 Boxed [mkTupleTy1 Boxed [intTy, anyType], anyType]

             co = mkCastCo rowRepTy resultTy

             arg_row =  Cast (Var ry) (mkCastCo argTy rowRepTy)

             fer = mkCoreApps (Var fstId) [Type dRepTy, Type anyType, arg_row]
             ser = mkCoreApps (Var sndId) [Type dRepTy, Type anyType, arg_row]

             body :: CoreExpr
             body = mkCoreTup [ mkCoreApps (Var composeId)
                                [ Type anyType
                                , Type anyType
                                , Type anyType
                                , Cast (Var d) (mkCastCo dTy dRepTy)
                                , fer ]
                              , ser ]

             debug_msg = text "prjCore" <+> vcat [ text "Type:" <+> ppr oType
                                                  , text "dTy:" <+> ppr dTy
                                                  , text "argTy:" <+> ppr argTy
                                                  , text "resultTy:" <+> ppr resultTy
                                                  , ppr prjFun ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return prjFun }
  | otherwise = pprPanic "shouldn't happen prjCore" (ppr oType)

-- catCore :: Type -> CoreM CoreExpr
catCore (opts, mgs, oType)                                    -- :: oType = forall x y z. Plus x y z => R0 x -> R0 y -> R0 z
  |  (tyVars, ty) <- splitForAllTyVars oType              -- tys = [x, y ,z]
  , (tys, resultTy) <- splitFunTys ty                     -- ty  = Plus x y z => R0 x -> R0 y -> R0 z
  ,  [dplusTy, argxTy, argyTy] <- fmap scaledThing tys    -- ty_body  = [R0 x, R0 y]
  = do { catId <- findId mgs "catC"
       ; us <- getUniquesM
       ; let cat0Fun :: CoreExpr
             cat0Fun = mkCoreLams (tyVars ++ [dplus, rx, ry]) (Cast body (mkCastCo rowRepTy resultTy))

             dRepTy = mkTupleTy1 Boxed [intTy, anyType]
             rowRepTy = mkTupleTy1 Boxed [mkTupleTy1 Boxed [intTy, anyType], anyType]

             dn    = mkName (us !! 3) "$dplus"
             dplus = mkLocalId dn manyDataConTy dplusTy

             rxn, ryn :: Name
             rxn = mkName (us !! 4) "rx"
             ryn = mkName (us !! 5) "ry"

             rx, ry :: CoreBndr
             rx = mkLocalId rxn manyDataConTy argxTy
             ry = mkLocalId ryn manyDataConTy argyTy

             body = mkCoreApps (Var catId) [ Type anyType, Type anyType, Type anyType, Type anyType, Type anyType, Type anyType, Type anyType
                                           , Cast (Var dplus) (mkCastCo dplusTy dRepTy)
                                           , Cast (Var rx) (mkCastCo argxTy rowRepTy)
                                           , Cast (Var ry) (mkCastCo argyTy rowRepTy)
                                           ]

             debug_msg = text "catCore" <+> vcat [ text "Type" <+> ppr oType
                                                   , text "tys"   <+> ppr tys
                                                   , text "dty" <+> ppr dplusTy
                                                   , text "resultTy" <+> ppr resultTy
                                                   , ppr cat0Fun
                                                   ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return cat0Fun
       }
  | otherwise = pprPanic "shouldn't happen catCore" (ppr oType)

-- injections go from smaller rows to bigger rows
injCore (opts, mgs, oType) -- forall y z. y ~<~ z => V0 y -> V0 z
  | (tys, ty) <- splitForAllTyVars oType                          -- tys      = [y, z]
  , (_invsFun, (_:_:dTy:ty_body:_)) <- splitTyConApp ty             -- ty       = d => V0 z -> V0 y
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp (ty_body)  -- ty_body  = [V0 y -> V0 z]
  = do { injId <- findId mgs "inj"
       ; us <- getUniquesM
       ; let injFun :: CoreExpr
             injFun = mkCoreLams (tys ++ [d,ry]) (Cast body co)


       -- The types match because, again, it was justified during type checking

             dn, ryn :: Name
             dn = mkName (us !! 2) "$dz~<~y"
             ryn = mkName (us !! 3) "ry"

             d, ry :: CoreBndr -- Can be TyVar or Id
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn manyDataConTy argTy

             dRepTy = mkTupleTy1 Boxed [intTy, anyType]
             dRowRepTy = mkTupleTy1 Boxed [intTy, anyType]

             co = mkCastCo dRowRepTy resultTy

             body :: CoreExpr
             body = mkCoreApps (Var injId) [ Type anyType, Type anyType
                                           , Cast (Var d) (mkCastCo dTy dRepTy)
                                           , Cast (Var ry) (mkCastCo argTy dRowRepTy)
                                           ]

             debug_msg = text "injCore" <+> vcat [ text "Type:" <+> ppr oType
                                                  , text "dTy:" <+> ppr dTy
                                                  , text "argTy:" <+> ppr argTy
                                                  , text "resultTy:" <+> ppr resultTy
                                                  , ppr injFun ]

       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return injFun }
  | otherwise = pprPanic "shouldn't happen injCore" (ppr oType)


-- forall c {z} {t} {u}.
--          All c z =>
--          (forall s y {f}. (Plus (R '[s := f]) y z, R '[s := f] ~<~ z, y ~<~ z, c f)
--                         => Proxy s -> f u -> t)
--       -> V1 z u -> t
ana1Core (opts, mgs, oType)
  | (tyVars, ty) <- splitForAllTyVars oType     -- tyVars = [c, z, t]
  , (tys, resultTy) <- splitFunTys ty           -- [forall ... , V0 z], t
  , [dAllTy, fTy, vzTy] <- fmap scaledThing tys
  = do { fstId <- findId mgs "fstC"
       ; sndId <- findId mgs "sndC"
       ; oneIn <- findId mgs "oneIn"
       ; manyIn <- findId mgs "manyIn"
       ; plusE <- findId mgs "plusE"
       ; unsafeNth <- findId mgs "unsafeNth"

       ; us <- getUniquesM

       ; let ana1Fun = mkCoreLams (tyVars ++ [dId, fId, vId]) body

             dn, fn, vn :: Name
             dn = mkName (us !! 0) "$dAll"
             fn = mkName (us !! 1) "f"
             vn = mkName (us !! 2) "vz"

             dId = mkLocalId dn  manyDataConTy dAllTy
             fId = mkLocalId fn  manyDataConTy fTy
             vId = mkLocalId vn  manyDataConTy vzTy

             dAllRepTy = mkTupleTy1 Boxed [intTy, anyType]
             vRepTy = mkTupleTy1 Boxed [intTy, anyType]

             dAllrep = Cast (Var dId) (mkCastCo dAllTy dAllRepTy)
             vrep = Cast (Var vId) (mkCastCo vzTy vRepTy)

             (f_tyVars, f_plusdTy, f_leq1, f_leq2, cuTy, proxyTy, uTy) = decomp fTy

             f_tyVarsTy = fmap (anyTypeOfKind . idType) f_tyVars

             subst = zipTvSubst f_tyVars f_tyVarsTy

             -- This is ugly, but meh.
             body :: CoreExpr
             body = mkCoreApps (Var fId) (
                        (fmap Type f_tyVarsTy)
                        ++ [ Cast (mkCoreApps (Var plusE)
                                [ Type anyType
                                , (mkCoreApps (Var fstId) [ Type intTy
                                                          , Type anyType
                                                          , dAllrep])
                                , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]])
                          (mkCastCo (substTy subst dAllRepTy) (substTy subst f_plusdTy))
                        , Cast (mkCoreApps (Var oneIn)  [ Type anyType
                                                        , mkCoreApps (Var fstId)
                                                          [Type intTy
                                                          , Type anyType, vrep]])
                          (substCo subst $ mkCastCo dAllRepTy f_leq1) -- leq1
                        , Cast (mkCoreApps (Var manyIn) [ Type anyType
                                                        , mkCoreApps (Var fstId) [Type intTy
                                                                                 , Type anyType, dAllrep]
                                                        , mkCoreApps (Var fstId) [Type intTy, Type anyType, vrep]
                                                        ])
                          (substCo subst $ mkCastCo dAllRepTy f_leq2) -- leq2
                        , Cast (mkCoreApps (Var unsafeNth) [ Type anyType
                                                           , Type anyType
                                                           , mkCoreApps (Var fstId)
                                                             [Type intTy, Type anyType, vrep]
                                                           , mkCoreApps (Var sndId) [Type intTy
                                                                                    , Type anyType
                                                                                    , dAllrep]])
                          (substCo subst $ mkCastCo anyType cuTy)
                        , Cast (mkCoreTup []) (substCo subst $ mkCastCo (mkTupleTy1 Boxed []) proxyTy)-- not used so making this up
                        , mkCoreApps (Var sndId) [ Type intTy
                                                 , Type (mkAppTy
                                                         (anyTypeOfKind (mkTyVarTy (tyVars !! 0)
                                                                         `mkVisFunTyMany` liftedTypeKind))
                                                          (mkTyVarTy (tyVars !! 4)))
                                                 , Cast vrep (mkCastCo
                                                              vRepTy
                                                              (mkTupleTy1 Boxed [intTy
                                                                               , substTy subst $  uTy ]))]
                        ])

             debug_msg = text "ana1Fun" <+> vcat [ text "Type" <+> ppr oType
                                                 , text "TyBnds"   <+> ppr tyVars
                                                 , text "argTys"    <+> ppr tys
                                                 , text "resultTy" <+> ppr resultTy
                                                 , text "decompTy" <+> (ppr $ decomp fTy)
                                                 , ppr ana1Fun
                                                 ]
       ; whenDebugM opts $ debugTraceMsg debug_msg
       ; return ana1Fun

       }

  | otherwise = pprPanic "shouldn't happen ana1Core" (ppr oType)

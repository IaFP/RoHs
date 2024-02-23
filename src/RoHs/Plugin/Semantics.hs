module RoHs.Plugin.Semantics where

import GHC.Builtin.Names

import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Types.TyThing
import GHC.Types.Name.Cache
import GHC.Core.Type
import GHC.Core.Multiplicity
import GHC.Core.Utils
import GHC.Iface.Env
import GHC.Tc.Utils.Env

import GHC.Plugins

import GHC.Types.Literal
import GHC.Types.Unique

import Control.Concurrent.MVar
import Data.Maybe

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
                   , (fsLit "unlabV0",  unlabV0Core)
                   , (fsLit "inj0",     inj0Core)
                   , (fsLit "ana0",     ana0Core)
                   , (fsLit "anaE0",    mkIdCore)
                   , (fsLit "anaA0",    mkIdCore)
                   ]

-- unlabR0Core  = mkIdCore
unlabV0Core = mkIdCore
labV0Core = mkIdCore
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


labR0Core  (_, oType) -- :: forall s {t}. t -> R0 (R '[s := t])
  | (tyVars, ty) <- splitForAllTyVars oType                 -- tys [s, t]
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty -- ty = t -> R0 (R '[s := t])
  = do { let lab0Fun :: CoreExpr
             lab0Fun = mkCoreLams [tyVars !! 0, tyVars !! 1 , t] (Cast body co)

             sn   = mkName 0 "s"
             tn = mkName 1 "t"

             sTyVar, tTyVar :: TyVar
             sTyVar = getTyVar (mkTyVarTy (tyVars !! 0))
             tTyVar = getTyVar (mkTyVarTy (tyVars !! 1))

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

findId :: ModGuts -> String -> CoreM Id
-- the ModuleGuts are of the module that is being core processed.
findId mgs n = do this_mod <- getModule
              -- liftIO $ lookupIfaceTop nOcc
                  let binds = mg_binds mgs
                      nrs  = [ nr | nr@(NonRec var b) <- binds , n == getOccString var  ]
                  debugTraceMsg (text "findId " <+> vcat [text n,  ppr nrs])
                  case nrs of
                    (NonRec var _):_ -> return var
                    _ ->  pprPanic "findId" (text "couldn't find" <+> vcat [text n,  ppr nrs])

-- findId :: String -> CoreM Id
-- findId n = do let nOcc = mkVarOcc n
--               name <- lookupOrig pRELUDE nOcc
--               lookupId name


-- unlabR0Core ::  Type -> CoreM CoreExpr
unlabR0Core  (_, oType)   -- oType = forall s t. R0 (R '[s := t]) -> t
  | (tys, ty) <- splitForAllTyCoVars oType      -- tys      = [s, t]
  , (_vis, (_:_:_:argTy:resultTy:_)) <- splitTyConApp ty  -- ty = R0 (R '[s := t]) -> t
  = do { -- snd <- findId ("snd")
       ; let
             unlabR0Fun :: CoreExpr
             unlabR0Fun = mkCoreLams [s, t, r] (Cast body co)

             sn, tn :: Name
             sn = mkName 0 "s"
             tn = mkName 1 "t"
             rn = mkName 2 "r"

             s, t :: TyVar
             s = getTyVar (mkTyVarTy $ tys !! 0)
             t = getTyVar (mkTyVarTy $ tys !! 1)
             r = mkLocalId rn manyDataConTy argTy

             bodyTy = resultTy
             body :: CoreExpr
             body = App (mkCoreTup []) (Cast (Var r) (co')) -- mkCoreInt 42

             co = mkCastCo anyTy resultTy
             co' = mkCastCo argTy (mkTupleTy Boxed [intTy, mkListTy intTy, mkListTy anyTy])
             debug_msg = text "unlabR0Core" <+> vcat [ text "Type:" <+> ppr oType
                                                     , text "tys:" <+> ppr tys
                                                     , text "argTy:" <+> ppr argTy
                                                     , text "resultTy:" <+> ppr resultTy
                                                     , ppr unlabR0Fun
                                                     ]

       ; debugTraceMsg debug_msg
       ; return unlabR0Fun
       }



-- prj0Core :: Type -> CoreM CoreExpr
prj0Core  (_, oType) -- forall z y. z ~<~ y => R0 y -> R0 z
  | (tys, ty) <- splitForAllTyCoVars oType      -- tys      = [y, z]
  , (_invsFun, (_:_:dTy:ty_body:_)) <- splitTyConApp ty  -- ty       = d => R0 y -> R0 z
  , (_visFun, (_:_:_:argTy:resultTy:_)) <- splitTyConApp (ty_body)  -- ty_body  = [R0 y -> R0 z]
  = do { let prjFun :: CoreExpr
             prjFun = mkCoreLams [z, y, d, ry] (Cast body co)
    --  \ d@(3, (1,3,4)) (r) -> (r !! 1, r !! 3, r !! 4)
    -- The !! is justified as it was computed during type checking
    -- The types match because, again, it was justified during type checking
             zn, yn, dn, ryn :: Name
             zn = mkName 0 "z"
             yn = mkName 1 "y"
             dn = mkName 2 "$dz~<~y"
             ryn = mkName 3 "ry"

             z, y, d, ry :: CoreBndr -- Can be TyVar or Id
             z = mkTyVar zn (idType $ tys !! 0)
             y = mkTyVar yn (idType $ tys !! 1)
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

-- cat0Core :: Type -> CoreM CoreExpr
cat0Core  (mgs, oType)                               -- :: oType = forall x y z. Plus x y z => R0 x -> R0 y -> R0 z
  |  (tys, ty) <- splitForAllTyCoVars oType              -- tys = [x, y ,z]
  ,  (_invsFun, (_:_:dplusTy:ty_body)) <- splitTyConApp ty   -- ty  = Plus x y z => R0 x -> R0 y -> R0 z
  ,  (vTys, resultTy) <- splitFunTys (ty_body !! 0)  -- ty_body  = [R0 x -> R0 y -> R0 z]
  = do { let cat0Fun :: CoreExpr
             cat0Fun = mkCoreLams [x, y, z, dplus, rx, ry] (Cast body (mkCastCo bodyTy resultTy))

             rxTy = vTys !! 0
             ryTy = vTys !! 1

             xn = mkName 0 "x"
             yn = mkName 1 "y"
             zn = mkName 2 "z"


             x, y, z :: CoreBndr
             x = mkTyVar xn (idType (tys !! 0))
             y = mkTyVar yn (idType (tys !! 1))
             z = mkTyVar zn (idType (tys !! 2))

             dn    = mkName 3 "$dplus"
             dplus = mkLocalId dn manyDataConTy dplusTy

             rxn, ryn :: Name
             rxn = mkName 4 "rx"
             ryn = mkName 4 "ry"

             rx, ry :: CoreBndr
             rx = mkLocalId rxn manyDataConTy (scaledThing $ vTys !! 0)
             ry = mkLocalId rxn manyDataConTy (scaledThing $ vTys !! 1)

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
             injFun = mkCoreLams [y, z, d, ry] (Cast body co)


    -- The types match because, again, it was justified during type checking
             zn, yn, dn, ryn :: Name
             zn = mkName 0 "z"
             yn = mkName 1 "y"
             dn = mkName 2 "$dz~<~y"
             ryn = mkName 3 "ry"

             z, y, d, ry :: CoreBndr -- Can be TyVar or Id
             y = mkTyVar yn (idType $ tys !! 0)
             z = mkTyVar zn (idType $ tys !! 1)
             d = mkLocalId dn manyDataConTy dTy
             ry = mkLocalId ryn manyDataConTy argTy

             v = Cast (Var ry) (mkCastCo argTy (mkTupleTy Boxed [intTy, anyTy]))

             n = mkCoreApps (Var fstCoreId) [Type intTy, v]

             s = mkCoreApps (Var sndCoreId) [Type intTy
                                            , Cast (Var d) (mkCastCo dTy $ mkTupleTy Boxed [intTy, anyTy])]

             b = mkCoreApps (Var unsafeCoerceNthCoreId) [(Type intTy), (Type anyTy), n, s]

             co = mkCastCo bodyTy resultTy

             bodyTy = mkTupleTy Boxed [intTy, anyTy]

             body :: CoreExpr

             -- Need a match here
             -- match d ry with
             body = b


             debug_msg = text "inj0Core" <+> vcat [ text "Type:" <+> ppr oType
                                                  , text "dTy:" <+> ppr dTy
                                                  , text "argTy:" <+> ppr argTy
                                                  , text "resultTy:" <+> ppr resultTy
                                                  , ppr injFun ]

       ; debugTraceMsg debug_msg
       ; return injFun }

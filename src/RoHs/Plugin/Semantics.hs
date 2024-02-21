module RoHs.Plugin.Semantics where

import GHC.Plugins
import GHC.Core.Type
import GHC.Types.Literal
import GHC.Types.Unique

import GHC.Core
import qualified GHC.TcPlugin.API as API

import RoHs.Plugin.CoreUtils

type PrimMap = [(FastString, (Type -> CoreM CoreExpr))]

primMap :: PrimMap
primMap = [ (fsLit "labR0" ,   labR0Core)    -- :: forall s {t}. t -> R0 (R '[s := t])
          , (fsLit "unlabR0",  unlabR0Core)  -- :: forall s t. V0 (R '[s := t]) -> t
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

labR0Core, unlabR0Core, prj0Core, cat0Core, labV0Core, unlabV0Core, inj0Core, ana0Core, brn0Core :: Type -> CoreM CoreExpr
labR0Core = mkIdCore
unlabR0Core  = mkIdCore
cat0Core = mkIdCore
unlabV0Core = mkIdCore
labV0Core = mkIdCore
inj0Core = mkIdCore
ana0Core = mkIdCore
brn0Core = mkIdCore

mkIdCore :: Type -> CoreM CoreExpr
mkIdCore oType = return $ Cast (mkCoreLams [a, x] (Var x)) (mkCastCo idTy oType)
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


-- prj0Core :: Type -> CoreM CoreExpr
prj0Core oType
  | (tys, ty) <- splitForAllTyCoVars oType      -- tys      = [y, z]
  , (_invsFun, (_:_:dTy:ty_body)) <- splitTyConApp ty  -- ty       = d => R0 y -> R0 z
  , (_visFun, (_:_:_:argTy:resultTy)) <- splitTyConApp (ty_body !! 0)  -- ty_body  = [R0 y -> R0 z]
  = do { let mkPrjFun :: CoreExpr
             mkPrjFun = mkCoreLams [z, y, d, ry] body
    --  \ (3, (1,3,4)) (d) -> (d !! 1, d !! 3, d !! 4)
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


             body :: CoreExpr
             -- Need a match here
             -- match d ry with


             body = Case (Var ry) ry (resultTy !! 0) []

             debug_msg = text "prj0Core" <+> vcat [ ppr oType
                                                  , ppr dTy
                                                  , ppr argTy
                                                  , ppr resultTy
                                                  , ppr mkPrjFun ]

       ; debugTraceMsg debug_msg
       ; mkIdCore oType }

getLitInt :: CoreExpr -> Integer
getLitInt (Lit il) = litValue il
getLitInt _ = error "getLitInt"

{-
-- | labR0 :: forall s {t}. s -> t -> R0 (R '[ s := t])
--   labR0 = /\ s t. \ l v. ()
labR0Core :: CoreM CoreExpr
labR0Core = return $ mkCoreLams bnds body
  where
    mkName :: Int -> String -> Name
    mkName i n = mkInternalName (mkLocalUnique i) (mkOccName tcName n) noSrcSpan

    -- ltyn :: Name
    -- ltyn = mkName 500 "labelty"

    -- ltyvar:: TyVar
    -- ltyvar = mkTyVar ltyn liftedTypeKind

    -- labelTy :: Type
    -- labelTy = (mkTyVarTy ltyvar)


    ln :: Name
    ln = mkName 501 "label"
    -- x :: a
    label :: Id
    label = mkLocalId ln manyDataConTy liftedTypeKind


    -- vn :: Name = mkName 502 "value"

    value :: CoreExpr = Lit $ mkLitString "value"
    -- label = Lit $ mkLitString "label"
    -- labelName = Lit $ mkLitString "labelName"

    -- valueTy = Lit $ mkLitString "valueTy"
    -- value   = Lit $ mkLitString "value"

    bnds = [ label      -- s
           -- , valueTy    -- t
           -- , labelName  -- l :: s
           -- , value      -- v :: t
           ]
    body = mkBigCoreTup [ Lit $ mkLitInt8 1 -- single tuple
                        , Var label
                        , value
                        ]

-}

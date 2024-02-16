module RoHs.Plugin.Semantics where

import GHC.Plugins
import GHC.Types.Unique

import qualified GHC.TcPlugin.API as API


type PrimMap = [(FastString, (Type -> CoreM CoreExpr))]

primMap :: PrimMap
primMap = [ (fsLit "labR0" , mkIdCore)
          , (fsLit "unlabR0", mkIdCore)
          , (fsLit "prj0", mkIdCore)
          , (fsLit "cat0", mkIdCore)


          , (fsLit "labV0", mkIdCore)
          , (fsLit "brn0", mkIdCore)
          , (fsLit "unlabV0", mkIdCore)
          , (fsLit "inj0", mkIdCore)
          , (fsLit "ana0", mkIdCore)
          , (fsLit "anaE0", mkIdCore)
          , (fsLit "anaA0", mkIdCore)

          ]

mkCoercion :: Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "RoHs.Plugin.Core"


mkIdCore :: Type -> CoreM CoreExpr
mkIdCore otype = return $ Cast (mkCoreLams [a, x] (Var x)) co
  where
    mkName :: Int -> String -> Name
    mkName i n = mkInternalName (mkLocalUnique i) (mkOccName tcName n) noSrcSpan

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

    co :: Coercion
    co = mkCoercion Representational idTy otype





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

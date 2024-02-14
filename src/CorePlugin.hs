{-# LANGUAGE RecordWildCards #-}
module CorePlugin (install) where

import GHC.Plugins

import GHC.Types.Unique

import GHC.Utils.Monad

import qualified GHC.TcPlugin.API as API

import Data.List as List

-- TODO: Why is this core plugin being called twice?



{-
The plugin portion that gives real meanings to undefined terms.

It makes a traveral over the generated compiler core and replaces
each primitive mentioned in the `primMap` with the actual core expression.

Optionally: Runs the simplifier after the replacement
to see if any simplifications can be made to the core term structure
to have efficient (space and time) during the runtime phase.

-}

type PrimMap = [(FastString, (Type -> CoreM CoreExpr))]

primMap :: PrimMap
primMap = [ (fsLit "labR0" , mkIdCore)
          ]
mkCoercion :: Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "Proven by RoHs.CorePlugin"


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

data RoHsPluginOptions = RoHsPluginOptions {debugMode :: Bool}

-- | The entry point for the core plugin.
--   shamelessly copied from AsyncRattus.Plugin.hs
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todo = case find findSamePass todo of       -- check that we don't run the transformation twice
                      Nothing -> return (strPass : todo) -- (e.g. if the "-fplugin" option is used twice)
                      _ -> return todo
    where name = "RoHs Semantics Plugin"
          strPass = CoreDoPluginPass name (insertRoHsSemantics RoHsPluginOptions{debugMode = dmode})
          dmode = "debug" `elem` opts
          findSamePass (CoreDoPluginPass s _) = s == name
          findSamePass _ = False



-- | All the RoHs primities need to be transformed into the actual semantics
--   eg. RoHsPrimitives.labR0 should do the dictonary manipulation to create/simulate
--   a singleton row
--   Theoritically, the safety-ness criteria comes from the GHC Typechecker and TcPlugin
--   The implementation correctness is well: ¯\_(ツ)_/¯
insertRoHsSemantics :: RoHsPluginOptions -> ModGuts -> CoreM ModGuts
insertRoHsSemantics _ mgs@ModGuts{..} = do {putMsg (text "Hello from" <+> (ppr $ moduleName mg_module))
                               ; mg_binds' <- mapM (tx primMap) mg_binds
                               ; return $ mgs{mg_binds = mg_binds'}}


class Transform x where
  tx :: PrimMap -> x -> CoreM x


instance Transform CoreProgram where
  tx pm x = do { putMsgS "--CorePlugin: transforming binds--"
               ; mapM (tx pm) x --
               }

instance Transform CoreBind where
  tx pm (NonRec var expr) = NonRec var <$> tx pm expr
  tx pm (Rec bnds)        = Rec <$> mapSndM (tx pm) bnds

instance Transform CoreExpr where
  tx pm (Var i) = case List.lookup (getOccFS i) pm of
                    Nothing -> return $ Var i
                    Just e -> e (idType i)
  tx pm (Lam arg body) = Lam arg <$> tx pm body
  tx pm (App e1 e2)    = liftA2 App (tx pm e1) (tx pm e2)

  tx _ x              = return x

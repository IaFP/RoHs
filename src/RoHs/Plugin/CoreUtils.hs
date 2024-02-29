module RoHs.Plugin.CoreUtils where

import GHC.Plugins
import qualified GHC.TcPlugin.API as API

-- | Helper functions for generating Core, as GHCi API may not give us the right abstractions
mkCoercion :: Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "RoHs.Plugin.Core"

mkCastCo :: Type -> Type -> Coercion
mkCastCo iTy oTy = mkCoercion Representational iTy oTy

mkName :: Unique -> String -> Name
mkName u n = mkInternalName u (mkOccName tcName n) noSrcSpan

mkCoreInt :: Int -> CoreExpr
mkCoreInt i = mkCoreConApps intDataCon [Lit (LitNumber LitNumInt (fromIntegral i))]

getLitInt :: CoreExpr -> Integer
getLitInt (Lit il) = litValue il
getLitInt _ = error "getLitInt"

repackageArg :: Type -> Type -> Type
repackageArg repTy ty | ([_], rty) <- splitFunTys ty
                      = mkFunTy (visArg TypeLike) manyDataConTy repTy rty
                      | otherwise = error "repackageArg"


findId :: ModGuts -> String -> CoreM Id
-- the ModuleGuts are of the module that is being core processed.
findId mgs n = do this_mod <- getModule
                  let binds = mg_binds mgs
                      nrs  = [ nr | nr@(NonRec var _) <- binds , n == getOccString var  ]
                  -- debugTraceMsg (text "findId " <+> vcat [text n,  ppr nrs])
                  case nrs of
                    (NonRec var _):_ -> return var
                    _ ->  pprPanic "findId" (text "couldn't find" <+> vcat [text n,  ppr nrs] <+> text "in" <+> ppr this_mod)


anyType :: Type
anyType = anyTypeOfKind liftedTypeKind


-- Exposing this definition from GHC.Core.Make...
mkCoreBoxedTuple :: [CoreExpr] -> CoreExpr
mkCoreBoxedTuple cs = mkCoreConApps (tupleDataCon API.Boxed (length cs))
                      (map (Type . exprType) cs ++ cs)

type PrimMap = [(FastString, (RoHsPluginOptions, ModGuts, Type) -> CoreM CoreExpr)]
data RoHsPluginOptions = RoHsPluginOptions {debugMode :: Bool}

whenDebugM :: Monad m => RoHsPluginOptions -> m () -> m ()
whenDebugM opts thing_inside = if (debugMode opts) then thing_inside else return ()

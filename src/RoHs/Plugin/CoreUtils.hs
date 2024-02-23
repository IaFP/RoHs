module RoHs.Plugin.CoreUtils where

import GHC.Plugins
import GHC.Core
import GHC.Builtin.Types
import GHC.Types.Unique

import qualified GHC.TcPlugin.API as API

-- | Helper functions for generating Core, as GHCi API may not give us the right abstractions

mkCoercion :: Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "RoHs.Plugin.Core"

mkCastCo :: Type -> Type -> Coercion
mkCastCo iTy oTy = mkCoercion Representational iTy oTy

mkName :: Int -> String -> Name
mkName i n = mkInternalName (mkLocalUnique i) (mkOccName tcName n) noSrcSpan

mkCoreInt :: Int -> CoreExpr
mkCoreInt i = mkCoreConApps intDataCon [Lit (LitNumber LitNumInt (fromIntegral i))]

getLitInt :: CoreExpr -> Integer
getLitInt (Lit il) = litValue il
getLitInt _ = error "getLitInt"

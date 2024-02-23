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


anyType :: Type
anyType = anyTypeOfKind liftedTypeKind

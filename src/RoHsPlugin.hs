-- Heavily Influenced by ghc-tcplugin-api example
-- https://github.com/sheaf/ghc-tcplugin-api/blob/main/examples/RewriterPlugin/plugin/RewriterPlugin.hs
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
module RoHsPlugin (plugin) where

import qualified GHC.Plugins as GHC (Plugin(..), defaultPlugin, purePlugin)
import GHC.Utils.Outputable

-- ghc-tcplugin-api
import qualified GHC.TcPlugin.API as API
import GHC.Builtin.Types (listTyCon, mkPromotedListTy)
import GHC.TcPlugin.API ( TcPluginErrorMessage(..) )

-- TODOs: The plugin should enable replacing class Common.Plus with Common.(~+~)

-- The point of this exercise it to show that the GHCs injective type families (implementation, the very least)
-- not as expressive as it should be.API
-- `Plus x y z` also has an associated evidence that says how z is formed using x and y
-- If we use x ~+~ y, then we are potentially losing that information. (but do we really need it)

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = \ _args -> Just $ API.mkTcPlugin tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    }
tcPlugin :: API.TcPlugin
tcPlugin =
  API.TcPlugin
    { API.tcPluginInit    = tcPluginInit
    , API.tcPluginSolve   = tcPluginSolve
    , API.tcPluginRewrite = tcPluginRewrite
    , API.tcPluginStop    = tcPluginStop
    }

-- Definitions used by the plugin.
data PluginDefs =
  PluginDefs
    { rowPlusTyCon     :: !API.TyCon -- standin for ~+~
    , rowLeqClass      :: !API.Class -- standin for ~<~
    , rowTyCon         :: !API.TyCon -- standin for Row
    , rTyCon           :: !API.TyCon -- standin for R
    , rowAssoc         :: !API.TyCon -- standin for :=
    , rowAssocTy       :: !API.TyCon -- standin for Assoc
    }


findCommonModule :: API.MonadTcPlugin m => m API.Module
findCommonModule = do
  let modlName = API.mkModuleName "Common"
  pkgQual    <- API.resolveImport      modlName Nothing
  findResult <- API.findImportedModule modlName pkgQual
  case findResult of
    API.Found _ res     -> pure res
    API.FoundMultiple _ -> error $ "RoHs.Plugin: found multiple modules named RoHs.Common in the current package."
    _                   -> error $ "RoHs.Plugin: could not find any module named RoHs.Common in the current package."


tcPluginInit :: API.TcPluginM API.Init PluginDefs
tcPluginInit = do
  API.tcPluginTrace "--Plugin Init--" empty
  commonModule   <- findCommonModule
  rowPlusTyCon   <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "~+~")
  rowLeqClass    <- API.tcLookupClass =<< API.lookupOrig commonModule (API.mkClsOcc "~<~")
  rowTyCon       <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "Row")
  rTyCon         <- fmap API.promoteDataCon . API.tcLookupDataCon =<< API.lookupOrig commonModule (API.mkDataOcc "R")
  rowAssoc       <- fmap API.promoteDataCon . API.tcLookupDataCon =<< API.lookupOrig commonModule (API.mkDataOcc ":=")
  rowAssocTy     <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "Assoc")
  pure (PluginDefs { rowPlusTyCon
                   , rowLeqClass
                   , rowTyCon
                   , rTyCon
                   , rowAssoc
                   , rowAssocTy
                   })

-- The entry point for constraint solving
tcPluginSolve :: PluginDefs -> [ API.Ct ] -> [ API.Ct ] -> API.TcPluginM API.Solve API.TcPluginSolveResult
tcPluginSolve _ givens [] = do -- simplify given constraints
  API.tcPluginTrace "--Plugin Solve Simplify--" (ppr givens)
  pure $ API.TcPluginOk [] []
tcPluginSolve _ givens wanteds = do
  API.tcPluginTrace "--Plugin Solve--" (ppr givens $$ ppr wanteds)
  pure $ API.TcPluginOk [] []

-- Nothing to shutdown.
tcPluginStop :: PluginDefs -> API.TcPluginM API.Stop ()
tcPluginStop _ = do
  API.tcPluginTrace "--Plugin Stop--" empty
  pure ()

-- We have to possibly rewrite ~+~ type family applications
tcPluginRewrite :: PluginDefs -> API.UniqFM API.TyCon API.TcPluginRewriter
tcPluginRewrite defs@(PluginDefs {rowPlusTyCon}) = API.listToUFM [(rowPlusTyCon, rewrite_rowplus defs)]

rewrite_rowplus :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
rewrite_rowplus pdefs@(PluginDefs { .. }) _givens tys
  | [k, a, b] <- tys
  = if
      | Just (_ , [_, arg_a]) <- API.splitTyConApp_maybe a
      , Just (_ , [_, arg_b]) <- API.splitTyConApp_maybe b
      , Just (_, assocs_a) <- API.splitTyConApp_maybe arg_a
      , Just (_, assocs_b) <- API.splitTyConApp_maybe arg_b
      , let args = (init $ tail assocs_a) ++ (init $ tail assocs_b)
            rowAssocKi = head assocs_a
      -> do API.tcPluginTrace "--Plugin RowConcatRewrite--" (vcat [ text "args_a:" <+> ppr assocs_a
                                                                  , text "args_b:" <+> ppr assocs_b
                                                                  , text "args:"   <+> ppr args
                                                                  ]
                                                            )
            pure $ API.TcPluginRewriteTo
                           (API.mkTyFamAppReduction "RoHsPlugin" API.Representational rowPlusTyCon [k, a, b]
                               (API.mkTyConApp rTyCon [k, mkPromotedListTy rowAssocKi (args)]))
                           []
            -- pure API.TcPluginNoRewrite
      | otherwise
      -> pure API.TcPluginNoRewrite
  | otherwise
  = do API.tcPluginTrace "other tyfam" (ppr tys)
       pure API.TcPluginNoRewrite


-- rewriteWanteds :: [API.Ct] -> [(API.EvTerm, API.Ct)]
-- rewriteWanteds = fmap mb_rewriteCt

-- maybe rewrite cosntraint. if you see a ~+~ constraint, rewrite it to its canonical form
-- else return it as is
-- mb_rewriteCt :: API.Ct -> Maybe (API.EvTerm,  API.Ct)
-- mb_rewriteCt ct = (API.mkPluginUnivCo "RoHsAssertsOk" API.Representational () (), ct)


-- Return the given type family reduction, while emitting an additional type error with the given message.
-- throwTypeError :: API.Reduction -> API.TcPluginErrorMessage -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
-- throwTypeError badRedn msg = do
--   env <- API.askRewriteEnv
--   errorTy <- API.mkTcPluginErrorTy msg
--   let
--     errorCtLoc :: API.CtLoc
--     errorCtLoc = API.bumpCtLocDepth $ API.rewriteEnvCtLoc env
--   errorCtEv <- API.setCtLocM errorCtLoc $ API.newWanted errorCtLoc errorTy
--   pure $ API.TcPluginRewriteTo badRedn [ API.mkNonCanonical errorCtEv ]

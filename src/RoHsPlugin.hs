-- Heavily Influenced by ghc-tcplugin-api example
-- https://github.com/sheaf/ghc-tcplugin-api/blob/main/examples/RewriterPlugin/plugin/RewriterPlugin.hs
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
module RoHsPlugin (plugin) where

import qualified GHC.Plugins as GHC (Plugin(..), defaultPlugin, purePlugin, mkLocalId)
import GHC.Utils.Outputable

-- ghc-tcplugin-api
import qualified GHC.TcPlugin.API as API
import GHC.Core.TyCo.Rep
-- import GHC.TcPlugin.API ( TcPluginErrorMessage(..) )
import GHC.Core
import GHC.Core.Make
import GHC.Core.Type

import Data.List (sortBy)
import Data.Foldable (foldlM)

import GHC.Types.Name      ( mkInternalName, tcName )
import GHC.Types.Name.Occurrence   ( mkOccName )
import GHC.Types.Unique
import GHC.Types.SrcLoc
import GHC.Builtin.Types

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
    { rowPlusTF        :: !API.TyCon -- standin for ~+~
    , allTF            :: !API.TyCon -- standin for All
    , rowTyCon         :: !API.TyCon -- standin for Row
    , rTyCon           :: !API.TyCon -- standin for R
    , rowAssoc         :: !API.TyCon -- standin for :=
    , rowAssocTy       :: !API.TyCon -- standin for Assoc

    , rowLeqCls        :: !API.Class -- standin for ~<~
    , rowPlusCls       :: !API.Class -- standin for Plus
    , functorCls       :: !API.Class -- standin for Functor
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



findPreludeModule :: API.MonadTcPlugin m => m API.Module
findPreludeModule = do
  let modlName = API.mkModuleName "GHC.Base"
  let pkgName = Just $ API.fsLit "base"
  pkgQual    <- API.resolveImport      modlName pkgName
  findResult <- API.findImportedModule modlName pkgQual
  case findResult of
    API.Found _ res     -> pure res
    API.FoundMultiple _ -> error $ "RoHs.Plugin: found multiple modules named GHC.Base in the current package."
    _                   -> error $ "RoHs.Plugin: could not find any module named GHC.Base in the current package."


tcPluginInit :: API.TcPluginM API.Init PluginDefs
tcPluginInit = do
  API.tcPluginTrace "--Plugin Init--" empty
  commonModule   <- findCommonModule
  preludeModule  <- findPreludeModule

  rowPlusTF      <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "~+~")
  allTF          <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "All")
  rowTyCon       <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "Row")
  rTyCon         <- fmap API.promoteDataCon . API.tcLookupDataCon =<< API.lookupOrig commonModule (API.mkDataOcc "R")
  rowAssoc       <- fmap API.promoteDataCon . API.tcLookupDataCon =<< API.lookupOrig commonModule (API.mkDataOcc ":=")
  rowLeqCls      <- API.tcLookupClass =<< API.lookupOrig commonModule (API.mkClsOcc "~<~")
  rowAssocTy     <- API.tcLookupTyCon =<< API.lookupOrig commonModule (API.mkTcOcc "Assoc")
  rowPlusCls     <- API.tcLookupClass =<< API.lookupOrig commonModule (API.mkClsOcc "Plus")
  functorCls     <- API.tcLookupClass =<< API.lookupOrig preludeModule (API.mkClsOcc "Functor")

  pure (PluginDefs { rowPlusTF = rowPlusTF
                   , allTF = allTF
                   , rowTyCon = rowTyCon
                   , rTyCon = rTyCon
                   , rowAssoc = rowAssoc
                   , rowAssocTy = rowAssocTy
                   , rowPlusCls = rowPlusCls
                   , rowLeqCls = rowLeqCls
                   , functorCls = functorCls
                   })

-- The entry point for constraint solving
tcPluginSolve :: PluginDefs -> [ API.Ct ] -> [ API.Ct ] -> API.TcPluginM API.Solve API.TcPluginSolveResult
tcPluginSolve _ givens [] = do -- simplify given constraints
  API.tcPluginTrace "--Plugin Solve Simplify--" (ppr givens)
  pure $ API.TcPluginOk [] []
tcPluginSolve defs givens wanteds = do
  API.tcPluginTrace "--Plugin Solve--" (ppr givens $$ ppr wanteds)
  (solved, new_wanteds) <- foldlM (try_solving defs) ([], [])  wanteds
  pure $ API.TcPluginOk solved new_wanteds


-- | Try solving a given constraint
--   What should be the strategy look like? Here's what i'm going to try and implement
--   0. Get all the trivial constraints out of the way by using solve_trivial
--   1. Do a collective improvement where we use the set of givens and set of wanteds
--   2. if we have made some progress go to step 0
try_solving :: PluginDefs -> ([(API.EvTerm, API.Ct)], [API.Ct]) -> API.Ct -> API.TcPluginM API.Solve ([(API.EvTerm, API.Ct)], [API.Ct])
try_solving defs acc ct = do solve_trivial defs acc ct


-- | Solves simple wanteds.
--   By simple I mean the ones that do not give rise to new wanted constraints
--   They are the base cases of the proof generation, if you will
--   Solving for things like: 1. Plus (x := t) (y := u) ((x := t) ~+~ (y := u)) etc
--                            2. x ~<~ x
--                            3. (x := t) ~<~ [x := t , y := u]
solve_trivial :: PluginDefs -> ([(API.EvTerm, API.Ct)], [API.Ct]) -> API.Ct -> API.TcPluginM API.Solve ([(API.EvTerm, API.Ct)], [API.Ct])
solve_trivial PluginDefs{..} acc ct
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y, z])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowPlusCls
  , Just x_s@(_r_tycon1, [_, assocs_x])<- API.splitTyConApp_maybe x
  , Just y_s@(_r_tycon2, [_, assocs_y])<- API.splitTyConApp_maybe y
  , Just z_s@(_r_tycon3, [_, assocs_z])<- API.splitTyConApp_maybe z
  , let xs = sortAssocs $ fold_list_type_elems assocs_x
  , let ys = sortAssocs $ fold_list_type_elems assocs_y
  , let zs = sortAssocs $ fold_list_type_elems assocs_z
  , let args = sortAssocs $ xs ++ ys
  = if (length args == length zs)
           && all (\(l, r) -> API.eqType l r) (zip args (init zs))
    then do { API.tcPluginTrace "--Plugin solving Plus construct evidence--" (vcat [ ppr clsCon
                                                                                 , ppr x_s, ppr xs
                                                                                 , ppr y_s, ppr ys
                                                                                 , ppr z_s, ppr zs ])
            ; return ([(mkIdFunEvTerm predTy, ct)], []) }
    else do { API.tcPluginTrace "--Plugin solving Plus throw error--"  (vcat [ ppr clsCon
                                                                                 , ppr x_s, ppr xs
                                                                                 , ppr y_s, ppr ys
                                                                                 , ppr z_s, ppr zs ])
            ; return acc } -- no need to actually throw error.
                           -- it might fail down the tc pipleline anyway witha good error message
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , API.eqType x y -- if x ~<~ x definitely holds
  = do { API.tcPluginTrace "--Plugin solving Plus construct evidence--" (vcat [ ppr clsCon
                                                                              , ppr x , ppr y ])
       ; return ([(mkIdFunEvTerm predTy, ct)], []) }

  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , Just x_s@(_r_tycon1, [_, assocs_x])<- API.splitTyConApp_maybe x
  , Just y_s@(_r_tycon2, [_, assocs_y])<- API.splitTyConApp_maybe y
  , let xs = sortAssocs $ fold_list_type_elems assocs_x
  , let ys = sortAssocs $ fold_list_type_elems assocs_y
  = if (checkMembership xs ys)
    then do { API.tcPluginTrace "--Plugin solving Plus construct evidence--" (vcat [ ppr clsCon
                                                         , ppr x_s, ppr xs
                                                         , ppr y_s, ppr ys ])
            ; return ([(mkIdFunEvTerm predTy, ct)], []) }
    else do { API.tcPluginTrace "--Plugin solving Plus throw error--"  (vcat [ ppr clsCon
                                                         , ppr x_s, ppr xs
                                                         , ppr y_s, ppr ys])
            ; return acc } -- no need to actually throw error here
                           -- it might fail down the tc pipleline anyway with a good error message


  -- TODO | Each ?? is trivially solvable?
  | otherwise = return acc


checkMembership :: [Type] -> [Type] -> Bool
checkMembership [] _         =  True
checkMembership _  []        =  False
checkMembership (x:xs) (y:ys)=  (x `eqAssoc` y == EQ) && checkMembership xs ys

-- Some constraint solving just results to having identity functions as evidence
mkIdFunEvTerm :: Type -> API.EvTerm
mkIdFunEvTerm predTy = API.evCast (mkCoreLams [a, x] (Var x)) co
  where
    mkName :: Int -> String -> API.Name
    mkName i n = mkInternalName (mkLocalUnique i) (mkOccName tcName n) noSrcSpan

    xn :: API.Name
    xn = mkName 0 "x"


    an :: API.Name
    an = mkName 1 "a"

    a :: API.TyVar
    a = API.mkTyVar an liftedTypeKind

    -- x :: a
    x :: API.Id
    x = GHC.mkLocalId xn manyDataConTy (TyVarTy a)

    -- \forall a. a -> a
    idTy :: Type
    idTy = mkForAllTy (mkForAllTyBinder Inferred a) $ mkVisFunTy manyDataConTy (TyVarTy a) (TyVarTy a)

    co :: Coercion
    co = mkCoercion API.Representational idTy predTy

mkCoercion :: API.Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "Proven by Le RoHsPlugin"

-- If you get a list of assocs, flatten it out
fold_list_type_elems :: API.TcType -> [API.TcType]
fold_list_type_elems =  go []
  where
    go :: [API.TcType] -> API.TcType -> [API.TcType]
    go acc ty | Nothing <- API.splitTyConApp_maybe ty
              = acc
              | Just (_, [_, assoc]) <- API.splitTyConApp_maybe ty
              = assoc : acc
              | Just (_, [_, assoc, rest]) <- API.splitTyConApp_maybe ty
              = go (assoc : acc) rest
              | otherwise
              = acc

-- Nothing to shutdown.
tcPluginStop :: PluginDefs -> API.TcPluginM API.Stop ()
tcPluginStop _ = do
  API.tcPluginTrace "--Plugin Stop--" empty
  pure ()

-- We have to possibly rewrite ~+~ type family applications
tcPluginRewrite :: PluginDefs -> API.UniqFM API.TyCon API.TcPluginRewriter
tcPluginRewrite defs@(PluginDefs {rowPlusTF, allTF}) = API.listToUFM [ (rowPlusTF, rewrite_rowplus defs)
                                                                   -- , (rTyCon, intercept_tyfam defs)
                                                                     , (allTF, rewrite_allTF defs)
                                                                     ]

-- | Template interceptor for a type family tycon
-- intercept_tyfam :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
-- intercept_tyfam (PluginDefs { .. }) givens tys
--   = do API.tcPluginTrace "--Plugin RowConcatRewrite TF--" (vcat [ ppr givens $$ ppr tys ])
--        pure API.TcPluginNoRewrite


-- | Constraints like All Functor (R [x := t]) should reduce to () as they are trivially satisfiable
rewrite_allTF :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
rewrite_allTF (PluginDefs { .. }) givens tys
  | [_, clsTyCon, r] <- tys
  , API.eqType clsTyCon (mkNakedTyConTy $ API.classTyCon functorCls)
  , Just (rtc_mb, _) <- API.splitTyConApp_maybe r
  , rtc_mb == rTyCon
  -- TODO: and possibly check if the assocs are well formed?
  = do API.tcPluginTrace "--Plugin All TF unit constraint--" (vcat [ ppr allTF, ppr tys, ppr givens ])
       -- return a unit constraint?
       pure $ API.TcPluginRewriteTo
                           (API.mkTyFamAppReduction "RoHsPlugin" API.Nominal allTF tys
                               (mkConstraintTupleTy []))
                           []
  | otherwise
  = do API.tcPluginTrace "--Plugin All TF--" (vcat [ ppr allTF, ppr tys, ppr givens ])
       pure API.TcPluginNoRewrite

-- | Reduce (x := t) ~+~ (y := u) to [x := t, y := u]
--   The label occurance in the list is lexicographic.
rewrite_rowplus :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
rewrite_rowplus (PluginDefs { .. }) _givens tys
  | [k, a, b] <- tys
  = if
      | Just (_ , [_, arg_a]) <- API.splitTyConApp_maybe a
      , Just (_ , [_, arg_b]) <- API.splitTyConApp_maybe b
      , assocs_a <- fold_list_type_elems arg_a
      , assocs_b <- fold_list_type_elems arg_b
      , let concat_assocs = sortAssocs $ assocs_a ++ assocs_b
            rowAssocKi = head assocs_a
      -> do API.tcPluginTrace "--Plugin RowConcatRewrite (~+~)--" (vcat [ text "args_a:" <+> ppr assocs_a
                                                                  , text "args_b:" <+> ppr assocs_b
                                                                  , text "args:"   <+> ppr concat_assocs
                                                                  , text "givens:" <+> ppr _givens
                                                                  ]
                                                            )
            pure $ API.TcPluginRewriteTo
                           (API.mkTyFamAppReduction "RoHsPlugin" API.Nominal rowPlusTF tys
                               (API.mkTyConApp rTyCon [k, mkPromotedListTy rowAssocKi concat_assocs]))
                           []
      | otherwise
      -> pure API.TcPluginNoRewrite
  | otherwise
  = do API.tcPluginTrace "other tyfam" (ppr tys)
       pure API.TcPluginNoRewrite

-- At this point i'm just sorting on the kind of the type which happens to be a string literal, Sigh ...
cmpAssoc :: API.TcType -> API.TcType -> Ordering
cmpAssoc lty rty | Just (_, [_, LitTy lbl_l, _]) <- API.splitTyConApp_maybe lty
                 , Just (_, [_, LitTy lbl_r, _]) <- API.splitTyConApp_maybe rty
                 = cmpTyLit lbl_l lbl_r
cmpAssoc _ _ = EQ

-- make GHC Type checker go brrr
eqAssoc :: API.TcType -> API.TcType -> Ordering
eqAssoc lty rty | Just (_, [_, LitTy lbl_l, _]) <- API.splitTyConApp_maybe lty
                , Just (_, [_, LitTy lbl_r, _]) <- API.splitTyConApp_maybe rty
                = cmpTyLit lbl_l lbl_r
eqAssoc _ _ = GT

-- This is the "cannonical/principal" type representation of a row type
sortAssocs :: [API.TcType] -> [API.TcType]
sortAssocs = sortBy cmpAssoc


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

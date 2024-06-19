-- Heavily Influenced by ghc-tcplugin-api example
-- https://github.com/sheaf/ghc-tcplugin-api/blob/main/examples/RewriterPlugin/plugin/RewriterPlugin.hs
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module RoHs.Plugin.TC (tcPlugin) where

import GHC.Utils.Outputable hiding ((<>))

-- ghc-tcplugin-api
import qualified GHC.TcPlugin.API as API
import GHC.TcPlugin.API (TcPluginErrorMessage(..))

import GHC.Builtin.Types

import GHC.Core
import GHC.Core.Make
import GHC.Core.Predicate
import GHC.Core.Type
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon

import RoHs.Plugin.CoreUtils hiding (mkCoercion)
import qualified GHC.Tc.Types.Constraint as API


import Control.Monad (mplus)
import Data.List (findIndex, sortBy)
import Data.Foldable (foldlM)
import Data.Maybe

-- The point of this exercise it to show that the GHCs injective type families (implementation, the very least)
-- not as expressive as it should be
-- `Plus x y z` also has an associated evidence that says how z is formed using x and y
-- If we use x ~+~ y, then we are potentially losing that information. (but do we really need it? -- Yes.)

tcPlugin :: API.TcPlugin
tcPlugin =
  API.TcPlugin
    { API.tcPluginInit    = tcPluginInit
    , API.tcPluginSolve   = tcPluginSolve
    , API.tcPluginRewrite = tcPluginRewrite
    , API.tcPluginStop    = tcPluginStop
    }


-- | PluginWork is a 2-tuple.
type PluginWork = ( [(API.EvTerm, API.Ct)]      -- solved things
                  , [API.Ct]                    -- new wanteds
                  , [API.Ct]                    -- Insoluble constraints which should throw an type error
                  )

-- Definitions used by the plugin.
data PluginDefs =
  PluginDefs
    { rowPlusTF        :: !API.TyCon -- standin for ~+~
    , rowTyCon         :: !API.TyCon -- standin for Row
    , rTF              :: !API.TyCon -- standin for R
    , rowAssoc         :: !API.TyCon -- standin for :=
    , rowAssocTyCon    :: !API.TyCon -- standin for Assoc
    , v1TyCon          :: !API.TyCon -- standin for V1
    , v0TyCon          :: !API.TyCon -- standin for V0

    , rowLeqCls        :: !API.Class -- standin for ~<~
    , rowPlusCls       :: !API.Class -- standin for Plus
    , allCls           :: !API.Class -- standin for All

    , composeId        :: !API.Id    -- standin for compose function
    }


findModule :: API.MonadTcPlugin m => String -> Maybe String -> m API.Module
findModule moduleName pkgName_mb = do
  let modlName = API.mkModuleName moduleName
  pkgQual    <- API.resolveImport      modlName (API.fsLit <$> pkgName_mb)
  findResult <- API.findImportedModule modlName pkgQual
  case findResult of
    API.Found _ res     -> pure res
    API.FoundMultiple _ -> error $ "RoHs.Plugin: found multiple modules named "
                                   ++ errorSuffix
    _                   -> error $ "RoHs.Plugin: found no modules named "
                                   ++ errorSuffix

  where
    errorSuffix = moduleName ++ " in the " ++ (mkPkgName pkgName_mb) ++ " package."

    mkPkgName Nothing = "current"
    mkPkgName (Just s) = s



findTypesModule :: API.MonadTcPlugin m => m API.Module
findTypesModule = findModule "RoHs.Language.Types" Nothing

tcPluginInit :: API.TcPluginM API.Init PluginDefs
tcPluginInit = do
  API.tcPluginTrace "--Plugin Init--" empty
  typesModule    <- findTypesModule

  rowPlusTF      <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "~+~")
  rTF            <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "R")
  rowTyCon       <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "Row")
  rowAssoc       <- fmap API.promoteDataCon . API.tcLookupDataCon =<< API.lookupOrig typesModule (API.mkDataOcc ":=")
  rowAssocTyCon  <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "Assoc")
  v1TyCon        <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "V1")
  v0TyCon        <- API.tcLookupTyCon =<< API.lookupOrig typesModule (API.mkTcOcc "V0")

  rowLeqCls      <- API.tcLookupClass =<< API.lookupOrig typesModule (API.mkClsOcc "~<~")
  rowPlusCls     <- API.tcLookupClass =<< API.lookupOrig typesModule (API.mkClsOcc "Plus")
  allCls         <- API.tcLookupClass =<< API.lookupOrig typesModule (API.mkClsOcc "All")

  composeId      <- API.tcLookupId =<< API.lookupOrig typesModule (API.mkVarOcc "compose")


  pure (PluginDefs { rowPlusTF     = rowPlusTF
                   , rowTyCon      = rowTyCon
                   , rTF           = rTF
                   , rowAssoc      = rowAssoc
                   , rowAssocTyCon = rowAssocTyCon
                   , v1TyCon       = v1TyCon
                   , v0TyCon       = v0TyCon

                   , rowPlusCls    = rowPlusCls
                   , rowLeqCls     = rowLeqCls
                   , allCls        = allCls

                   , composeId     = composeId
                   })

-- The entry point for constraint solving
tcPluginSolve :: PluginDefs -> [ API.Ct ] -> [ API.Ct ] -> API.TcPluginM API.Solve API.TcPluginSolveResult
tcPluginSolve _ [] [] = do -- simplify given constraints, we don't have to worry about it yet
  pure $ API.TcPluginOk [] []
tcPluginSolve defs givens wanteds = do
  API.tcPluginTrace "--tcPluginSolveStart--" (ppr givens $$ ppr wanteds)
  (solved, ws, insolubles) <- main_solver defs givens wanteds
  API.tcPluginTrace "--tcPluginSolveEnd--" (vcat [ ppr wanteds
                                              , text "------solved---------"
                                              , ppr solved
                                              , text "----new_wanted--------"
                                              , ppr ws
                                              , text "-----insolubles----------"
                                              , ppr insolubles
                                              ])
  if not (null insolubles)
  then return $ API.TcPluginContradiction insolubles
  else return $ API.TcPluginOk solved ws

main_solver :: PluginDefs -> [API.Ct] -> [API.Ct] -> API.TcPluginM API.Solve PluginWork
main_solver defs givens wanteds = try_solving defs ([], [], []) givens wanteds -- we don't use givens as of now.

-- | Try solving a given constraint
--   What should be the strategy look like? Here's what i'm going to try and implement
--       0. Get all the trivial constraints out of the way by using solve_trivial
--       1. Do a collective improvement where we use the set of givens and set of wanteds
--       2. if we have made some progress go to step 0
try_solving :: PluginDefs -> PluginWork -> [API.Ct] -> [API.Ct] -> API.TcPluginM API.Solve PluginWork
try_solving defs acc@(solved, unsolveds, _) givens wanteds =
  do acc'@(solved', new_wanteds, insol') <- foldlM (solve_trivial defs givens) acc wanteds
     API.tcPluginTrace "--Plugin Solve Improvements--" (vcat [ ppr unsolveds, ppr new_wanteds, ppr insol' ])
     if any (isEqPrimPred . API.ctPred) new_wanteds
       then return $ acc <> acc'
       else if madeProgress solved solved'
            then foldlM (solve_trivial defs givens) acc' unsolveds
            else return $ acc <> ([], [], insol')

        -- we only make progress when we either solve more things
  where madeProgress s s' = length s' > length s

-- | Solves simple wanteds.
--   By simple I mean the ones that do not give rise to new wanted constraints or are "obvous" :)
--   They are the base cases of the proof generation, if you will
--   Solving for things like: 1. Plus (x := t) (y := u) ((x := t) ~+~ (y := u)) etc
--                            2. x ~<~ x
--                            3. (x := t) ~<~ [x := t , y := u]
solve_trivial :: PluginDefs -> [API.Ct] -> PluginWork -> API.Ct -> API.TcPluginM API.Solve PluginWork
solve_trivial PluginDefs{..} givens acc ct
{-
      r1 U r2 = r3    r1 n r2 = 𝝓
  ---------------------------------
    𝚪 |= Plus (R r1) (R r2) (R r3)
-}
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y, z])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowPlusCls
  , Just x_s@(r_tycon1, [_, assocs_x])<- API.splitTyConApp_maybe x
  , Just y_s@(r_tycon2, [_, assocs_y])<- API.splitTyConApp_maybe y
  , Just z_s@(r_tycon3, [_, assocs_z])<- API.splitTyConApp_maybe z
  , r_tycon1 == r_tycon2 && r_tycon2 == r_tycon3 && r_tycon3 == rTF
  , let xs = unfold_list_type_elems assocs_x
  , let ys = unfold_list_type_elems assocs_y
  , let zs = unfold_list_type_elems assocs_z
  , length xs + length ys == length zs
  , let inter = setIntersect xs ys
  , Just ps <- checkConcatEv xs ys zs
  = if null inter
    then
      do { API.tcPluginTrace "--Plugin solving Plus construct evidence for z--"
           (vcat [ ppr clsCon, ppr x_s, ppr xs, ppr y_s, ppr ys, ppr z_s, ppr zs, ppr ps ])
         ; API.tcPluginTrace "Generated evidence" (ppr (mkPlusEvTerm ps predTy))
         ; return $ acc <> ([(mkPlusEvTerm ps predTy, ct)], [], [])
         }
      else do { API.tcPluginTrace "--Plugin overlapping rows--" (ppr ct)
              ; error_predTy <- API.mkTcPluginErrorTy (mkSameLabelError x y inter)
              ; nw_error <- API.newWanted (API.ctLoc ct) error_predTy
              ; return $ acc <> ([], [], [API.mkNonCanonical nw_error])
              }

  -- handles the case such where we have [W] Plus ([x := t]) (y0) ([x := t, y := u])
  -- due to functional dependency we _know_ that y0 is unique we can
  -- then emit that Plus is solvable, and (y0 ~ y := u)
{-
           r2 = r3 \ r1
  ---------------------------------
    𝚪 |= Plus (R r1) (R r2) (R r3)
-}
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y, z])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowPlusCls
  , Just (r_tycon, [k, assocs_x])<- API.splitTyConApp_maybe x
  , Just (_, [_, assocs_z])<- API.splitTyConApp_maybe z
  , let xs = unfold_list_type_elems assocs_x
  , let zs = unfold_list_type_elems assocs_z
  , Just yTVar <- getTyVar_maybe y
  -- y is just a type variable which we will solve for
  , Just _is <- checkSubsetEv xs zs
  , let ys = sortAssocs $ setDiff xs zs
  , let rowAssocKi = mkTyConApp rowAssocTyCon [k]
  , let y0 = API.mkTyConApp r_tycon [k,  mkPromotedListTy rowAssocKi ys]
  , isJust $ checkConcatEv xs ys zs
  = do { API.tcPluginTrace "--Plugin solving improvement for Plus with Eq emit --" (vcat [ ppr predTy ])
       ; API.tcPluginTrace "--Plugin solving Plus construct evidence for y--"
                      (vcat [ ppr clsCon, ppr x, ppr z, ppr y, ppr ys, text "computed" <+> ppr y <+> text "=:=" <+> ppr y0])
       ; new_eq_wanted <- API.newWanted (API.ctLoc ct) $ API.mkPrimEqPredRole API.Nominal (mkTyVarTy yTVar) y0
       ; return $ acc <> ( []
                         , API.mkNonCanonical <$> [new_eq_wanted]
                         , []
                         )
       }
  -- Handles the case where x is unknown but y and z is known
  -- technically this is solvable by swapping x and y from the previous case, but i'm afraid
  -- I'll make the plugin solver go another round and round which would be generating unnecessary extra
  -- constraints.
{-
           r1 = r3 \ r2
  ---------------------------------
    𝚪 |= Plus (R r1) (R r2) (R r3)
-}

  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, y, x, z])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowPlusCls
  , Just (rx_tycon, [k, assocs_x])<- API.splitTyConApp_maybe x
  , Just (rz_tycon, [_, assocs_z])<- API.splitTyConApp_maybe z
  , let xs = unfold_list_type_elems assocs_x
  , let zs = unfold_list_type_elems assocs_z
  , Just yTVar <- getTyVar_maybe y
  , rx_tycon == rz_tycon
  , let r_tycon = rx_tycon
  -- y is just a type variable which we will solve for
  , isJust (checkSubsetEv xs zs)
  , let ys = sortAssocs $ setDiff xs zs
  , isJust $ checkConcatEv xs ys zs
  = do { API.tcPluginTrace "--Plugin solving improvement for Plus with Eq emit --" (vcat [ ppr predTy ])
       ; let
             rowAssocKi = mkTyConApp rowAssocTyCon [k]
             y0 = API.mkTyConApp r_tycon [k,  mkPromotedListTy rowAssocKi ys]
       ; API.tcPluginTrace "--Plugin solving Plus construct evidence for x--"
                      (vcat [ ppr clsCon, ppr x, ppr z, ppr y, ppr ys, text "computed" <+> ppr y <+> text "=:=" <+> ppr y0])
       ; nw <- API.newWanted (API.ctLoc ct) $ API.mkPrimEqPredRole API.Nominal (mkTyVarTy yTVar) y0
       ; return $ acc <> ([]
                         , [API.mkNonCanonical nw]
                         , []
                         )
       }
  -- Handles the case where z is of the form x0 ~+~ y0 in [W] Plus x y (x0 ~+~ y0)
  --
  -- JGM: I am pretty sure we should not be handling this case at all yet.  Suppose that we have:
  --
  --   Plus x y (w ~+~ z)
  --
  -- There are plenty of satisfying ways to instantiate this...for example, w/x,
  -- z/y, or z/x, w/y, or say ["x" := Int, "y" := Bool] for x, ["z" := Float]
  -- for y, ["x" := Int, "z" := Float] for w, and ["y" := Bool] for z.  So,
  -- until further instantiation, I don't think there's anything to do with such
  -- a constraint.
  --
  -- | predTy <- API.ctPred ct
  -- , Just (clsCon, ([_, x, y, z])) <- API.splitTyConApp_maybe predTy
  -- , clsCon == API.classTyCon rowPlusCls
  -- , Just (ztyCon, [_, z1, z2]) <- API.splitTyConApp_maybe z
  -- , ztyCon == rowPlusTF
  -- =  do { API.tcPluginTrace "--Plugin solving Plus and ~+~--" (vcat [ ppr clsCon
  --                                                                   , ppr x, ppr y, ppr z
  --                                                                   , ppr rowPlusTF
  --                                                                   , ppr z1, ppr z2 ])
  --       ; nw1 <- API.newWanted (API.ctLoc ct) (GHC.mkPrimEqPred x z1)
  --       ; nw2 <- API.newWanted (API.ctLoc ct) (GHC.mkPrimEqPred y z2)
  --       ; return $ acc <> ([(mkIdFunEvTerm predTy, ct)]
  --                                       , API.mkNonCanonical <$> [ nw1, nw2 ]
  --                                       , [])
  --       }

  -- Handles the case where z is unknown, but we know x = R '[ .. ] and y = R '[ .. ] in [W] Plus x y z
{-
      r3 = r1 U r2   r1 n r2 = 𝝓
  ---------------------------------
    𝚪 |= Plus (R r1) (R r2) (R r3)
-}

  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y, z])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowPlusCls
  , Just (r_tycon, [kx, assocs_x])<- API.splitTyConApp_maybe x
  , Just (_, [ky, assocs_y])<- API.splitTyConApp_maybe y
  , API.eqType kx ky -- x and y should be of the same row kinds
  , Just zTVar <- getTyVar_maybe z  -- z is a type variable
  , let xs = unfold_list_type_elems assocs_x
  , let ys = unfold_list_type_elems assocs_y
  , let zs = sortAssocs (xs ++ ys)
  , Just ps <- checkConcatEv xs ys zs
  =  do { API.tcPluginTrace "--Plugin solving simple Plus--" (vcat [ ppr clsCon
                                                                    , ppr xs, ppr ys, ppr z
                                                                    ])
        ; let rowAssocKi = mkTyConApp rowAssocTyCon [kx]
              z0 = API.mkTyConApp r_tycon [kx,  mkPromotedListTy rowAssocKi zs]
              inter = setIntersect xs ys
        ; if null inter
          then do { nw <- API.newWanted (API.ctLoc ct) $ API.mkPrimEqPredRole API.Nominal (mkTyVarTy zTVar) z0
                  ; API.tcPluginTrace "Generated evidence" (ppr (mkPlusEvTerm ps predTy))
                  ; API.tcPluginTrace "--Plugin solving Type Eq rule (emit equality)--"
                    (text "computed [w]" <+> ppr zTVar <+> text "=:=" <+> ppr z0)
                  ; return $ acc <> ([]
                                    , [API.mkNonCanonical nw]
                                    , [])
                  }
          else do { API.tcPluginTrace "--Plugin overlapping rows--" (vcat [ppr ct, ppr zs, ppr inter])
                  ; error_predTy <- API.mkTcPluginErrorTy (mkSameLabelError x y inter)
                  ; nw_error <- API.newWanted (API.ctLoc ct) error_predTy
                  ; return $ acc <> ([], [], [API.mkNonCanonical nw_error])
                  }
        }

{-

  ---------------------------------
             𝚪 |= x ~<~ x
-}

  --  Handles the case of x ~<~ x
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , API.eqType x y -- if x ~<~ x definitely holds
  = do { API.tcPluginTrace "--Plugin solving ~<~ construct evidence--" (vcat [ ppr clsCon
                                                                             , ppr x , ppr y ])
       ; return $ acc <> ([(mkReflEvTerm predTy, ct)], [], []) }


{-
                   x ⊆ y
  ---------------------------------
             𝚪 |= R x ~<~ R y
-}

  -- Handles the case of [(x := t)] ~<~ [(x := t), (y := u)]
  -- with the case where y0 ~<~ z0 but we have a substitution which makes it true
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, x, y])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , Just x_s@(_r_tycon1, [kx, assocs_x]) <- API.splitTyConApp_maybe x
  , Just y_s@(_r_tycon2, [ky, assocs_y]) <- API.splitTyConApp_maybe y
  , let xs = unfold_list_type_elems assocs_x
  , let ys = unfold_list_type_elems assocs_y
  , API.eqType kx ky -- we are not having hetrogenous row concat
  , Just is <- checkSubsetEv xs ys
  =  do { API.tcPluginTrace "--Plugin solving ~<~ construct evidence--"
                               (vcat [ ppr clsCon, ppr x_s, ppr xs, ppr y_s, ppr ys, ppr is ])
        ; return $ acc <> ([(mkLtEvTerm is predTy, ct)], [], []) }


  -- Solving for All constraints
{-
        ∀  x ∈ r. 𝚪 |= C x
  -----------------------------
        𝚪 |= All C (R r)
-}

  | predTy <- API.ctPred ct
  , Just (clsCon, [_, cls, row]) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon allCls
  , Just (rCon, [_, assocs]) <- API.splitTyConApp_maybe row
  , rCon == rTF
  , Just (ls, ts) <- unzipAssocList assocs
  = do { API.tcPluginTrace "1 Found instance of All with class and args" (vcat [ppr ct, ppr (cls, ls, ts)])
       ; wanteds <- sequence [API.newWanted (API.ctLoc ct) (AppTy cls t) | t <- ts]
       ; API.tcPluginTrace "2 Generating new wanteds" (ppr wanteds)
       ; return $ acc <> ([(mkAllEvTerm wanteds predTy, ct)], map API.mkNonCanonical wanteds, [])
       }

  -- Handles the case where we have [W] (R [x := t] ~+~ r) ~#  (R [x := t, y := u])
  -- This just emits the equality constraint [W] r ~# R [y := u]
  -- This is very specific becuase i want it to be the last resort and not cause the plugin to loop
{-
            r = x \ y
  -------------------------------
        𝚪 |= (R x ~+~ R r)  ~  R y
-}

  | predTy <- API.ctPred ct
  , isEqPrimPred predTy
  , Just (_tc, [_, _, lhsTy, rhsTy]) <- API.splitTyConApp_maybe predTy
  , Just (_tftc, [_, r, y]) <- API.splitTyConApp_maybe lhsTy
  , Just yTVar <- getTyVar_maybe y -- y is a type variable
  , Just (_ , [k , assocs]) <- API.splitTyConApp_maybe r
  , Just (tcRhs , [_ , rhsAssocs]) <- API.splitTyConApp_maybe rhsTy
  , tcRhs == rTF
  , let xs = unfold_list_type_elems assocs
  , let ys = unfold_list_type_elems rhsAssocs
  , let diff = sortAssocs $ setDiff xs ys
  = do { API.tcPluginTrace "--Plugin solving Type Eq rule--" (vcat [ppr _tc , ppr assocs, ppr rhsAssocs, ppr diff])
       ; let rowAssocKi = mkTyConApp rowAssocTyCon [k]
             y0 = API.mkTyConApp rTF [k,  mkPromotedListTy rowAssocKi diff]
       ; API.tcPluginTrace "--Plugin solving Type Eq rule (emit equality)--" (text "computed" <+> ppr yTVar <+> text "=:=" <+> ppr y0)
       ; nw <- API.newWanted (API.ctLoc ct) $ API.mkPrimEqPredRole API.Nominal (mkTyVarTy yTVar) y0
       ; return $ acc <> ( []
                         , [API.mkNonCanonical nw]
                         , []
                         )
       }

  -- Handles the case where we have [W] (R [x1 := t]) ~#  (R [x2 := t])
  -- This just emits the equality constraint [W] x1 ~# x2
{-
        𝚪 |=  x ~ y
  -------------------------------
        𝚪 |= R x  ~  R y
-}

  | predTy <- API.ctPred ct
  , isEqPrimPred predTy
  , Just (_, [_, _, lhsTy, rhsTy]) <- API.splitTyConApp_maybe predTy
  , Just (_tcL, [kl, las]) <- API.splitTyConApp_maybe lhsTy
  , Just (_tcR, [kr, ras]) <- API.splitTyConApp_maybe rhsTy
  , _tcL == rTF
  , _tcR == rTF
  , let rs = unfold_list_type_elems ras
  , let ls = unfold_list_type_elems las
  , API.eqType kr kl
  , length rs == length ls
  , eqs <- makeEqFromAssocs rs ls
  = do { API.tcPluginTrace "--Plugin Eq RTF--" (vcat [ppr rs, ppr ls])
       ; nws <- mapM (\(lhsTy', rhsTy') ->
                        API.newWanted (API.ctLoc ct) $ API.mkPrimEqPredRole API.Nominal lhsTy' rhsTy')
                  eqs
       ; return $ acc <> ( [(API.mkPluginUnivEvTerm "RoHs.Plugin.TC" API.Nominal lhsTy rhsTy, ct)]
                         , API.mkNonCanonical <$> nws
                         , [] )
       }


{-
     𝚪 |= F x  ~  F' y   F /= F'
  ---------------------------------
        𝚪 |= contra (F x) (F' y)
-}
  -- We want to reject equalities between V0 x and V1 y
-- TODO: I don't think we should be doing this.
  | predTy <- API.ctPred ct
  , isEqPrimPred predTy
  , Just (_tc, [_, _, lhsTy, rhsTy]) <- API.splitTyConApp_maybe predTy
  , Just (lhsTc, _) <- API.splitTyConApp_maybe lhsTy
  , Just (rhsTc, _) <- API.splitTyConApp_maybe rhsTy
  , lhsTc /= rhsTc
  , isFamilyTyCon lhsTc
  , isFamilyTyCon rhsTc
  = do { do API.tcPluginTrace "--Plugin obviously not equal TyFam--" (ppr ct)
       ; error_predTy <- API.mkTcPluginErrorTy (mkTyFamNotEqError lhsTy rhsTy)
       ; nw_error <- API.newWanted (API.ctLoc ct) error_predTy
       ; return $ acc <> ([], [], [API.mkNonCanonical nw_error])
       }

  -- We want to reject equalities between labels that are not equal
{-
     𝚪 |= (l1 := t) ~ (l2 := t)  l1 /= l2
  -----------------------------------------
        𝚪 |= contra (l1 := t) (l2 := t)
-}
  | predTy <- API.ctPred ct
  , isEqPrimPred predTy
  , Just (_tc, [_, _, lhsTy, rhsTy]) <- API.splitTyConApp_maybe predTy
  , Nothing <- API.splitTyConApp_maybe lhsTy
  , Nothing <- API.splitTyConApp_maybe rhsTy
  , not (API.isTyVarTy lhsTy)
  , not (API.isTyVarTy rhsTy)
  , not $ API.eqType lhsTy rhsTy
  = do { do API.tcPluginTrace "--Plugin obviously not equal groundType--" (ppr ct)
       ; error_predTy <- API.mkTcPluginErrorTy (mkTyFamNotEqError lhsTy rhsTy)
       ; nw_error <- API.newWanted (API.ctLoc ct) error_predTy
       ; return $ acc <> ([], [], [API.mkNonCanonical nw_error])
       }

{-
                 r1 /= r2
  -----------------------------------------
        𝚪 |= contra (R r1) (R r2)
-}
  | predTy <- API.ctPred ct
  , isEqPrimPred predTy
  , Just (_, ([_, _, lhsTy, rhsTy])) <- API.splitTyConApp_maybe predTy
  , Just (_r_tycon1, [kx, assocs_x]) <- API.splitTyConApp_maybe lhsTy
  , Just (_r_tycon2, [ky, assocs_y]) <- API.splitTyConApp_maybe rhsTy
  , let xs = unfold_list_type_elems assocs_x
  , let ys = unfold_list_type_elems assocs_y
  , not (API.eqType kx ky) || length xs /= length ys -- we are not having hetrogenous row concat
  , _r_tycon1 == _r_tycon2
  , _r_tycon1 == rTF
  = do { do API.tcPluginTrace "--Plugin obviously not equal R TypeFams--" (ppr ct)
       ; error_predTy <- API.mkTcPluginErrorTy (mkTyFamNotEqError lhsTy rhsTy)
       ; nw_error <- API.newWanted (API.ctLoc ct) error_predTy
       ; return $ acc <> ([], [], [API.mkNonCanonical nw_error])
       }

{-

  ---------------------------------------------------
    𝚪, ctEq: V1 x ~ V1 z, ct1: x ~<~ xy, ct2: xy ~<~ y0 |= z ~<~ y0
-}
  -- Handles the case of transitive reasoning of ~<~
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, z, y0])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , Just zTyVar <- getTyVar_maybe z
  , Just y0TyVar <- getTyVar_maybe y0
  , Just (vTyVar, _) <- findV1EqGiven v1TyCon zTyVar givens
  , Just (xy, ct1, ct2) <- findLeqGiven (API.classTyCon rowLeqCls) (vTyVar, y0TyVar) givens
  =  do {
        ; let new_ev = mkLeqTransEvTerm composeId ct1 ct2 predTy
        --  TODO cast ctEvidence with ctEq first.
        ; API.tcPluginTrace "--Plugin solving ~<~ transitive" (vcat [ ppr ct
                                                                    , ppr zTyVar
                                                                    , ppr y0TyVar
                                                                    , ppr (xy, ct1, ct2) , ppr new_ev
                                                                    ])

        ; return $ acc <> ([(new_ev, ct)], [], [])
        }


-- This is now looking like whack a mole,
-- precicely because GHC cannot do injectivity of TFs 𝚪, V1 x ~ V1 z |= x ~ z
{-

 ---------------------------------------------------
    𝚪, V1 x ~ V1 z, x ~<~ y |= z ~<~ y
-}
  -- Handles the case of transitive reasoning of ~<~
  | predTy <- API.ctPred ct
  , Just (clsCon, ([_, z, y])) <- API.splitTyConApp_maybe predTy
  , clsCon == API.classTyCon rowLeqCls
  , isJust $ getTyVar_maybe z
  , isJust $ getTyVar_maybe y
  , let ctV1eqs = filter (\c -> case getEqPredTys_maybe (API.ctPred c) of
                              {Just (_, lhsTy', rhsTy') | Just (tc, [_, _]) <- splitTyConApp_maybe lhsTy'
                                                        , Just (tc', [_, r']) <- splitTyConApp_maybe rhsTy'
                                                        , tc == tc', tc == v1TyCon
                                                        -> API.eqType r' z

                              ; _ -> False})
                    givens
  , let ctleqs = filter (\c -> case API.splitTyConApp_maybe (API.ctPred c) of
                              {Just (tc, [_, _, y']) | tc == API.classTyCon rowLeqCls, isJust $ getTyVar_maybe y'
                                                      -> API.eqType y' y

                              ; _ -> False})
                    givens

  =  do { API.tcPluginTrace "--Plugin solving ~<~ transitive simple" (vcat [ ppr ct
                                                                           , ppr ctV1eqs
                                                                           , ppr ctleqs
                                                                           ])
        ; if not (null ctV1eqs) && not (null ctleqs)
          then do { let new_ev = API.evCast (API.ctEvExpr $ API.ctEvidence (head ctleqs))
                                            (mkCoercion API.Representational (API.ctPred (head ctleqs)) predTy)
                  ; API.tcPluginTrace "" (ppr new_ev)
                  ; return $ acc <> ([(new_ev, ct)], [], [])
                  }
        ; else return $ acc
        }


{-

  ---------------------------
    𝚪, V1 x ~ V1 z |= x ~ z
-}
  -- Handles the case where we get injectivity of V1, apparently it doesn't come for free :(
  | predTy <- API.ctPred ct
  , Just (_, lhsTy, rhsTy) <- getEqPredTys_maybe predTy
  , ctEqs <- filter (\c -> case getEqPredTys_maybe (API.ctPred c) of
                              {Just (_, lhsTy', rhsTy') | Just (tc, [_, l']) <- splitTyConApp_maybe lhsTy'
                                                        , Just (tc', [_, r']) <- splitTyConApp_maybe rhsTy'
                                                        , tc == tc', tc == v1TyCon
                                                        -> API.eqType l' rhsTy && API.eqType r' lhsTy
                              ; _ -> False})
                    givens
  =  do {
        --  TODO cast ctEvidence with ctEq first.
        ; if  null ctEqs
          then return acc
          else do { API.tcPluginTrace "--Plugin solving Eq from Given V1" (vcat [ ppr ct, ppr (lhsTy, rhsTy), ppr ctEqs ])
                  ; return $ acc <> ([(API.mkPluginUnivEvTerm "RoHs.Plugin.TC" API.Nominal lhsTy rhsTy, ct)], [], [])}
        }

  | otherwise = do API.tcPluginTrace "--Plugin solving No rule matches--" (ppr ct)
                   return $ acc


unzipAssocList :: API.TcType -> Maybe ([API.TcType], [API.TcType])
unzipAssocList t = unzip <$> mapM openAssoc (unfold_list_type_elems t) where

  openAssoc :: API.TcType -> Maybe (API.TcType, API.TcType)
  openAssoc tup
    | Just (_assocCon, [_, lhs, rhs]) <- API.splitTyConApp_maybe tup
     -- check that assocCon is actually `:=`
    = return (lhs, rhs)
    | otherwise
    = Nothing


mkLtEvTerm :: [Int] -> Type -> API.EvTerm
mkLtEvTerm is predTy = API.evCast tuple (mkCoercion API.Representational tupleTy predTy) where
  n = length is
  tupleTy = mkTupleTy1 API.Boxed [intTy, mkTupleTy1 API.Boxed (replicate n intTy)]
  tuple = mkCoreBoxedTuple [mkCoreInt n, mkCoreBoxedTuple (map mkCoreInt is)]

mkPlusEvTerm :: [(Int, Int)] -> Type -> API.EvTerm
mkPlusEvTerm pairs predTy = API.evCast tuple (mkCoercion API.Representational tupleTy predTy) where
  n = length pairs
  tupleTy = mkTupleTy1 API.Boxed [intTy, mkTupleTy1 API.Boxed (replicate n (mkTupleTy1 API.Boxed [intTy, intTy]))]
  tuple = mkCoreBoxedTuple [mkCoreInt n, mkCoreBoxedTuple [mkCoreBoxedTuple [mkCoreInt x, mkCoreInt y] | (x, y) <- pairs]]

mkReflEvTerm :: Type -> API.EvTerm
mkReflEvTerm predTy = API.evCast tuple (mkCoercion API.Representational tupleTy predTy) where
  tupleTy = mkTupleTy1 API.Boxed [intTy, unitTy]
  tuple = mkCoreBoxedTuple [mkCoreInt (-1), mkCoreBoxedTuple []]

mkAllEvTerm :: [API.CtEvidence] -> Type -> API.EvTerm
mkAllEvTerm evs predTy = API.evCast evAllTuple (mkCoercion API.Representational evAllTupleTy predTy) where
  (evVars, predTys) = unzip [(evVar, pTy) | API.CtWanted pTy (API.EvVarDest evVar) _ _ <- evs]
  evTuple = mkCoreConApps (cTupleDataCon (length evVars)) $ (map Type predTys) ++ map Var evVars
  evAllTupleTy = mkTupleTy1 API.Boxed [intTy, anyType]
  evAllTuple = mkCoreBoxedTuple [ mkCoreInt (length evVars)
                                , Cast evTuple (mkCoercion API.Representational (mkConstraintTupleTy predTys) anyType)]

-- We have x ~<~ y and y ~<~ z
-- We need to build an evidence for x ~<~ z (toType)
-- we have a function compose :: (Int, a) -> (Int, b) -> (Int, c)
--
mkLeqTransEvTerm :: API.Id -> API.Ct -> API.Ct -> Type -> API.EvTerm
mkLeqTransEvTerm composeId ct1 ct2 toType = API.evCast evExpr (mkCoercion API.Representational tupleTy toType)
  where
    evExpr :: API.EvExpr
    evExpr = mkCoreApps (Var composeId) [Type anyType, Type anyType, Type anyType, arg1, arg2]

    tupleTy = mkTupleTy1 API.Boxed [intTy, anyType]

    arg1, arg2 :: API.EvExpr
    arg1 = Cast (API.ctEvExpr (API.ctEvidence ct1)) (mkCoercion API.Representational (API.ctPred ct1) tupleTy)
    arg2 = Cast (API.ctEvExpr (API.ctEvidence ct2)) (mkCoercion API.Representational (API.ctPred ct2) tupleTy)


mkCoercion :: API.Role -> Type -> Type -> Coercion
mkCoercion = API.mkPluginUnivCo "Proven by RoHs.Plugin.TC"

-- If you get a list of assocs, flatten it out
unfold_list_type_elems :: API.TcType -> [API.TcType]
unfold_list_type_elems t =  sortAssocs $ go [] t
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

makeEqFromAssocs :: [API.TcType] -> [API.TcType] -> [(API.TcType, API.TcType)]
makeEqFromAssocs gs ws = go [] gs ws
  where
    go acc [] [] = acc
    go acc (g:gs') (w:ws')
      | Just (_, [_, sg, ug]) <- API.splitTyConApp_maybe g
      , Just (_, [_, sw, uw]) <- API.splitTyConApp_maybe w
      = go ((sg, sw):(ug, uw):acc) gs' ws'
    go _ ls rs = API.pprPanic "mkEqFromAssocs" (ppr ls $$ ppr rs)

-- Nothing to shutdown.
tcPluginStop :: PluginDefs -> API.TcPluginM API.Stop ()
tcPluginStop _ = do
  API.tcPluginTrace "--Plugin Stop--" empty
  pure ()

-- We have to possibly rewrite ~+~ type family applications
tcPluginRewrite :: PluginDefs -> API.UniqFM API.TyCon API.TcPluginRewriter
tcPluginRewrite defs@(PluginDefs {..}) = API.listToUFM [ (rowPlusTF, rewrite_rowplus defs)
                                                       -- , (rTF, intercept_tyfam defs)
                                                       ]

-- | Template interceptor for a type family tycon
-- intercept_tyfam :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
-- intercept_tyfam _ givens tys
--   = do API.tcPluginTrace "--Plugin R TF--" (vcat [ ppr givens $$ ppr tys ])
--        pure API.TcPluginNoRewrite

-- | Reduce (x := t) ~+~ (y := u) to [x := t, y := u]
--   Post condition: The label occurance in the list is lexicographic.
rewrite_rowplus :: PluginDefs -> [API.Ct] -> [API.TcType] -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
rewrite_rowplus (PluginDefs { .. }) _givens tys
  | [_, a, b] <- tys
  , Just (_ , [ka, arg_a]) <- API.splitTyConApp_maybe a
  , Just (_ , [kb, arg_b]) <- API.splitTyConApp_maybe b
  , assocs_a <- unfold_list_type_elems arg_a
  , assocs_b <- unfold_list_type_elems arg_b
  , API.eqType ka kb
  , let rowAssocKi = mkTyConApp rowAssocTyCon [ka]
  = do { let inter = setIntersect assocs_a assocs_b
             concat_assocs = sortAssocs $ assocs_a ++ assocs_b
             redn = API.mkTyFamAppReduction "RoHs.Tc.Plugin" API.Nominal rowPlusTF tys
                               (API.mkTyConApp rTF [ka, mkPromotedListTy rowAssocKi concat_assocs])
       ; if null inter
         then do { API.tcPluginTrace "--Plugin RowConcatRewrite (~+~)--" (vcat [ text "args_a:" <+> ppr assocs_a
                                                                     , text "args_b:" <+> ppr assocs_b
                                                                     , text "args:"   <+> ppr concat_assocs
                                                                     , text "givens:" <+> ppr _givens
                                                                     , text "redn:"  <+> ppr redn
                                                                     ])
                 ; return $ API.TcPluginRewriteTo redn []
                 }
         else do { API.tcPluginTrace "--Plugin Throw error RowConcatRewrite (~+~)--" (vcat [ text "a:" <+> ppr assocs_a
                                                                                           , text "b:" <+> ppr assocs_b
                                                                                           , text "inter" <+> ppr inter])
                 ; throwTypeError redn (mkSameLabelError a b inter) }
       }
  | otherwise
  = do API.tcPluginTrace "--Plugin Cannot Reduce TyFam (~+~)--" (ppr tys)
       pure API.TcPluginNoRewrite


-- | get labels from an assoc
getLabel :: API.TcType -> Maybe API.Type
getLabel ty | Just (_, [_, LitTy lbl_l, _]) <- API.splitTyConApp_maybe ty
            = Just (LitTy lbl_l)
            | otherwise = Nothing


getLabels :: [API.TcType] -> [API.Type]
getLabels = catMaybes . fmap getLabel


---- The worlds most efficient set operations below ---

-- Precondition for each of the operations below is that they should be Assocs
-- They will not work as expected for non-Assoc types

-- | Checks if the first argument is a subset of the second argument, with evidence
checkSubsetEv :: [Type] -> [Type] -> Maybe [Int]
checkSubsetEv [] _        = Just []
checkSubsetEv (x : xs) ys = (:) <$> findIndex (API.eqType x) ys <*> checkSubsetEv xs ys

-- | Checks if the first argument is a subset of the second argument
-- checkSubset  :: [Type] -> [Type] -> Bool
-- checkSubset xs ys = isJust (checkSubsetEv xs ys)

checkConcatEv :: [Type] -> [Type] -> [Type] -> Maybe [(Int, Int)]
checkConcatEv _ _ [] = Just []
checkConcatEv xs ys (z : zs) = (:) <$> zIdx <*> checkConcatEv xs ys zs where
  zIdx = ((0,) <$> findIndex (API.eqType z) xs) `mplus` ((1,) <$> findIndex (API.eqType z) ys)

-- | computes for set difference
--   setDiff xs ys = { z  | z in ys && z not in xs }
setDiff :: [Type] -> [Type] -> [Type]
setDiff xs ys = setDiff_inner [] xs ys
  where
    setDiff_inner acc _ [] = acc
    setDiff_inner acc xs' (y : ys') | any (API.eqType y) xs' = setDiff_inner acc xs' ys'
                                    | otherwise = setDiff_inner (y:acc) xs' ys'

-- computes the set intersection of two rows
setIntersect :: [Type] -> [Type] -> [Type]
setIntersect xs ys = if length xs < length ys then set_intersection [] xs ys else set_intersection [] ys xs
  where
    set_intersection acc [] _ = acc
    set_intersection acc (x:xs') ys' | any (eqAssoc x) ys' = set_intersection (x:acc) xs' ys'
                                     | otherwise = set_intersection acc xs' ys'

-- At this point i'm just sorting on the kind of the type which happens to be a string literal, Sigh ...
cmpAssoc :: API.TcType -> API.TcType -> Ordering
cmpAssoc lty rty | Just (_, [_, LitTy l@(StrTyLit _), _]) <- API.splitTyConApp_maybe lty
                 , Just (_, [_, LitTy r@(StrTyLit _), _]) <- API.splitTyConApp_maybe rty
                 = cmpTyLit l r
cmpAssoc _ _ = error "shouldn't happen cmpAssoc"

-- make GHC Type checker go brrr
eqAssoc :: API.TcType -> API.TcType -> Bool
eqAssoc lty rty | Just (_, [_, LitTy (StrTyLit lbl_l), _]) <- API.splitTyConApp_maybe lty
                , Just (_, [_, LitTy (StrTyLit lbl_r), _]) <- API.splitTyConApp_maybe rty
                = lbl_l == lbl_r
eqAssoc _ _ = error "shouldn't happen eqAssoc"

-- This is the "cannonical/principal" type representation of a row type
sortAssocs :: [API.TcType] -> [API.TcType]
sortAssocs = sortBy cmpAssoc

---- The worlds most efficient set operations above -----

findV1EqGiven :: API.TyCon -> TyVar -> [API.Ct] -> Maybe (TyVar, API.Ct)
findV1EqGiven v1TyCon zTyVar givens = case filter (matchTyVar v1TyCon zTyVar) givens of
                                        (ct : _) | Just (_eqTyCon, [_, _, pTy, _]) <- splitTyConApp_maybe (API.ctPred ct)
                                                 , Just (tc, [_, vTy]) <- splitTyConApp_maybe pTy
                                                 , tc == v1TyCon
                                                 , Just vTyVar <- getTyVar_maybe vTy
                                                 -> Just (vTyVar , ct)
                                        _    -> Nothing
   where
     matchTyVar :: API.TyCon -> TyVar -> API.Ct -> Bool
     matchTyVar tc ztv c | pTy <- API.ctPred c
                         , isEqPrimPred pTy
                         , Just (_ , [_, _, _, t1]) <- splitTyConApp_maybe pTy
                         , Just (tycon, [_, tyVar]) <- splitTyConApp_maybe t1
                         , Just tv <- getTyVar_maybe tyVar
                         , tycon == tc
                         = tv == ztv
                         | otherwise
                         = False

findLeqGiven :: API.TyCon -> (TyVar, TyVar) -> [API.Ct] -> Maybe (TyVar, API.Ct, API.Ct)
findLeqGiven leqClsTyCon (tvx, _) givens | (ct1 : _) <-  filter (matchTyVar leqClsTyCon tvx) givens
                                           , Just (_, [_, _, t2]) <- splitTyConApp_maybe (API.ctPred ct1)
                                           , Just tvxy <- getTyVar_maybe t2
                                           , (ct2 : _) <- filter (matchTyVar leqClsTyCon tvxy) givens
                                           = Just (tvxy, ct1, ct2)
                                           | otherwise
                                           = Nothing
  where
    matchTyVar :: API.TyCon -> TyVar -> API.Ct -> Bool
    matchTyVar tc tv c | pTy <- API.ctPred c
                       , Just (clsTyCon , [_, t1, _]) <- splitTyConApp_maybe pTy
                       , clsTyCon == tc
                       , Just tvvar <- getTyVar_maybe t1
                       , tvvar == tv
                       = True
                       | otherwise
                       = False

-- Return the given type family reduction, while emitting an additional type error with the given message.
throwTypeError :: API.Reduction -> API.TcPluginErrorMessage -> API.TcPluginM API.Rewrite API.TcPluginRewriteResult
throwTypeError badRedn msg = do
  env <- API.askRewriteEnv
  errorTy <- API.mkTcPluginErrorTy msg
  let
    errorCtLoc :: API.CtLoc
    errorCtLoc = API.bumpCtLocDepth $ API.rewriteEnvCtLoc env
  errorCtEv <- API.setCtLocM errorCtLoc $ API.newWanted errorCtLoc errorTy
  pure $ API.TcPluginRewriteTo badRedn [ API.mkNonCanonical errorCtEv ]



-- | Make the error message to be raised when two rows cannot be concatinated
mkSameLabelError :: Type -> Type -> [Type] -> TcPluginErrorMessage
mkSameLabelError r1 r2 common = Txt "Cannot concat rows"
                         :-: (PrintType r1)
                         :-: (Txt " with ")
                         :-: (PrintType r2)
                         :-: Txt "Contains Common Labels"
                         :-: foldl (\ acc lbl -> acc :|: (Txt " ") :|: (PrintType lbl)) (Txt "") (getLabels common)

mkTyFamNotEqError :: Type -> Type -> TcPluginErrorMessage
mkTyFamNotEqError ty1 ty2
  = Txt "Cannot Unify"
  :-: (PrintType ty1)
  :-: (Txt " with ")
  :-: (PrintType ty2)

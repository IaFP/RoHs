module RoHs.Plugin.Source (addPlusConstraints) where

import           GHC.Hs
import           GHC.Rename.Names
import           GHC.Plugins            as GHC
import           GHC.Tc.Utils.Monad (traceRn)
import           GHC.Tc.Plugin          as GHC
import           GHC.Tc.Types

import Data.Generics.Aliases
import Data.Generics.Schemes

import Control.Monad.Writer

-- TODO: maybe less copy and paste?

resolveImport :: ModuleName -> Maybe FastString -> TcPluginM PkgQual
resolveImport mod_name mPkg = do
  hscEnv <- getTopEnv
  return $ renamePkgQual (hsc_unit_env hscEnv) mod_name mPkg

findCommonModule :: TcM Module
findCommonModule = do
  let modlName = mkModuleName "RoHs.Language.Types"
  pkgQual    <- runTcPluginM $ resolveImport modlName Nothing
  findResult <- runTcPluginM $ findImportedModule modlName pkgQual
  case findResult of
    Found _ res     -> pure res
    FoundMultiple _ -> error $ "RoHs.Plugin: found multiple modules named RoHs.Common in the current package."
    _               -> error $ "RoHs.Plugin: could not find any module named RoHs.Common in the current package."


addPlusConstraints :: [CommandLineOption] -> TcGblEnv -> HsGroup GhcRn ->  TcM (TcGblEnv, HsGroup GhcRn)
addPlusConstraints _options gblEnv grp =
  do traceRn "~~~ Entering addPlusConstraints ~~~" empty
     commonModule   <- findCommonModule
     names <- runTcPluginM $
              N <$> lookupOrig commonModule (mkTcOcc "~+~")
                <*> lookupOrig commonModule (mkTcOcc "Plus")
                <*> lookupOrig commonModule (mkDataOcc "R")
                <*> lookupOrig commonModule (mkDataOcc ":=")
     grp' <- everywhereM (mkM (xformSignatures names)) grp
     grp'' <- everywhereM (mkM (xformE names)) grp'
     return (gblEnv, grp'')

data Names = N { plusTyCon, plusPredCon, rowTyCon, assocTyCon :: Name }

-- | Top level function to transform the type signature
xformSignatures :: Names -> LSig GhcRn -> TcM (LSig GhcRn)
xformSignatures names (L sigLoc (TypeSig tsext ids (HsWC wcext (L sigTypeLoc sigType@(HsSig {}))))) =
  do sig_body' <- xformT names (sig_body sigType)
     return (L sigLoc (TypeSig tsext ids (HsWC wcext (L sigTypeLoc sigType { sig_body = sig_body' }))))
xformSignatures _ sig =
  do return sig

-- | Top level function to transform the declaration body as it may contain type signatures
xformE :: Names -> HsExpr GhcRn -> TcM (HsExpr GhcRn)
xformE names (ExprWithTySig ext ex (HsWC wcext (L sigTypeLoc sigType@(HsSig {})))) =
  do body' <- xformT names (sig_body sigType)
     return (ExprWithTySig ext ex (HsWC wcext (L sigTypeLoc sigType { sig_body = body'})))
xformE _ e = return e

xformT :: Names -> LHsType GhcRn -> TcM (LHsType GhcRn)
xformT names t =
  do (t'@(L loc@(SrcSpanAnn _ srcSpan) _), preds) <- runWriterT (collect names t)
     if null preds
     then return t'
     else -- We encountered a type without quantifiers... so I'll try converting
          -- it to a qualified type, but I'm not 100% sure how this will work
          -- out...
          do let t'' = L loc (HsQualTy NoExtField (L (SrcSpanAnn EpAnnNotUsed srcSpan) preds) t')
             traceRn "3 adding predicates to type (no quantifiers):" (cat [ppr t, text " ==> ", ppr t''])
             return t''

type CollectM = WriterT (HsContext GhcRn) TcM

-- Identifies types that look like `R '["x" := t, "y" := u, "z" := v, ...]`.
isRowLiteral :: Names -> LHsType GhcRn -> Bool
isRowLiteral names (L _ (HsAppTy _ (L _ (HsTyVar _ _ (L _ vname))) (L _ (HsExplicitListTy _ _ assocs)))) =
  vname == rowTyCon names && all isAssocLiteral assocs where

  isAssocLiteral (L _ (HsAppTy _ (L _ (HsAppTy _ (L _ (HsTyVar _ _ (L _ name))) (L _(HsTyLit _ (HsStrTy _ _))))) _)) =
    name == assocTyCon names
  isAssocLiteral (L _ (HsOpTy _ _ (L _ (HsTyLit _ (HsStrTy _ _))) (L _ name) _)) =
    name == assocTyCon names
  isAssocLiteral _ = False

isRowLiteral names (L _ (HsParTy _ ty)) = isRowLiteral names ty -- are there more cases like this?!
isRowLiteral _ _ = False

collect :: Names -> LHsType GhcRn -> CollectM (LHsType GhcRn)
collect names = collectL where

  collectT :: HsType GhcRn -> CollectM (HsType GhcRn)
  collectT (HsForAllTy NoExtField tele body@(L typeLoc _)) =
    do (body', preds) <- censor (const []) $ listen (collectL body)
       lift (traceRn ("6 At " ++ showSDocUnsafe (ppr typeLoc) ++ " found a signature") (vcat [ text "body:" <+> ppr body'
                                                                                               , text "preds:" <+> ppr preds]))
       return (HsForAllTy NoExtField tele (L typeLoc (HsQualTy NoExtField (L (SrcSpanAnn EpAnnNotUsed (locA typeLoc)) preds) body')))
  collectT (HsQualTy NoExtField ctxt body) =
    HsQualTy NoExtField <$> collectC ctxt <*> collectL body
  collectT t@(HsAppTy NoExtField (L srcloc (HsAppTy NoExtField (L _ (HsTyVar _ NotPromoted (L nameLoc name))) lhs)) rhs)
    | name == plusTyCon names && (not (isRowLiteral names lhs) || not (isRowLiteral names rhs)) =
      do let p = L srcloc (HsAppTy NoExtField (L srcloc (HsAppTy NoExtField (L srcloc (HsAppTy NoExtField (L srcloc (HsTyVar EpAnnNotUsed NotPromoted (L nameLoc (plusPredCon names)))) lhs)) rhs)) (L srcloc t)) -- lying about source location here
         lift (traceRn ("1 At " ++ showSDocUnsafe (ppr srcloc) ++ " found use of ~+~:") (ppr t))
         tell [p]
         return t
    | name == plusTyCon names =
      do lift (traceRn "4 Not emitting `Plus` constraint, as both arguments are literal rows" (ppr t))
         return t
  collectT (HsAppTy NoExtField fun arg) =
    HsAppTy NoExtField <$> collectL fun <*> collectL arg
  collectT (HsAppKindTy ext fun arg) = -- this gains an argument by GHC 9.8
    HsAppKindTy ext <$> collectL fun <*> collectL arg
  collectT (HsFunTy ext arr dom cod) =
    HsFunTy ext arr <$> collectL dom <*> collectL cod
  collectT (HsListTy ext e) =
    HsListTy ext <$> collectL e
  collectT (HsTupleTy ext sort elems) =
    HsTupleTy ext sort <$> mapM collectL elems
  collectT (HsSumTy ext ts) =   -- Btw, what is this?
    HsSumTy ext <$> mapM collectL ts
  collectT t@(HsOpTy _ NotPromoted lhs@(L srcloc _) (L nameloc name) rhs)
    | name == plusTyCon names && (not (isRowLiteral names lhs) || not (isRowLiteral names rhs)) =
      do let p = L srcloc (HsAppTy NoExtField (L srcloc (HsAppTy NoExtField (L srcloc (HsAppTy NoExtField (L srcloc (HsTyVar EpAnnNotUsed NotPromoted (L nameloc (plusPredCon names)))) lhs)) rhs)) (L srcloc t)) -- lying about source location here
         lift (traceRn "2 Emitting constraint" (ppr p))
         tell [p]
         return t
    | name == plusTyCon names =
      do lift (traceRn "5 Not emitting `Plus` constraint, as both arguments are literal rows" (ppr t))
         return t
  collectT (HsOpTy ext promoted lhs op rhs) =
    HsOpTy ext promoted <$> collectL lhs <*> pure op <*> collectL rhs
  collectT (HsParTy ext ty) =
    HsParTy ext <$> collectL ty
  collectT (HsIParamTy ext name ty) =
    HsIParamTy ext name <$> collectL ty
  collectT (HsKindSig ext ty k) =
    HsKindSig ext <$> collectL ty <*> collectL k
  collectT (HsSpliceTy {}) =
    undefined -- missing some bits here
  collectT (HsDocTy ext ty doc) =
    HsDocTy ext <$> collectL ty <*> pure doc
  collectT (HsBangTy ext bang ty) =
    HsBangTy ext bang <$> collectL ty
  collectT (HsRecTy{}) =
    undefined -- TODO: look up field types
  collectT (HsExplicitListTy ext promoted tys) =
    HsExplicitListTy ext promoted <$> mapM collectL tys
  collectT (HsExplicitTupleTy ext tys) =
    HsExplicitTupleTy ext <$> mapM collectL tys
  collectT t = return t
    -- HsTyVar _ _ _
    -- HsStarTy _ _
    -- HsTyLit _ _
    -- HsWildCardTy _
    -- XXType    ...

  collectC :: LHsContext GhcRn -> CollectM (LHsContext GhcRn)
  collectC (L ann preds) = L ann <$> mapM collectL preds

  collectL :: LHsType GhcRn -> CollectM (LHsType GhcRn)
  collectL (L loc t) = L loc <$> collectT t

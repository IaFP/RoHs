{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
module RoHs.Plugin.Core (install) where

import GHC.Plugins
import GHC.Utils.Monad

import RoHs.Plugin.Semantics

import Data.List as List


{-
The plugin portion that gives real meanings to undefined terms.

It makes a traveral over the generated compiler core and replaces
each primitive mentioned in the `primMap` with the actual core expression.

Optionally: Runs the simplifier after the replacement
to see if any simplifications can be made to the core term structure
to have efficient (space and time) during the runtime phase.

-}

data RoHsPluginOptions = RoHsPluginOptions {debugMode :: Bool}

-- | The entry point for the core plugin.
--   shamelessly copied from AsyncRattus.Plugin.hs
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todo = case find findSamePass todo of       -- check that we don't run the transformation twice
                      Nothing -> return (strPass : todo) -- (e.g. if the "-fplugin" option is used twice)
                      _ -> return todo
    where name = "RoHs Semantics Plugin"
          strPass = CoreDoPluginPass name (txRoHsSemantics RoHsPluginOptions{debugMode = dmode})
          dmode = "debug" `elem` opts
          findSamePass (CoreDoPluginPass s _) = s == name
          findSamePass _ = False



-- | All the RoHs primities need to be transformed into the actual semantics
--   eg. RoHsPrimitives.labR0 should do the dictonary manipulation to create/simulate
--   a singleton row
--   Theoritically, the safety-ness criteria comes from the GHC Typechecker and TcPlugin
--   The implementation correctness is well: ¯\_(ツ)_/¯
txRoHsSemantics :: RoHsPluginOptions -> ModGuts -> CoreM ModGuts
txRoHsSemantics _ mgs@ModGuts{..} = do { putMsg (text "Hello from" <+> (ppr $ moduleName mg_module))
                                       ; mg_binds' <- mapM (tx (mgs, primMap)) mg_binds
                                       ; return $ mgs{mg_binds = mg_binds'}}


class Transform x where
  tx :: (ModGuts, PrimMap) -> x -> CoreM x

instance Transform CoreBind where
  tx pm (NonRec var expr) = NonRec var <$> tx pm expr
  tx pm (Rec bnds)        = Rec <$> mapSndM (tx pm) bnds

instance Transform CoreExpr where
  tx (mgs, pm) (Var i) = case List.lookup (getOccFS i) pm of
                          Nothing -> do { -- putMsg (text "not found" <+> ppr i);
                                          return $ Var i }
                          Just e -> do { putMsg (text "found" <+> ppr i);
                                         e (mgs, idType i) }

  tx pm (Lam arg body) = Lam arg <$> tx pm body
  tx pm (App e1 e2)    = liftA2 App (tx pm e1) (tx pm e2)

  tx pm (Let bind e)    = liftA2 Let (tx pm bind) (tx pm e)

  tx pm (Tick ct e)    = Tick ct <$> (tx pm e)

  tx pm (Case e b ty alts) = (\ x -> Case x b ty alts) <$> tx pm e

  tx pm (Cast e co)       = (\ x -> Cast x co) <$> tx pm e

  tx _ x              = return x

{-# LANGUAGE RecordWildCards #-}
module RoHs.Plugin.Core (install) where

import GHC.Plugins
import GHC.Utils.Monad

import RoHs.Plugin.Semantics


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
txRoHsSemantics _ mgs@ModGuts{..} = do {putMsg (text "Hello from" <+> (ppr $ moduleName mg_module))
                               ; mg_binds' <- mapM (tx primMap) mg_binds
                               ; return $ mgs{mg_binds = mg_binds'}}


class Transform x where
  tx :: PrimMap -> x -> CoreM x


instance Transform CoreProgram where
  tx pm x = do { putMsgS "=================Plugin.Core: transforming binds=============="
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

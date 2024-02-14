{-# LANGUAGE RecordWildCards #-}
module CorePlugin (install) where

import GHC.Plugins

import GHC.Core
import GHC.Tc.Types


import Data.List
import Data.Set as Set
import Data.Set (Set)
import Data.Map as Map
import Data.Map (Map)

-- TODO: Why is this core plugin being called twice?



{-
The plugin portion that gives real meanings to undefined terms.

It makes a traveral over the generated compiler core and replaces
each primitive mentioned in the `primMap` with the actual core expression.

Optionally: Runs the simplifier after the replacement
to see if any simplifications can be made to the core term structure
to have efficient (space and time) during the runtime phase.

-}

type PrimMap = Map String (CoreM CoreExpr)

primMap :: PrimMap
primMap = Map.fromList [ ("labR0", labR0Core)
                     ]


-- | labR0 :: forall s {t}. s -> t -> R0 (R '[ s := t])
--   labR0 = /\ s t. \ l v. ()
labR0Core :: CoreM CoreExpr
labR0Core = do return $ mkCoreLams bnds body
  where

    label = undefined "label"
    labelName = undefined "labelName"

    valueTy = undefined "valueTy"
    value   = undefined "value"

    bnds = [ label      -- s
           , valueTy    -- t
           , labelName  -- l :: s
           , value      -- v :: t
           ]
    body = mkBigCoreTup [ Lit $ mkLitInt8 1 -- single tuple
                        , mkBigCoreTup [ label ]
                        , mkBigCoreTup [ value ]
                        ]



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
                               ; mg_binds' <- transformBinds primMap mg_binds
                               ; return $ mgs{mg_binds = mg_binds'}}


transformBinds :: PrimMap -> CoreProgram -> CoreM CoreProgram
transformBinds _ x = do {putMsgS "--CorePlugin: transforming binds--"; return x}

module CorePlugin (install) where

import GHC.Plugins

import GHC.Core
import GHC.Tc.Types


import Data.List
import Data.Set as Set
import Data.Set (Set)
import Data.Map as Map
import Data.Map (Map)


primMap :: Map String CoreExpr
primMap = Map.fromList [ ("labR0", labR0Core)
                     ]

labR0Core :: CoreExpr
labR0Core = error "undefined CoreExpr"



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
insertRoHsSemantics _ mgs = do {putMsgS "Hello!"; return mgs}

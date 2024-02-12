-- Heavily Influenced by ghc-tcplugin-api example
-- https://github.com/sheaf/ghc-tcplugin-api/blob/main/examples/RewriterPlugin/plugin/RewriterPlugin.hs
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module RoHsPlugin (plugin) where

import qualified GHC.Plugins as GHC (Plugin(..), defaultPlugin, purePlugin)
import qualified GHC.TcPlugin.API as API

import qualified SourcePlugin as SP (addPlusConstraints)
import qualified TcPlugin as TP (tcPlugin)
import qualified CorePlugin as CP (install)

-- TODOs: (DONE) The plugin should enable replacing class Common.Plus with Common.(~+~)
--                    The user writes x ~+~ y and the source plugin converts it to Plus constraints
--                    BUG: (t -> (forall m x. m ~+~ x ~ z => p) -> g) shouldn't get converted to (Plux m x z) => (t -> ... -> g)
--                         i.e. make sure variables don't escape their scope
--        (DONE) Solving those `Plus` constraints.
--                    It also computes the right unknown meta variable
--                    Eg. `Plus (x:=t) y0 ( x:=t , y := u )` will deduce y0 ~ y := u
--
--               Internalize the representations of `labX` `unLabX` primitives
--               Internal.hs to be ported into manipulating dictonary evidences

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = \ _args -> Just $ API.mkTcPlugin TP.tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    , GHC.renamedResultAction = SP.addPlusConstraints
    , GHC.installCoreToDos = CP.install
    }

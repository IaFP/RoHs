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

-- TODOs: (DONE) The plugin should enable replacing class Common.Plus with Common.(~+~)
--               Internalize the representations of `labX` `unLabX` primitives

plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = \ _args -> Just $ API.mkTcPlugin TP.tcPlugin
    , GHC.pluginRecompile = GHC.purePlugin
    , GHC.renamedResultAction = SP.addPlusConstraints
    }

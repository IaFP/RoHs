-- Heavily Influenced by ghc-tcplugin-api example
-- https://github.com/sheaf/ghc-tcplugin-api/blob/main/examples/RewriterPlugin/plugin/RewriterPlugin.hs
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE NamedFieldPuns  #-}
{-# LANGUAGE MultiWayIf      #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
module RoHs.Plugin (plugin) where

import qualified GHC.Plugins as GHC (Plugin(..), defaultPlugin, impurePlugin)
import qualified GHC.TcPlugin.API as API

import qualified RoHs.Plugin.Source as SP (addPlusConstraints)
import qualified RoHs.Plugin.TC as TP (tcPlugin)

-- TODOs: (DONE) The plugin should enable replacing class Common.Plus with Common.(~+~)
--                    The user writes x ~+~ y and the source plugin converts it to Plus constraints
--                    BUG (FIXED): (t -> (forall m x. m ~+~ x ~ z => p) -> g) shouldn't get converted to (Plux m x z) => (t -> ... -> g)
--                         i.e. make sure variables don't escape their scope
--        (DONE) Solving those `Plus` constraints.
--                    It also computes the right unknown meta variable
--                    Eg. `Plus (x:=t) y0 ( x:=t , y := u )` will deduce y0 ~ y := u
--
--        (Done) Internalize the representations of `labX` `unLabX` primitives
--        (Done) Internal.hs to be ported into manipulating dictonary evidences

--               We are a bit sloppy with R '[ x := u ] vs R [ x := u ]. The user written types are marked as former, while plugin generated
--                    types are generated as the later. This makes eqType fail when we try to compare both of them.
--
--               Store `~<~` evidences inside the `Plus` evidences
--
--               Parameteraize the plugin with the theory
--                    Eg. Theories: 1. Rows with Unique labels  (currently implimented)
--                                  2. The most recent label in a row overwrites other labels (scoped?)
--                                  3. Non-commutative rows
--
--
plugin :: GHC.Plugin
plugin =
  GHC.defaultPlugin
    { GHC.tcPlugin        = \ _args -> Just $ API.mkTcPlugin TP.tcPlugin
    , GHC.pluginRecompile = GHC.impurePlugin
    , GHC.renamedResultAction = SP.addPlusConstraints
    }

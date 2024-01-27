module RoHsPlugin (plugin) where

import GHC.Plugins

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  putMsgS "Hello from RoHsPlugin!"
  return todo

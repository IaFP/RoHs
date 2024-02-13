module CorePlugin (install) where
import GHC.Plugins


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  putMsgS "Hello!"
  return todo

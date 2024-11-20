RoHs
----

Experimenting with row types in GHC using a plugin

- How to compile? set GHC to `9.10.1` (`ghcup tui` is your friend)
```
$ cabal configure --enable-tests
$ cabal build
```

- How to run tests?
```
$ cabal test
```

- How to run?
     - The repl way:
     ```
     $ cabal repl
     ghci> :set -XDataKinds -fplugin RoHs.Plugin
     ghci> import RoHs.Language.Lib
     ghci> import RoHs.Examples.Basic -- contains some basic examples
     ghci> ...
     ```
     - The compile way
     ```
     $ cabal run RoHs-sample-exe
     ```

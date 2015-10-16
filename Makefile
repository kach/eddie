eddie:
	ghc -O4 -package-db=.cabal-sandbox/x86_64-osx-ghc-7.10.1-packages.conf.d/ repl.hs  -o eddie


# ./eddie +RTS -p
# cat eddie.prof
# https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/profiling.html
profile:
	ghc -O4 -prof -fprof-auto -package-db=.cabal-sandbox/x86_64-osx-ghc-7.10.1-packages.conf.d/ repl.hs  -o eddie


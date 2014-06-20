doconSource = /home/mechvel/docon/2.11/docon/source
configure:
	runhaskell Setup.hs configure --ghc --prefix=${doconSource}/inst -v 

#                                     \ --enable-library-profiling

build:
	runhaskell Setup.hs build
install:
	runhaskell Setup.hs install --user

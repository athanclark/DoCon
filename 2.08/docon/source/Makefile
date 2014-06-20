ghcBinDir = /home/mechvel/ghc/6.2.2/inst/bin
#
# EDIT these three!  
# $(s) is the DoCon source directory,
# $(e) a directory the DoCon library and interface to install to.
#
s = /home/mechvel/docon/2.08/docon/source
e = $(s)/export

ghc    = $(ghcBinDir)/ghc
ghcpkg = $(ghcBinDir)/ghc-pkg


# un-comment ONE of the below three lines - the one corresponding to
# `ar -s' command equivalent in your system:
#
RANLIB = ar -s
#
# RANLIB = ranlib
# RANLIB = true

language =  -fglasgow-exts  -fallow-overlapping-instances \
                            -fallow-undecidable-instances
# this aims   
# Haskell-2-pre  =  Haskell-98 + Extension,
# Extension      =  multiparametric classes, overlapping instances 
#                   ... - the functionality preserved, though.

warnings = -fno-warn-overlapping-patterns -fwarn-unused-binds \
            -fwarn-unused-matches -fwarn-unused-imports 

idirs    = auxil:parse:lin:residue:pol:pol/factor:pol/symmfunc

HCFlags  =  $(language) $(warnings)            \
            -i$(idirs) -odir $(e) -hidir $(e)  \
            -ddump-hi-diffs                    \
            +RTS $(space) -RTS  $(extraHCOpts) 

space       = -M55m
#                   -G3 -F1.5 
extraHCOpts =
#             -O    ghcpkg=... 


pack =Package {name            = "\"docon\"",  \
	       import_dirs     = ["\"$(e)\""],    \
               source_dirs     = [],              \
               library_dirs    = ["\"$(e)\""],    \
               hs_libraries    = ["\"HSdocon\""], \
               extra_libraries = [], \
               include_dirs    = [], \
               c_includes      = [], \
               package_deps    = [\"data\"],         \
               extra_ghc_opts  = [$(extraPackOpts)], \
               extra_cc_opts   = [],                 \
               extra_ld_opts   = [] } 

extraPackOpts = $(pwarnings), $(planguage)

# `backslash' copy of $(HCFlags)
#
planguage = "\"-fglasgow-exts\"", \
            "\"-fallow-overlapping-instances\"", \
            "\"-fallow-undecidable-instances\""
pwarnings = "\"-fno-warn-overlapping-patterns\"", \
            "\"-fwarn-unused-binds\"","\"-fwarn-unused-matches\"", \
            "\"-fwarn-unused-imports\""

obj:
	if [ ! -d $(e) ]; then mkdir $(e); fi
	$(ghc) $(HCFlags) --make DExport  -package-name docon

docon:	obj
	rm -f  $(e)/libHSdocon.a $(e)/HSdocon.o
	ar -qc $(e)/libHSdocon.a $(wildcard $(e)/*.o)
	$(RANLIB)  $(e)/libHSdocon.a
	echo $(pack) | $(ghcpkg) -f $(s)/docon.conf -u -g
	$(ghcpkg) -f $(s)/docon.conf -l
#
# o. files can be extracted from the library by  ar -x 

clearO:
	mv $(e)/HSdocon.o $(e)/t
	rm -f $(e)/*.o
	mv $(e)/t $(e)/HSdocon.o 

clearT:
	rm -f $(s)/demotest/*.hi $(s)/demotest/*.o $(s)/demotest/log

clearButInstall:
	rm -f  $(s)/*.hs  $(s)/log
	rm -rf $(s)/auxil $(s)/parse $(s)/lin $(s)/residue
	rm -rf $(s)/pol   $(s)/demotest

clear:
	$(ghcpkg) -f $(s)/docon.conf -r docon
	rm -f  $(s)/docon.conf.old
	rm -rf $(e)
	rm -f $(s)/log
	rm -f $(s)/demotest/*.hi $(s)/demotest/*.o $(s)/demotest/log
	rm -f $(s)/demotest/a.out*


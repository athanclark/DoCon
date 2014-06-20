HC =  ghc

HCFLAGS =  -cpp  -hi-diffs  -ipol:lin:parse   $(EXTRA_HC_OPTS)


SRCS =  \
  Main.hs             Categ.hs              Categ1.hs            \
  Generic.hs          Matrix.hs             Fraction.hs          \
  PreludeChar.hs      PreludeInteger.hs     PreludeList.hs       \
  PreludePair.hs      PreludeRational.hs                         \
  parse/IParse.hs     parse/ParOpTab.hs                          \
  pol/ExtPol.hs       pol/GrBas.hs          pol/NF.hs            \
  pol/PP.hs           pol/Pol.hs            pol/RelBas.hs        \
  pol/UnvPol.hs       pol/VarPol.hs         pol/ExprPol.hs       \
  pol/PolGCD.hs                                                  \
  lin/StrCase.hs      lin/ToDiag.hs         lin/Det.hs

# Res_z2.hs  
# tests/ConeEqu.hs  tests/Buch1.hs      tests/Buch2.hs        
# tests/Cyclroot.hs   tests/Discrim.hs      tests/Grbastes.hs



OBJS =  \
  Main.o              Categ.o               Categ1.o             \
  Generic.o           Matrix.o              Fraction.o           \
  PreludeChar.o       PreludeInteger.o      PreludeList.o        \
  PreludePair.o       PreludeRational.o                          \
  parse/IParse.o      parse/ParOpTab.o                           \
  pol/ExtPol.o        pol/GrBas.o           pol/NF.o             \
  pol/PP.o            pol/Pol.o             pol/RelBas.o         \
  pol/UnvPol.o        pol/VarPol.o          pol/ExprPol.o        \
  pol/PolGCD.o                                                   \
  lin/StrCase.o       lin/ToDiag.o          lin/Det.o

# Res_z2.o
# tests/ConeEqu.o  tests/Buch1.o       tests/Buch2.o       \
# tests/Coneequ.o  tests/Cyclroot.o    tests/Discrim.o     \
# tests/Grbastes.o


.SUFFIXES : .o .hs

.hs.o: 
	$(HC) -c $< $(HCFLAGS)

#
all : run

run : $(OBJS)                         
	$(HC) -o $@ $(HCFLAGS) $(OBJS)

objs : $(OBJS)

tags :
	hstags $(SRCS)



depend :
	/usr/haskell/bin/i386-unknown-linuxaout/mkdependHS -- $(HCFLAGS) -- $(SRCS)

# DO NOT DELETE: Beginning of Haskell dependencies
Main.o : Main.hs
Main.o : ./PreludeChar.hi
Main.o : ./PreludePair.hi
Main.o : ./PreludeList.hi
Main.o : ./PreludeRational.hi
Main.o : ./PreludeInteger.hi
Main.o : ./Generic.hi
Main.o : ./Categ.hi
Main.o : ./Categ1.hi
Main.o : ./Matrix.hi
Main.o : lin/StrCase.hi
Main.o : lin/ToDiag.hi
Main.o : lin/Det.hi
Main.o : pol/PP.hi
Main.o : pol/Pol.hi
Main.o : pol/VarPol.hi
Main.o : ./Fraction.hi
Main.o : parse/IParse.hi
Main.o : parse/ParOpTab.hi
Categ.o : Categ.hs
Categ.o : ./Categ1.hi
Categ.o : ./Generic.hi
Categ.o : ./Matrix.hi
Categ.o : parse/IParse.hi
Categ.o : parse/ParOpTab.hi
Categ1.o : Categ1.hs
Categ1.o : ./Categ.hi
Categ1.o : ./Generic.hi
Categ1.o : ./Matrix.hi
Categ1.o : parse/IParse.hi
Categ1.o : parse/ParOpTab.hi
Generic.o : Generic.hs
Generic.o : ./PreludeList.hi
Generic.o : ./Categ.hi
Generic.o : ./Categ1.hi
Generic.o : ./Matrix.hi
Generic.o : parse/IParse.hi
Generic.o : parse/ParOpTab.hi
Matrix.o : Matrix.hs
Matrix.o : ./Categ.hi
Matrix.o : ./Categ1.hi
Matrix.o : ./PreludeList.hi
Matrix.o : ./PreludeChar.hi
Matrix.o : ./Generic.hi
Matrix.o : lin/StrCase.hi
Matrix.o : parse/IParse.hi
Fraction.o : Fraction.hs
Fraction.o : ./PreludeInteger.hi
Fraction.o : ./Categ.hi
Fraction.o : ./Categ1.hi
Fraction.o : ./Matrix.hi
Fraction.o : parse/IParse.hi
PreludeChar.o : PreludeChar.hs
PreludeChar.o : ./Categ.hi
PreludeChar.o : ./Categ1.hi
PreludeChar.o : ./Matrix.hi
PreludeChar.o : parse/IParse.hi
PreludeInteger.o : PreludeInteger.hs
PreludeInteger.o : ./PreludeChar.hi
PreludeInteger.o : ./PreludeList.hi
PreludeInteger.o : ./PreludeRational.hi
PreludeInteger.o : ./Categ.hi
PreludeInteger.o : ./Categ1.hi
PreludeInteger.o : ./Generic.hi
PreludeInteger.o : ./Matrix.hi
PreludeInteger.o : parse/IParse.hi
PreludeList.o : PreludeList.hs
PreludeList.o : ./PreludeChar.hi
PreludeList.o : ./Categ.hi
PreludeList.o : ./Categ1.hi
PreludeList.o : ./Matrix.hi
PreludeList.o : parse/ParOpTab.hi
PreludeList.o : parse/IParse.hi
PreludePair.o : PreludePair.hs
PreludePair.o : ./PreludeInteger.hi
PreludePair.o : ./PreludeList.hi
PreludePair.o : ./Categ.hi
PreludePair.o : ./Categ1.hi
PreludePair.o : ./Matrix.hi
PreludePair.o : parse/IParse.hi
PreludeRational.o : PreludeRational.hs
PreludeRational.o : ./PreludeInteger.hi
PreludeRational.o : ./Categ.hi
PreludeRational.o : ./Categ1.hi
PreludeRational.o : ./Matrix.hi
PreludeRational.o : parse/IParse.hi
parse/IParse.o : parse/IParse.hs
parse/ParOpTab.o : parse/ParOpTab.hs
parse/ParOpTab.o : parse/IParse.hi
pol/ExtPol.o : pol/ExtPol.hs
pol/ExtPol.o : ./PreludeChar.hi
pol/ExtPol.o : ./PreludeList.hi
pol/ExtPol.o : ./PreludeInteger.hi
pol/ExtPol.o : ./Categ.hi
pol/ExtPol.o : ./Categ1.hi
pol/ExtPol.o : ./Generic.hi
pol/ExtPol.o : pol/PP.hi
pol/ExtPol.o : pol/Pol.hi
pol/ExtPol.o : pol/UnvPol.hi
pol/ExtPol.o : ./Matrix.hi
pol/ExtPol.o : parse/IParse.hi
pol/GrBas.o : pol/GrBas.hs
pol/GrBas.o : ./PreludeInteger.hi
pol/GrBas.o : ./Generic.hi
pol/GrBas.o : ./Categ.hi
pol/GrBas.o : ./Categ1.hi
pol/GrBas.o : ./Matrix.hi
pol/GrBas.o : pol/PP.hi
pol/GrBas.o : pol/Pol.hi
pol/GrBas.o : pol/NF.hi
pol/GrBas.o : parse/IParse.hi
pol/NF.o : pol/NF.hs
pol/NF.o : ./PreludeInteger.hi
pol/NF.o : ./PreludeList.hi
pol/NF.o : ./Categ.hi
pol/NF.o : ./Categ1.hi
pol/NF.o : ./Matrix.hi
pol/NF.o : pol/PP.hi
pol/NF.o : pol/Pol.hi
pol/NF.o : parse/IParse.hi
pol/PP.o : pol/PP.hs
pol/PP.o : ./PreludeInteger.hi
pol/PP.o : ./PreludeList.hi
pol/PP.o : ./Categ.hi
pol/PP.o : ./Categ1.hi
pol/PP.o : ./Matrix.hi
pol/PP.o : parse/IParse.hi
pol/Pol.o : pol/Pol.hs
pol/Pol.o : ./PreludeList.hi
pol/Pol.o : ./PreludeInteger.hi
pol/Pol.o : ./Categ.hi
pol/Pol.o : ./Categ1.hi
pol/Pol.o : ./Generic.hi
pol/Pol.o : pol/PP.hi
pol/Pol.o : pol/ExprPol.hi
pol/Pol.o : pol/VarPol.hi
pol/Pol.o : pol/PolGCD.hi
pol/Pol.o : ./Matrix.hi
pol/Pol.o : pol/NF.hi
pol/Pol.o : pol/GrBas.hi
pol/Pol.o : pol/RelBas.hi
pol/Pol.o : parse/IParse.hi
pol/RelBas.o : pol/RelBas.hs
pol/RelBas.o : ./PreludeList.hi
pol/RelBas.o : ./Categ.hi
pol/RelBas.o : ./Categ1.hi
pol/RelBas.o : ./Matrix.hi
pol/RelBas.o : pol/PP.hi
pol/RelBas.o : pol/Pol.hi
pol/RelBas.o : pol/NF.hi
pol/RelBas.o : pol/GrBas.hi
pol/RelBas.o : parse/IParse.hi
pol/UnvPol.o : pol/UnvPol.hs
pol/UnvPol.o : ./PreludeInteger.hi
pol/UnvPol.o : ./Categ.hi
pol/UnvPol.o : ./Categ1.hi
pol/UnvPol.o : ./Generic.hi
pol/UnvPol.o : pol/PP.hi
pol/UnvPol.o : pol/Pol.hi
pol/UnvPol.o : ./Matrix.hi
pol/UnvPol.o : parse/IParse.hi
pol/VarPol.o : pol/VarPol.hs
pol/VarPol.o : ./PreludeChar.hi
pol/VarPol.o : ./PreludeList.hi
pol/VarPol.o : ./Categ.hi
pol/VarPol.o : ./Categ1.hi
pol/VarPol.o : pol/PP.hi
pol/VarPol.o : pol/Pol.hi
pol/VarPol.o : pol/ExprPol.hi
pol/VarPol.o : ./Matrix.hi
pol/VarPol.o : parse/IParse.hi
pol/ExprPol.o : pol/ExprPol.hs
pol/ExprPol.o : ./PreludeInteger.hi
pol/ExprPol.o : ./PreludeList.hi
pol/ExprPol.o : ./Categ.hi
pol/ExprPol.o : ./Categ1.hi
pol/ExprPol.o : ./Generic.hi
pol/ExprPol.o : pol/PP.hi
pol/ExprPol.o : pol/Pol.hi
pol/ExprPol.o : pol/VarPol.hi
pol/ExprPol.o : ./Matrix.hi
pol/ExprPol.o : parse/IParse.hi
pol/PolGCD.o : pol/PolGCD.hs
pol/PolGCD.o : ./Categ.hi
pol/PolGCD.o : ./Categ1.hi
pol/PolGCD.o : pol/PP.hi
pol/PolGCD.o : pol/Pol.hi
pol/PolGCD.o : ./Matrix.hi
pol/PolGCD.o : parse/IParse.hi
lin/StrCase.o : lin/StrCase.hs
lin/StrCase.o : ./PreludeList.hi
lin/StrCase.o : ./PreludeChar.hi
lin/StrCase.o : ./Categ.hi
lin/StrCase.o : ./Categ1.hi
lin/StrCase.o : ./Matrix.hi
lin/StrCase.o : parse/IParse.hi
lin/ToDiag.o : lin/ToDiag.hs
lin/ToDiag.o : ./Categ.hi
lin/ToDiag.o : ./Categ1.hi
lin/ToDiag.o : ./Matrix.hi
lin/ToDiag.o : lin/StrCase.hi
lin/ToDiag.o : parse/IParse.hi
lin/Det.o : lin/Det.hs
lin/Det.o : ./Categ.hi
lin/Det.o : ./Categ1.hi
lin/Det.o : ./Generic.hi
lin/Det.o : ./Matrix.hi
lin/Det.o : lin/StrCase.hi
lin/Det.o : parse/IParse.hi
# DO NOT DELETE: End of Haskell dependencies

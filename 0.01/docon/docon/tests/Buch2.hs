------------------------  DoCon  tests  --------------------------

-- Groebner bases.

-- Buchberger's  example No 2.
------------------------------------------------------------------


module  Buch2  where

import  PreludeInteger
import  PreludeRational
import  Categ
import  PP
import  Pol
import  VarPol



type  K = Rational

type  A = VarPol K 

vars = ["z","y","x"]    -- z > y > x

rtUn   = (fromInteger 1) :: K
rtZero = (fromInteger 0) :: K


unp =  cToPol rtZero lexComp rtUn          -- unity polynomial

un  = VarP unp vars

n m = (i un m)                              -- integer to  A


fr :: Integer -> Integer -> A               -- k/m  to A

fr k m =  VarP (cToPol rtZero lexComp (k%m)) vars


x = varToVarPol un "x"
y = varToVarPol un "y"
z = varToVarPol un "z"


f1 =  z*y^2  +  (n 2)*x +  (fr 1 2)
f2 =  z*x^2  -  y^2     -  (fr 1 2)*x
f3 =  -z     +  y^2*x   +  (n 4)   *x^2  +  (fr 1 4)

basis = [f1,f2,f3]

gb =  fst (grBasis "r" basis) 
                        -- the reduced Groebner basis should be:


check = [f3,g1,g2]

g1 = y^2  + 
     (fr  112 2745)*x^6  -  (fr   84  305)*x^5  - 
     (fr 1264  305)*x^4  -  (fr   13  549)*x^3  + 
     (fr   84  305)*x^2  +  (fr 1772 2745)*x    +  (fr 2 2745)   

g2 = x^7 + (fr 29 4)*x^6 - (fr 17 16)*x^4 - (fr 11 8)*x^3 + 
           (fr 1 32)*x^2 + (fr 15 16)*x   + (fr 1  4)   
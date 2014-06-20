------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey.D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Groebner bases testing.

-- The cyclic roots relations.




module  CyclRoot  where

import  PreludeInteger
import  PreludeRational
import  Categ
import  PP
import  Pol
import  VarPol


type  K = Rational
type  A = VarPol K 

vars4 =  ["x","y","z","u"]
vars5 =  ["x","y","z","u","v"]
vars6 =  ["x","y","z","u","v","t"]

rtUn   = (fromInteger 1) :: K
rtZero = (fromInteger 0) :: K

unp =  cToPol rtZero degLex rtUn
                      --?--

un  =  VarP unp vars5
             -- vars4
             -- vars6

x =  varToVarPol un "x"
y =  varToVarPol un "y"
z =  varToVarPol un "z"
u =  varToVarPol un "u"
v =  varToVarPol un "v"

{- 
f1 = x     +  y     +  z     +  u
f2 = x*y   +  x*z   +  x*u   +  y*z   +  y*u   +  z*u
f3 = x*y*z +  x*y*u +  x*z*u +  y*z*u
f4 = x*y*z*u - un
-}

f1 = x   + y   + z   + u   + v
f2 = x*y + x*z + x*u + x*v + 
     y*z + y*u + y*v + 
     z*u + z*v +
     u*v
f3 = x*y*z + x*y*u + x*y*v + x*z*u + x*z*v +
     y*z*u + y*z*v + y*u*v +
     z*u*v
f4 = x*y*z*u + x*y*z*v + y*z*u*v
f5 = x*y*z*u*v - un




basis =  [f1,f2,f3,f4,f5]
       --[f1,f2,f3,f4]
       --[f1,f2,f3,f4,f5,f6]

gb =  fst (grBasis "" basis)
       

-- check =  ?



-- gb takes      Gofer reductions 
--                       for the grBasis version of  June 16,1995.










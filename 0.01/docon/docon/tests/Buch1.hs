------------------------  DoCon  tests  --------------------------

-- Groebner bases.

-- Buchberger's  example No 1.
------------------------------------------------------------------


module  Buch1  where

import  PreludeInteger
import  PreludeRational
import  Categ
import  PP
import  Pol
import  VarPol


type  K =  Rational

type  A =  VarPol K

vars =  ["x","y","z"]

                      -- Try also   reverse vars  &  degLex  - ?
                      -------------------------------------


unp =  cToPol ((fromInt 0)::K) degRevLex ((fromInt 1)::K)
un  =  VarP unp vars

n k =  i un k

x =  varToVarPol un "x"
y =  varToVarPol un "y"
z =  varToVarPol un "z"


f1 = x^2*y^2 - z^2
f2 = x*y^2*z - x*y*z
f3 = x^3*y*z - x*z^2

basis =  [f1,f2,f3]

gb =  fst (grBasis "r" basis)  
                        -- the reduced Groebner basis should be:
       

check =  [ x^2*y^2 - z^2,        x*y^2*z - x*y*z,
           x^2*y*z - z^3,        x*z^3   - x*z^2,
           y*z^3   - z^3,        x*y*z^2 - x*z^2,
           z^4     - x^2*z^2,    x^3*z^2 - x*z^2
         ]




-- The equivalence of the Groebner bases may be checked by calling

-- map  (\f -> fst (moduloBasis "g" bas1 f))  bas2  

-- gb takes  28800  Gofer reductions 
--                       for the grBasis version of  June 16,1995.


-- HUGS-1.01,   reduce & insert :    31000 reductions 








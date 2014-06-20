------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- DoCon tests.
--
-- Groebner bases.
--
-- Deriving the inconsistency conditions for the three quadratic
-- equations of the generic form.



module  Discrim  where

import  PreludeInteger
import  PreludeRational
import  Categ
import  PP
import  Pol
import  VarPol



vars = ["x","l","h","g","f","e","d","c","b","a"]

type  K = Rational

type  A = VarPol Rational

rtUn   = (fromInteger 1) :: K
rtZero = (fromInteger 0) :: K

unp = cToPol rtZero lexComp rtUn         -- unity polynomial

un  = VarP unp vars
n2  = un+un

x = varToVarPol un "x"
l = varToVarPol un "l"
h = varToVarPol un "h"
g = varToVarPol un "g"
f = varToVarPol un "f"
e = varToVarPol un "e"
d = varToVarPol un "d"
c = varToVarPol un "c"
b = varToVarPol un "b"
a = varToVarPol un "a"

f1 =  x^2*a + x*b + c
f2 =  x^2*d + x*e + f
f3 =  x^2*g + x*h + l 


basis = [f1,f2,f3]

gb =  fst (grBasis "r" basis)       -- the reduced Groebner basis 


  --  gb  and  check   should be equivalent:

  --  w  (map  (\f-> fst (moduloBasis "g" bas1 f)) bas2) 
  --                                                 ->  [0,...,0]

  -- The inconsistency conditions are the polynomials from  gb
  -- that do not depend on  x.
       


check =  
          -- this should be the polynomials to the number of 21.
 [ 
   f1, f2, f3,

   x*e*a - x*d*b + f*a - d*c,

   x*f*a - x*d*c + f*b - e*c,    
                                                     
   x*f*d*b - x*e*d*c - f^2*a + f*e*b + f*d*c - e^2*c,

   f^2*a^2 - f*e*b*a - n2*f*d*c*a + f*d*b^2 + e^2*c*a - e*d*c*b +   
     d^2*c^2, 

   x*h*a - x*g*b + l*a - g*c,

   l*f*a^2 - l*d*c*a - h*f*b*a + h*e*c*a - g*f*c*a + g*f*b^2 -       
     g*e*c*b + g*d*c^2,

   x*h*d - x*g*e + l*d - g*f,

   l*e*a - l*d*b - h*f*a + h*d*c + g*f*b - g*e*c,                    

   x*g*f*b - x*g*e*c - l*f*a + l*d*c + h*f*b - h*e*c,

   l*f*d*a - l*d^2*c - h*f*d*b + h*e*d*c - g*f^2*a + g*f*e*b +       
     g*f*d*c - g*e^2*c,

   l*f*d^2*b - l*e*d^2*c + h*f^2*d*a - h*f*e*d*b - h*f*d^2*c +       
     h*e^2*d*c - g*f^2*e*a - g*f^2*d*b + g*f*e^2*b + n2*g*f*e*d*c
     - g*e^3*c,

   x*l*a  -x*g*c +l*b  -h*c,

   x*l*g*b  -x*h*g*c  -l^2*a + l*h*b +l*g*c  -h^2*c, 


   l^2*a^2 - l*h*b*a - n2*l*g*c*a + l*g*b^2 + h^2*c*a - h*g*c*b +   
     g^2*c^2,

   l^2*d*a - l*h*d*b - l*g*f*a + l*g*e*b - l*g*d*c + h^2*d*c -       
     h*g*e*c + g^2*f*c,

   x*l*d - x*g*f + l*e - h*f,

   x*l*g*e - x*h*g*f - l^2*d + l*h*e + l*g*f - h^2*f,

   l^2*d^2 - l*h*e*d - n2*l*g*f*d + l*g*e^2 + h^2*f*d - h*g*f*e +   
     g^2*f^2 
 ]





-- HUGS-1.01,  reduce & insert :     607000 reductions




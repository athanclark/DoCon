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
-- Deriving the Cone equation  from the polynomial 
-- parameterization of the cone.



module  ConeEqu  where

import  PreludeInteger
import  PreludeRational
import  Categ
import  PP
import  Pol
import  VarPol



type  K = Rational

type  A =  VarPol K

vars =  ["u","v","x","y","z"]

unp =  cToPol ((fromInt 0)::K) lexComp ((fromInt 1)::K)
un  =  VarP unp vars
n2  =  un+un

u = varToVarPol un "u"
v = varToVarPol un "v"
x = varToVarPol un "x"
y = varToVarPol un "y"
z = varToVarPol un "z"


f1 =  u^2    - v^2  - x
f2 =  n2*u*v - y
f3 =  u^2    + v^2  - z

basis =  [f1,f2,f3]

gb =  fst (grBasis "r" basis)
                          -- the reduced Groebner basis should be:


check =  [ u^2   -  (inv n2)*x  -  (inv n2)*z,
           u*v   -  (inv n2)*y,
           v^2   +  (inv n2)*x  -  (inv n2)*z,
           u*x   -  u*z         +  v*y,
           x^2   +  y^2         -  z^2,
           u*y   -  v*x         -  v*z
         ]
                 -- the 5-th polynomial is the required equation.


-- gb takes  35600  Gofer reductions 
--                       for the grBasis version of  June 16,1995.



-- HUGS-1.01,  reduce&insert variant:   41.000 reductions 







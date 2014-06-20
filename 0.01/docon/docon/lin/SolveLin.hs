module  SolveLin  where


import  Categ
import  Matrix





solveLinSys ::  
            SyzygySolvableRing a =>
            String -> Matrix a -> Matrix a -> (Matrix a, Matrix a)
         -- mode      mM          mA           p         ker



-- General solution  of the linear system  mM * x = mA  

-- over the ring  a   -  SO FAR,  a  should be Euclidean.

-- mM  is   n x m,    x  is   m x 1,    mA  is  n x 1

-- n = height(mM) = height(mA),   width(mA) = 1.

-- p    is a partial solution:  mM * p = mA
--      (p, mA  are the matrices    ).

-- ker  is the matrix whoes columns form  the  basis of 
-- solutions of the Homogeneous system.      


-- -- solveLinSys  M [A]  [1]  -->    &P  [&Kernel]  |  "failed"       


-- M, A  are the matrices over R.                     

-- Column  matrix   &P   is the   Partial  Solution,  
-- Columns of the matrix  &Kernel  constitute the  basis of 
-- solutions of the Homogeneous system.      

-- Height(P) = Height(Kernel) = Height(A).            

-- The Default value of A is  {{&zr}...{&zr}}  which is the zero 
-- column over R having the same Height as  M. 

-- "1"   means to return  Partial Solution  Only.



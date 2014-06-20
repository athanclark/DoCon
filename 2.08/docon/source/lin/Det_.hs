--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module Det_   -- Determinant of matrix.
              --
              -- LinAlg  reexports all needed from here.

  (det, det_euc, maxMinor, delColumn) 

where
import List     (genericLength)

import DPrelude (Z, sortE, product1, del_n_th, invSign, compBy, 
                 showsWithDom 
                )
import SetGroup (zeroS                                             )
import Ring0_   (CommutativeRing(), EuclideanRing(..)              ) 
import VecMatr  (mainMtDiag,mtHeight,mtWidth,isZeroMt,isStaircaseMt)
import Stairc_  (toStairMatr_euc                                   )





--------------------------------------------------------------------
delColumn :: Z -> [[a]] -> [[a]]
delColumn    i =  map (\xs-> del_n_th i xs)

maxMinor :: Z -> Z -> [[a]] -> [[a]]
                                  -- pre-matrix obtained by deleting
                                  -- of  i-th row  and  j-th column  
maxMinor i j rows = delColumn j $ del_n_th i rows

--------------------------------------------------------------------
det :: (CommutativeRing a) => [[a]] -> a

    -- Determinant of square  matrix.
    -- ATTENTION: 
    -- it simply  *expands det(M) by the row*  (after moving ahead
    -- the rows which contain more of zeroes)  - O(n!) maximal cost.
    --
    -- For the  Euclidean case,  it is also provided  det_euc 
    -- - Gauss method.

det []          = error "det [] \n"
det ([]:_)      = error "det ([]:_) \n"
det m@((a:_):_) =  
  let  
    (zr,n,width) = (zeroS a, mtHeight m, mtWidth m)

    expandByRow [[a]]      = a
    expandByRow (row:rows) = dt 1 '+' row rows zr
                                    -- initiate det = zr, sign= '+',
                                    -- for i=1 to n ...
    dt _ _     []      _    res = res 
    dt i sign  (a:row) rows res = 
      if  
        a==zr  then  dt (i+1) (invSign sign) row rows res
                                                        -- skip zero
      else
        let  minorDet = expandByRow $ delColumn i rows
        in
        case sign of '+' -> dt (i+1) '-' row rows (res + a*minorDet)
                     '-' -> dt (i+1) '+' row rows (res - a*minorDet)
    ----------------------------------------------------------------
  in 
  if  n < 1  ||  n/=width  
             then
               error $ ("det mM,"++) $ showsWithDom a "mtHead mM" ""
                             "\nmM should be non-empty and square\n"
  else
    let  addNum row = (row, genericLength $ filter (==zr) row)

         pairs              = map addNum m
         (sortedPairs,sign) = sortE (flip (compBy snd)) pairs
         dt                 = expandByRow $ map fst sortedPairs
    in
    if  sign=='+'  then  dt  else  - dt




--------------------------------------------------------------------
det_euc :: (EuclideanRing a) => [[a]] -> a

  -- Determinant of square matrix over a Euclidean ring
  -- computed via the Gauss reduction to the staircase form.
  -- For the field case, its maximal cost is O(n^3) of divisions.

det_euc []          = error "det_euc [] \n"
det_euc ([]:_)      = error "det_euc ([]:_) \n"
det_euc m@((a:_):_) = case  (zeroS a, mtHeight m, mtWidth m)  of

  (zr,n,width) ->
    if 
      n < 1  ||  n /= width
      then  
           error $ ("det_euc mM,"++) $ showsWithDom a "mtHead mM" ""
                             "\nmM should be non-empty and square\n"
    else
      if  isZeroMt m  then  zr
      else
        if  isStaircaseMt m  then  product1 $ mainMtDiag m
        else
          let  (s,_,sign) = toStairMatr_euc "" m []
               dt         = product1 $ mainMtDiag s
          in
          if  sign=='+' then  dt  else  - dt

 ;







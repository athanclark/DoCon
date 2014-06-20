---------------------  DoCon  tests  -----------------------------



module  GrBasTes  where

import  Categ
import  Matrix




moduloBasisTest :: (SyzygySolvableRing a, Num a) =>
                                      String -> [a] -> a -> String
moduloBasisTest  mode xs y = 
  let
    (r,qs) =  moduloBasis mode xs y

    mess1  =  "\n(r,qs) = moduloBasis mode xs y   \n"

    [y1]   =  rowMatrMul qs (transpose [xs])

    mess2  =  if  y==(y1+r)  then  "y = r + qs*xs  O.K.\n"
              else              "ERROR:  y /= r + qs*xs \n"
  in
    mess1++mess2





grBasisTest :: (SyzygySolvableRing a, Num a) =>
                                           String -> [a] -> String
grBasisTest  mode xs = 
  let
    (gs,mt) =  grBasis mode xs

    pr1 = "\n Groebner basis  gs  for  xs  and the transforamtion" 
          ++ " matrix  mt  are being computed, \n\n"

    xsM =  matrMul mt (transp (Mt [xs]))

    pr2 =  " xs  multiplies by  mt,   \n\n"

    reducts =  map  (\f-> fst (moduloBasis "" gs f))  xs

    pr3 =  " xs  are being reduced by  gs. \n\n"
   
    pr4 =  
      if  xsM==(transp (Mt [gs]))  then  
            " (mt*(transp (Mt [xs])))==(transp (Mt [gs]))  O.K.\n"
       else
         " ERROR:  (mt*(transp (Mt [xs])))/=(transp (Mt [gs])) \n"
    
    pr5 =  if  (all (\x-> x==(zero x)) reducts)  then
                            " gs  reduces  xs  to zeroes  O.K. \n"
           else             " ERROR: non-zero among reducts"
  in
    pr1++pr2++pr3++pr4++pr5








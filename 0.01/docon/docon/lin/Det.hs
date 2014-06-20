------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Determinant of matrix.





module  Det ( det, minor, delColumn )    where

import  Categ
import  Categ1
import  Generic
import  Matrix
import  StrCase
import  IParse




delColumn  i xss =  map (del_n_th i) xss


------------------------------------------------------------------
minor ::  Integer -> Integer -> Matrix a -> Matrix a
          -- i       j          m

                       -- the matrix obtained from  m  by deleting
                       -- of  i-th row  and  j-th column             

minor  i j (Mt rows) =  Mt (delColumn j (del_n_th i rows)) 

------------------------------------------------------------------





det ::  (SyzygySolvableRing a, Num a) =>  String -> Matrix a -> a
                                       -- mode      m


-- The Determinant  of a Square matrix  m   of  n x n  size.

-- mode =  "" | "s" | "g" 

--  "s"  means  m  is staircase (a very "fast" case).
--  "g"  means applying the Gaussian method  (if  a  is Euclidean)
--       which takes  O(n^3)  of field operations  (in the case of
--       field).
--   otherwise - Expansion:
--       the rows are first sorted, so that the ones  having  more 
--       zeroes go ahead,  and then  det  is computed directly, by 
--       expanding it recursively by the row  
--       -  O(n!)  operations in the worst case.    



det  mode m =  
  let  
     n = matrHeight m   
  in 
    (case 
      (n==(matrWidth m), n<1, mode=="" || mode=="g" || mode=="s")
     of
      (False, _   , _    ) ->  error "det:  matrix is not square"
      (_    , True, _    ) ->  error "det:  empty matrix"
      (_    , _   , False) -> 
                       error "det:  mode = \"\" | \"g\" | \"s\"  "
      _                    ->
        let  (Mt rows) = m
             x         = head (head rows)
             zr        = zero x
        in
          (case  ( euclidean x, mode, matrElem (/= zr) m )  of
          
            (_  , _  , [] ) ->  zr
            (_  , "s", _  ) ->  genProduct (mainMatrDiag m)
            (Yes, "g", [y]) -> 
                     let  (s,_,sign) = toStairMatr "" m (Mt [])
                          dt         = genProduct (mainMatrDiag s)
                     in
                              if  sign=='+' then  dt  else  (- dt) 
            _               ->  
              let  addNum row  = 
                      ( row, genericLength ((filter (==zr)) row) )
                   pairs       =  map addNum rows
                   sortedPairs =  
                             sortP (\p q -> (snd p)>(snd q)) pairs
              in
                   expandRow  zr (map fst sortedPairs)
          )
    )
      where

      expandRow  _  [[a]]      =  a
      expandRow  zr (row:rows) =  dt  1 '+'  row rows  zr 
                                  -- initiate  det = zr, sign= '+'
        where                                   -- for i=1 to n ... 
        dt  _ _     []      _    res =  res 
        dt  i sign  (a:row) rows res = 

          if  a==zr  then   dt  (i+1) (invSign sign) row rows res
                                                     -- skip zero
          else
            let  minorDet =  expandRow zr (delColumn i rows)
            in
              case  sign  of
                 '+' ->  dt  (i+1) '-' row rows (res + a*minorDet)
                 '-' ->  dt  (i+1) '+' row rows (res - a*minorDet)

;


-- permanent ...

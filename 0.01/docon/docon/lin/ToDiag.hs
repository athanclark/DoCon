------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Diagonalizing of matrix.





module  ToDiag  where

import  Categ
import  Categ1
import  Matrix
import  StrCase
import  IParse





toDiagMatr ::  SyzygySolvableRing a =>
                     String -> Matrix a -> Matrix a -> Matrix a ->
                  -- mode      m           t0          u0

                     (Matrix a, Matrix a, Matrix a) 
                  --  d         t         u



-- Diagonal form  d  of matrix  m    - only Euclidean case so far.

-- t, u   are the unimodular protocol matrices for the row and the
--        column transformation respectively.                 

-- t0 or u0 =  Mt []   is a shorthand for the unity matrix of
--                     appropriate size.

-- mode =  "" | "s"      
--                   "s"  means  m  is  *staircase*.  In this case
--                   the computation is simpler.

-- Let  h = matrHeight(m),  wd = matrWidth(m).
-- If  t0,u0  are the (h x h) and (wd x wd)  unity  matrices, then  
--                     t * m * transp(u) = d  
-- where the (lower) non-zero part of  d is square and diagonal.

-- This means we first apply the elementary transformation to  the
-- rows.  If  m  is invertible over  a,  we always achieve the 
-- diagonal form by this.    If it is not  achieved,  the  similar 
-- transformations are applied to the *columns*.

-- Often the returnd  u  is unity (only row transformations used).
-- This holds, say, when  m  is *invertible*.

-- Remark: the determinant can only change sign under the above 
-- transformations.

-- This function is used in solving linear systems.



toDiagMatr  mode m t u =

  (case  matrElem (const True) m   of

    []  ->  error "toDiagMatr:  empty matrix"
    [x] ->  
      let  zr = zero x
      in
        (case  matrElem (/= zr) m   of
          []  ->  (m,t,u)
          [y] ->  
            let  un         =  unity y
                 (Mt rowsM) =  m
                 t0         =  if  t/=(Mt [])  then  t
                               else           scalMatr rowsM un zr
                 u0       =  if  u/=(Mt [])    then  u
                             else      scalMatr (head rowsM) un zr
                 hm         =  matrHeight m  
                 wm         =  matrWidth  m  
                 ht         =  matrHeight t0  
                 wt         =  matrWidth  t0  
                 wu         =  matrWidth  u0  
            in
              (case  (hm==ht, wm==wu, mode==""||mode=="s")  
               of
                (False, _    , _    ) ->
                               error( "toDiaglMatr mode m t u :  " 
                                      ++ " height(m)/=height(t) "
                                    )
                (_    , False, _    ) ->
                                error( "toDiagMatr mode m t u :  " 
                                       ++ " width(m)/=width(u) "
                                     )
                (_    , _    , False) ->
                        error "toDiagMatr:  mode == \"\" | \"s\" "
                _                     ->
                  if  (euclidean un)/=Yes  then  
                             error( "toDiagMatr:  only Euclidean " 
                                    ++ " domain handle so far "
                                  )
                  else
                    let  
                      (s'',t'',_) =  
                          (case  mode  of
                            "s"-> toStairMatr "u" m t0
                            "" -> 
                                let (s',t',_)= toStairMatr "" m t0
                                in  
                                    toStairMatr "u" s' t'
                          )
                    in
                      dm  True s'' t'' u0 
              )
        ) --case  matrixElement (/= zr)
  )
    where
          -- Here  s  is a staircase matrix.
          -- If it is not diagonal, then  transp(s)  it brought to
          -- the staircase form  -  this corresponds to the column 
          -- elementary transformations of  s -  and so on,  until 
          -- the diagonal matrix is  obtained   ( even  number  of 
          -- `transp' have to be applied).

    dm  even s t u =  case  (even, isDiagMatr s)  of

        (True , True ) -> ( s       ,  t,  u )
        (False, True ) -> ( transp s,  t,  u )
        (True , False) -> 
                      let  (s',u',_) = toStairMatr "" (transp s) u
                      in
                           dm  False s' t u'
        (False, False) -> 
                      let  (s',t',_) = toStairMatr "" (transp s) t
                      in
                           dm  True s' t' u



test_toDiagMatr ::  SyzygySolvableRing a => Matrix a -> String

test_toDiagMatr  m =
  let
    (Mt rows) = m
    zr        = zero (head (head rows))
  in 
    case   matrElem (/= zr) m 
    of
      []  -> error "test_toDiagMatr:  non-zero matrix needed"
      [x] -> let
               (d,t,u) =  toDiagMatr "" m (Mt []) (Mt [])
               m_by_tu =  t*m*(transp u)
               d_str   =  w d ""
               eq_str  = 
                 if  m_by_tu==d  then  
                                 "\n\n  t*m*transp(u) = d   O.K. "
                 else            "\n\nERROR:  t*m*transp(u) /= d "
             in
               "\nDiagonal form  d = \n\n" ++ (d_str++eq_str)




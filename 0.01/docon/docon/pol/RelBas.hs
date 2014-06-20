------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





-- Implementation for  SyzygySolvableRing  on  Pol a.   

-- Case  a  is a EUCLIDEAN ring.

-- syzygyBasis  is defined via  polRelBasis for  Polynomials.




------------------------------------------------------------------
{-                        REMARKS


             polRelBasis_euc  mode fs  ->  rs


fs :: [Pol a],
rs :: [ [Pol a] ]   is a list of rows, 
each row  r = [r1..rn]  is a linear relation for  fs: 
                                              f1*r1+...+fn*rn = 0.
rs  form a basis for the linear relation module (over (Pol a)).

Requirements:  length(fs) > 1,   No zeroes among  fs.


METHOD.

1. Case  mode = "g"   which means  fs  is a Groebner basis.

   In this case any  s-polynomial  sPol(fi,fj)  reduces to zero by
by  fs,  and it is known that the Coefficient vectors of this  re-
duction summed with the  comlementary monomial factors for  fi, fj
form a basis of syzygy module for fs.  This is expressed below  by 
the local function  grCase.
  grCase  creates a copy of  fi-s  supplied with the vectors:
fvs = [fv1..fvn],  fvi = (fi,vi)   where  vi  is the  i-th  vector 
from the unity matrix over  Pol a.
  Let  m1,m2  are the factors for the s-polynomial of fi,fj,

(Pol [], qs) =  moduloBasis "g" fs (m1*fi-m2*fj),

Then   m1*vi - m2*vj - qs   is a relation for (i,j).


2. mode = ""   is the general case.

   It reduces to "g" case as follows.

   1) (gs,mt) = grBasis "" fs  
                          produces the matrix  mt  such that  
                          mt*transp(fs) = gs  is a Groebner basis.
   2) map (moduloBasis "g" gs) fs   
                     produces  mt1  such that  mt1*transp(gs) = fs
   3) rels1  = mt1*mt - unityMatrix                  
   4) relsGr = grCase gs        makes the basic relations for  gs. 
   5) result = rels1 ++ (relsGr*mt)   
                 - the second matrix is set "under" the first one.

   The matrices are multiplied over  Pol a. 

   Theoretical hint:
   -----------------
   relsGr*mt  are the ported relations for the Groebner basis.
   rels1      are the relations caused by the fact that  mt   and  
              mt1  may be not presizely mutually  inverse  module 
              homomorphisms.
   
********************************************************
Possible optimization:
it seems, not all of s-polynomials have to be reduced in 
"g" case ...
********************************************************

-}
------------------------------------------------------------------   






module  RelBas   where


import  PreludeList
import  Categ
import  Categ1
import  Matrix
import  PP
import  Pol
import  NF
import  GrBas
import  IParse --?





polRelBasis_euc :: ( SyzygySolvableRing a, Num a)
                   =>   
                   String -> [Pol a] -> [[Pol a]]
                 --mode     

polRelBasis_euc  mode fs =  
  let
    --------------------------------------------------------------
    mVecMul m v =  map (mPolMul m) v
    vecAdd      =  binOpList polAdd
    vecSub  u v =  vecAdd  u (map polNeg v)

    zeroPol  =  zero  (head fs)
    unityPol =  unity (head fs)     
    --------------------------------------------------------------
    grCase  fs =  gr  fs (initVectors zeroPol unityPol fs)
      where
      gr  gs [fv]     = []  
      gr  gs (fv:fvs) = (map (relForPair gs fv) fvs)++(gr gs fvs)
        where
        relForPair  gs (f,u) (g,v) =
          let 
            (_,m1,m2) = sPol f g  
          in
            case 
              polNF "" gs (polSub (mPolMul m1 f) (mPolMul m2 g))
            of
                                        -- m1*u-m2*v = qs.gs  =>
                                        -- (m1*u-m2*v-qs).gs = 0
              (Pol [], qs) ->  
                  vecSub (vecAdd qs (mVecMul m2 v)) (mVecMul m1 u)

              _            -> error( "\n(polRelBasis_gr fs):  fs "
                                     ++ " is Not a Groebner basis"
                                   )
    --------------------------------------------------------------
    generalCase  prop fs =
      let
        (gs,mt)  =  grBas "" prop fs
        fBy_g_s  =  map (polNF "" gs) fs
      in 
        if  any (not.isZeroPol.fst) fBy_g_s  then
                   error( "polRelBasis_euc:  wrong Groebner basis"
                          ++ "  or  polNF "
                        )
        else
          let  mt1         =  Mt (map snd fBy_g_s)
               (Mt m1m)    =  matrMul mt1 mt
               unityMatrix =  scalMatr m1m unityPol zeroPol
               (Mt rels1)  =  matrSub (Mt m1m) unityMatrix
               relsGr      =  grCase gs 
               (Mt rsGr_m) =  matrMul (Mt relsGr) mt
          in
               filter  (not.(all isZeroPol)) (rels1++rsGr_m)
    --------------------------------------------------------------

  in
    (case  mode   of

      "g" ->  grCase fs 

      ""  ->  if  (field (lc (head fs)))==Yes  then 
                                            generalCase "field" fs
              else                          generalCase "euc"   fs

      _   ->  error "(syzygyBasis mode fs):  mode = \"\" | \"g\" "
    )














------------------------------------------------------------------
------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.02
--
--  Copyright  Serge Mechveliani,    2002
------------------------------------------------------------------
------------------------------------------------------------------




-- Demonstration, test, benchmarks.




{- -----------------------------------------------------------------
Resultant of polynomials from  k[t][x],
interpolation for computing determinant over  K[t],
K = Z/(q)  a finite field.

Involved tools: pValue,upollInterpol, Vandermonde, extendFieldToDeg.

For  f,g <- K[t][x],  resultant f g  is computed over  K = Z/(q)
via
(G) Gauss-like method over k[t] - repeated remainder taking,
(I) by interpolation            - find sufficiently many values for
                                det for matrices over K and rebuild.

If  bound(deg(resultant f g)) >= q,  then the interpolation finds 
first a prime  p <- K[y]  of sufficient degree, extends K  to  
F = K[y]/(p),  and the linear system is solved over F instead of 
over K. The result projects back to  K[t].
-}

--------------------------------------------------------------------



module T_detinterp (t_detinterp_)
where
import List       (genericTake                 )
import DPrelude   (Z, eFM, ctr, smParse        )
import Categs     (ResidueE(..)                )
import RingModule (eucIdeal, upField, upEucRing)
import VecMatr    (resultantMt                 )
import Z          (dZ                          )

import Pol        (PolLike(..), UPol(..), cToUPol, upolInterpol,
                   det_upol_finField
                  )
import LinAlg     (det_euc)






--------------------------------------------------------------------
type K = ResidueE Z   -- for the field Z/(q)
type T = UPol K
type X = UPol T


t_detinterp_ :: 
     Z -> String -> String -> ([Bool], [T], String-> Bool, X, [[T]])

t_detinterp_ q sf sg = 
  let     
    iI  = eucIdeal "bef" q [] [] []   -- iI = ideal(q) in Z
    a1  = Rse 1 iI dZ
    dK  = upField a1 eFM
    unT = cToUPol "t" dK a1  :: T
    dT  = upEucRing unT eFM

    as@(a0:_:a2:a3:a4:_) = map (ctr a1) [0..(q-1)]


    -- interpolation in K[t] only  ---------------------------------
    -- Parse polynomial f take its values in (deg f)+1 points, 
    -- interpolate by these values, compare the result to  f.
  
    interp :: String -> Bool
    interp    sf     =             
                      let  f   = smParse unT sf
                           d   = deg f
                           as' = genericTake (d+1) as
                           ps  = [(a,pValue f [a])| a<- as']
                           f'  = upolInterpol unT ps
                      in  f==f'

    sfExamples = ["1", "2*t+3", "(2*t^2 +3*t +4)^3", "t^10+t^9+t"]

    ----------------------------------------------------------------
    -- resultant f g  via interpolation,  f, g from K[t][x]

    unX       = cToUPol "x" dT unT  -- of X = T[x]
    [f,g]     = map (smParse unX) [sf,sg]
    (dgF,dgG) = (deg f, deg g)
    (fv ,gv ) = (pToVec (dgF+1) f, pToVec (dgG+1) g)
    mM        = resultantMt fv gv
    dt        = det_upol_finField [] mM 
    dt'       = det_euc mM
    ----------------------------------------------------------------
  in
  ([all interp sfExamples, dt==dt'], [unT,dt], interp, unX, mM)


  -- Test:  tuple51 (t_detinterp_ q sf sg)   -- choose q,sf,sg
  --
  -- Demo.
  -- For example,  let  interp = tuple53 $ t_detinterp_ 53 "x" "x"
  --               in   interp "(t^2+t+2)^9 + t^4 + 6"      --> True
  --
  -- Performance test:
  --   let  mM = tuple55 $ t_detinterp_ q sf sg
  --                            -- large f,g  given by strings sf,sg
  --   in   det_upol_finField [] mM





{- performance test  -----------------------------------------------

q = 97
f = (x^3 + t*x + t  ) * ((t^2+1)*x^4 + 3*x^3 + t^2*x^2 + t^3+t+2   )
g = (x^2 + t*x + 2*t) * (t*x^4       + x^3  + (t^2+2)*x^2 + x + 2*t)

deg_x f, deg_x g =  7, 6,
deg_t f, deg_t g =  4, 3,

resultant = t^38 + 23*t^37 + 61*t^36 + 46*t^35 + 73*t^34 + 
            ... 
            + 10*t^9 + 22*t^8 + 65*t^7 + 43*t^6 + 34*t^5 + 18*t^4


Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

May 1999.  Hugs98-March99, SmallResidue  Interpolation  Gauss method
                           ------------                 over k[t]   
                                   q = 97| 17.7         ?

August 1999.  ghc-4.04, DoCon-2, -O 
                                   q = 97|   1.7      70
                                       11|   6.5
                                        5|   7.5      75

-}














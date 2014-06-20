-- DoCon-2.04  Demonstration, test, benchmark.


-- Test and benchmark for  ResidueE Z.

{- -----------------------------------------------------------------
Mainly, it consists of forming of

          [(x,y,divide_m x y) |  x,y <- Z/(b) ]                  (D)
          and testing  x == y*q  
          for each obtained triplet of kind (x,y,Just q)

- we call this all "test D".
This tests the arithmetic correctness.

The performance can be compared by commenting out the lines after
`test' in the final `in'.

The ideal preparation  eucIdeal "bef" ...  
costs here much less then (D).
--------------------------------------------------------------------
-}



module T_reseuc (t_rse_)
where
import List       (genericTake                                     )
import Maybe      (isJust                                          )
import DPrelude   (PropValue(..),Z,sum1,ctr,eFM,tuple33, lookupProp)
import Categs     (Subring(..), Property_Subring(..), ResidueE(..) )
import RingModule (Ring(..), eucIdeal                              )
import SetGroup   (MulSemigroup(..)                                )
import Z          (dZ                                              )
import Residue    () --instances for ResidueE Z

type R = ResidueE Z

t_rse_ =
  let  
    b  = 100 :: Z
    iI = eucIdeal "bef" b [] [] [] 
    r0 = Rse 0 iI dZ
    rs@(_:r1:r2:r3:r4:_) = map (ctr r0) [0..(b-1)]  :: [R]

    (_,rR) = baseRing r0  eFM
    propsR = subringProps rR
    tab    = [(x,y,divide_m x y)|  x<-rs, y<-rs]
    tabJ   = filter (isJust .tuple33) tab
    eqs    = [x==(y*q) | (x,y,Just q) <- tabJ]
    test   = and eqs
    size   = quot (b^2) 6              -- this is to reduce the test
                                       -- - for slow systems
    test_small = and $ genericTake size eqs
    propsTest  = [lookupProp nm propsR | 
                              nm <- [IsField,HasZeroDiv,HasNilp,PIR]
                 ] == [No,Yes,Yes,Yes]
  in  
  (test_small, test, propsTest, sum1 rs)
                                       -- Benchmark:  tuple42 t_rse_



{- ghc
main = 
    let  (_,test,psTest,sumRs) = t_rse_  
    in  
    putStr
      ( -- un-comment the needed part

       ("test    =  "++)$ shows test $('\n':   )$

      -- ("propsTest  =  "++)$ shows psTest $ ('\n':   )$
      -- ("sumRs      =  "++)$ shows sumRs  $ ("\n\n"++)$
      -- ("qM's==qMEs =  "++)$ shows eq     "\n"
      )
-}





{- Timing ----------------------------------------------------------

tuple42 t_rse_     (`test')
                         
Heap, Stack  are the minimal values at which the given minimal 
             running time is achieved.

Platform: i586, 166MHz,

August 1999
ghc-4.04    DoCon-2, Rse-Z, -O    test:   0.7 sec  -M33k -K4

hugs-98-March-99                         13.6

ghc/hugs speed = 38
-}










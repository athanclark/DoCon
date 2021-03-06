--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.07
--
--  Copyright  Serge Mechveliani,    2003
--------------------------------------------------------------------
--------------------------------------------------------------------




module FAAGBas_ (faaSPol)

-- Groebner basis for non-commutative polynomials over a Field.

where
import Maybe      (fromJust        ) 
import DPrelude   (tuple31, tuple32)
import SetGroup   (MulSemigroup(..)) 
import RingModule (GCDRing(..)     )
import UPol_      (lc              )
import FAA0_





--------------------------------------------------------------------
faaSPol :: 
        (GCDRing a) => FAA a -> FAA a -> (FAA a, FAAMon a, FAAMon a)
                       -- f     g         sp     m1        m2
  
  -- S-polynomial for  non-zero non-commutative polynomials:
  --                                                sp = f*m1 - m2*g
  -- It also returns the corresponding
  -- complementary faa-monomial factors  m1, m2.

faaSPol f g = 
             ((snd $ faaMonFAAMul m1 f) - (fst $ faaMonFAAMul m2 g),
              m1, m2
             )
             where
             (a,b)   = (lc f, lc g)
             d       = gcD [a,b]
             (m1,m2) = ((b/d,q'), (a/d,p'))
             p'      = fromJust $ tuple31 $ divide_m2 p r
             q'      = fromJust $ tuple32 $ divide_m2 q r
             (p,q)   = (faaLPP f, faaLPP g)
             r       = snd $ freeMGCD p q     -- p = p'*r, q = r*q'
 

 







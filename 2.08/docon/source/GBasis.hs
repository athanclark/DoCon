--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module GBasis  

  -- The head module for the functions related to  Groebner basis 
  -- of polynomials over a  Euclidean ring.
  --
  -- See  PolNF_*, GBas*_.*, Polrel*  for implementation.


  (polNF, polNF_v, polNF_e, polNF_ev, test_polNF, underPPs, 
                                                     -- from PolNF_
   faaNF,                                            -- from FAANF_
   gBasis, gBasis_e, isGBasis, isGBasis_e,           -- from GBas_
   polRelGens, polRelGens_e, algRelsPols             -- from Polrel_
  )  

where
import PolNF_  (polNF,polNF_v,polNF_e,polNF_ev,test_polNF, underPPs)
import FAANF_  (faaNF                                              )
import GBas_   (gBasis, gBasis_e, isGBasis, isGBasis_e             )
import Polrel_ (polRelGens, polRelGens_e, algRelsPols              )

 ;













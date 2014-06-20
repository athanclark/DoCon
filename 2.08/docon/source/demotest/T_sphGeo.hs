------------------------------------------------------------------
------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.04
--
--  Copyright  Serge Mechveliani,    2002
------------------------------------------------------------------
------------------------------------------------------------------




-- Demonstration and test.


-- Arithmetics of the field  Q(S)  of rational functions on sphere  
-- S: x^2+y^2+z^2 = 1.


module T_sphGeo (t_sphGeo_)
where
import DPrelude   (PropValue(..), Z, eFM, ct, ctr, smParse        )
import Categs     (Subring(..), Property_Subring(..), ResidueE(..))
import RingModule (Ring(..), upEucRing, upField, eucIdeal         )
import Z          (dZ                                             )
import Fraction   (Fraction(..)                                   )
import Pol    
       (PolLike(..),UPol(..),Pol(..), lexPPO, cToUPol, varP, cToPol)


type P  = Pol Z         -- P  = Z[x,y] 
type F  = Fraction P    -- F  = Q(x,y),   Q rational
type PF = UPol F        -- PF = F[z]

-- K = Q(S) = PF/(p)  is the required field, 
--                          where  p = x^2 + y^2 + z^2 - 1  <- PF.
-- K  is the algebraic representation of the surface.

t_sphGeo_ =   
  let  
    o2          = lexPPO 2
    p1          = cToPol o2 ["x","y"] dZ 1  :: P  -- 1   of P
    [x,y]       = varPs 1 p1                      -- x,y in P
    unF         = p1:/p1                    :: F
    dF          = upField unF eFM           -- domain F
    unPF        = cToUPol "z" dF unF        :: PF
    dPF         = upEucRing unPF eFM
    p           = smParse unPF "y^2+x^2+z^2 - 1"  :: PF
    iI          = eucIdeal "be" p [] [] [(p,1)]  
    k1          = Rse unPF iI dPF  -- 1 of K
    (_,rK)      = baseRing k1 eFM
    kProps      = subringProps rK
    isFieldTest = (lookup IsField kProps)==(Just Yes)
    z           = varP unF unPF              -- z <- PF
    pToPF       = ctr p .(:/ p1)             -- P -> F[z]
    z'          = ct k1 z                    -- z,x,y  in K
    [x',y']     = map (ct k1 .pToPF) [x,y]   --

    -- try computations in K:

    f  = k1       / (k1   + z'  )  -- they
    f' = (k1 - z')/ (x'^2 + y'^2)  -- should be equal
  in  
  ([isFieldTest, f==f'],   -- test
   p,  rK                  -- demo
  )

 ;


{- 
     ("kProps          = "++)$ shows kProps $ ("\n\n"++)$
     ("p               = "++)$ shows p      $ ("\n\n"++)$
     ("1/(1+z)  in K   = "++)$ shows f      $ ("\n"++)$
     ("(1-z)/(x^2+y^2) = "++)$ shows f'     $ ("\n"++)$
to produce 
kProps = [(IsOrderedRing,Unknown)... (PIR,Yes), (IsField,Yes) ...]
p      = z^2 + (x^2 + y^2 - 1)
1/(1+z)  in K  = (((-1)/(x^2 + y^2))*z + ((1)/(x^2 + y^2)))
...
-}










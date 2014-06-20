--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




-- Demonstration and test.
--
-- Constructing an algebraic cubic extension of a field.
-- Computing in such extension.


module T_cubeext (cubicExt, t_cubeext_) 
where

-- cubicExt a b k   builds automatically the radical extension tower
--                  k -- k(d) -- E = k(d)(u,v,r)
--
-- for the given field  k,  and the coefficients  a, b   of 
-- irreducible polynomial  f = t^3 + a*t + b  over k,  a /= 0. 
--
-- d    stands for the square root of discriminant, 
-- r                    square root of  -3, 
-- u,v                  Cardano cubic radicals. 
--
-- cubicExt  applies the operation  root 2 x  for  x <- k  returning
-- Just (Just y),  y<-k such that  y^2 = x  if there is such y in k. 
--
-- cubicExt  performs as follows. 
--
-- Assigns  D  =  discriminant  -4*a^3 - 27*b^2  of  f
--          dd =  minimal polynomial for  d  which is here 
--                      d^2-D   if  squareRoot(D)  in  k  is Nothing
--                      d - squareRoot(D)  (in k)   otherwise;
--
-- Builds the field  k1 = k(d) = k[d]/(dd) and the ring B= k1[u,v,r]
-- Puts  r,u,v,uv  to be the defining polynomials for the  
-- corresponding field elements 
--                 r :  r^2  + 3  
--                 u :  u^3  - (3/2)*d*r + (27/2)*b 
--                 v :  v^3  + (3/2)*d*r + (27/2)*b 
--                 uv:  u*v  + 3*a ;  
--
-- Finds   gs = GroebnerBasis [u,v,uv,r]  in  B;
-- Builds  E = B/I  for  the ideal  I = Ideal(gs)  in B,  this  E
-- representing an extension of  k1  containing the roots of  f;
-- Defines the _roots_ of  f  in  E  by the Cardano formulas: 
--                  x = (1/3)*(u + v)  
--                  y = (1/6)*(r*v - r*u - u - v)  
--                  z = (1/6)*(r*u - r*v - u - v)
--
-- After this, we may compute various expressions of xi in  E  - see
-- below.



import qualified Data.Map as Map (empty, lookup)

import Prelude hiding (minimum, maximum)
import DPrelude   
import Categs     
       (CategoryName(..), Domain1(..), Domains1, Subring(..), 
        Ideal(..), Property_Subring(..), Property_Ideal(..),
        Property_IdealGen(..), ResidueE(..)
       )
import SetGroup   (MulSemigroup(..), times, isZero)
import RingModule 
import VecMatr    (Vector(..), Matrix(..), transp)
import Fraction   (Fraction(..)                  )
import Pol 
import Residue (Residue(..), ResidueI(..), resIdeal, gensToIdeal)
import GBasis  (algRelsPols                                     )


type Q    = Fraction Z       -- rational numbers - for coefficients
type A  k = UPol k           -- for  A  = k[d]
type K1 k = ResidueE (A k)   --      K1 = k[d]/(d_equation)
type B  k = Pol (K1 k)       --      B  = K1[u,v,r]
type E  k = ResidueI (B k)   --      E  = B/I = k1(u,v,r) 

                      -- wait OI fix ? **
cubicExt :: (Field k, FactorizationRing (UPol k)) 
            =>        
            k -> k -> Domains1 k -> (Domains1 (E k), [E k], k-> E k)
         -- a    b    dK             dE              [x,y,z] kToE

  -- Building the Extension  E  of the field  k  to include the 
  -- roots  x,y,z  of  irreducible  f = t^3 + a*t + b  
  -- according to the Cardano formulas,
  -- It returns the 
  --   domain description dE for the field E,
  --   elements  [x,y,z]  of  E  representing the above roots,
  --   embedding function k -> E.
  --
  -- RESTRICTION:  char(k) /= 2, 3.
  --
  -- Example:  let {un = 1:/1 :: Q;  dK = upField un Map.empty}
  --           in  cubicExt un (-un) dK 
  --
  -- builds the extension (dE, [x,y,z], kToE) expressing 
  --                                    Q -- Q(rootsOf(t^3-t+1)) = E


cubicExt a b dK =  
  let
    [unK, n4, n27] = map (fromi a) [1, 4, 27] -- integer images in k

    unA   = cToUPol "d" dK unK             -- 1 of A = k[d]
    dA    = upEucRing unA Map.empty        -- domain A
    dv    = varP unK unA                   -- "d" as element of A
    discr = - n4*a^3 - n27*b^2
  
    dd = case  root 2 discr  of      -- dd  is the minimal equation
                                     -- for the root of discriminant
      Just (Just rad) -> dv - (ctr unA rad)   
                                           -- linear equation in "d"

      Just Nothing    -> dv^2 - (ctr unA discr)      -- regular case
      _               -> 
            error ("cubicExtension a b _ _:  could not find whether"
                   ++" the discriminant is a square in  k \n"
                  )
    ddI     = eucIdeal "be" dd [] [] [(dd, 1)]
    unK1    = Rse unA ddI dA   
    dK1     = upField unK1 Map.empty         -- domain of  K1 = k(d)
    d       = ctr unK1 dv       -- d <- K1 satisfies the equation dd
    varsUVR = ["u", "v", "r"] 
                         -- variables for the cubic radicals over K1

        -- To obtain more clear formulas for the roots xi of f in E,
        -- we define certain special ordering on the power products 
        -- of  u,v,r:  compare according to the weight list
        -- [[1,1,0],[1,0,0],[0,0,1]]:
        --
    uvrComp (Vec [u, v, r]) (Vec [u', v', r']) =
                           case 
                               compare (u+v) (u'+v')  
                           of
                           EQ -> lexListComp compare [u, r] [u', r']
                           v  -> v

    o   = (("deg2lex", 3), uvrComp, [])
    unB = cToPol o varsUVR dK1 unK1
    dB  = upGCDLinSolvRing unB Map.empty  -- domain B
    d'  = ct unB d                        -- d image in B
    [u', v', r']  = varPs unK1 unB
    [m2, m3, m27] = map (times unB) [2, 3, 27] 
                                              -- integer images in B
    (m3_2, m27_2) = (m3/m2, m27/m2)
    kToB          = ctr unB . ctr unK1 . ctr unA
    [a', b']      = map kToB [a, b]            -- cast a,b to B

    radicals = [r'^2 + m3,                    -- equations for u,v,r
                u'^3 - m3_2*d'*r' + m27_2*b',
                v'^3 + m3_2*d'*r' + m27_2*b',
                u'*v'+ m3*a'
               ]                              -- :: [B k]
    (gs, _)    = gxBasis radicals
    (dI, iRad) = gensToIdeal gs [] [(IsGxBasis, Yes)] 
                                   [(IsMaxIdeal, Yes)] dB Map.empty
    unE  = Rsi unB (iRad, dI) dB
    kToE = ct unE . kToB
    dE   = upField unE Map.empty           -- E = B/iRad = K1(u,v,r)
    [u, v, r] = map (ctr unE) [u', v', r']       -- as elements of E

             -- Finally, the roots  x1,x2,x3  of  f  are represented
             -- by Cardano formulas in the radicals  u,v,uv,r :

    [e3, e6] = map (times unE) [3, 6]
    roots    = [(u + v)/e3,
                (r*v - r*u - u - v)/e6,
                (r*u - r*v - u - v)/e6
               ]
  in
  (dE, roots, kToE)




t_cubeext_ =       -- Example. Build the extension of Q = Fraction Z
  let              --          with  f = t^3 - t + 1

    un                = 1:/1 :: Q
    (a, b)            = (-un, un)         
    dK                = upField un Map.empty
    (dE, roots, kToE) = cubicExt a b dK 
    [x, y, z]         = roots 
    Just (D1Ring rE)  = Map.lookup Ring dE      -- look into ring E
    propsE            = subringProps rE         -- - for curiosity
    isFieldTest       = (lookup IsField propsE) == (Just Yes)

    -- Example of calculation in E.

    discr  = - (4:/1)*a^3 - (27:/1)*b^2
    n1     = fromi x 1                     -- 1 in E
    fRoots = [x^3 - x + n1| x <- roots]  
                                     -- it should be [0,0,0], 0 of E
    fRootsTest  = all isZero fRoots
    vieteValues = [x+y+z, x*y+x*z+y*z, x*y*z]     
                                        -- testing Viete relations:
    vtCheck = map kToE [0:/1, a, -b]    -- this should give [0,a,-b]
    vtTest  = vieteValues == vtCheck   

    -- For these a,b, the Galois theory says E'= k1(x,y,z) = k1(x)
    -- and E':k1 = 3.  
    -- In particular,  y  has to express as a quadratic polynomial
    -- in  x  over  k1.  Let us test this.
    -- x,y  are the polynomial residues of  x',y' <- B = k1[u,v,r] 
    -- modulo the ideal I.  So we have to find the algebraic 
    -- relations between x',y' in B modulo I.
    
    [x', y'] = map resRepr [x, y]
    Just hs  = idealGens (resIdeal x)
    o        = lexPPO 2
    rels     = algRelsPols hs ["y", "x"] o [y', x']  
        -- 
        -- the generators of algebraic relations for  y',x' viewed 
        -- modulo Ideal(hs) in  k1[u,v,r],  the relations to display
        -- in variables "y","x"

    relCol = transp $ Mt [rels] Map.empty  
                                           -- to print matrix nicely 

    -- rels  consists of the source cubic equation on  x  
    -- and a non-trivial expression of  y  via  x:
    --            y + ((3/23)*d)*x^2 + ((9/46)*d + 1/2)*x - (2/23)*d
    relCheck = 
           map (smParse (head rels))
               ["x^3 - x + 1",
                "y + ((3/23)*d)*x^2 + ((9/46)*d + 1/2)*x - (2/23)*d"
               ]
    relTest =  rels == relCheck
  in  
  ([isFieldTest, fRootsTest, vtTest, relTest],    -- test, benchmark

   propsE, [roots, fRoots, vieteValues], relCol   -- demo
  ) 





{- ----------------------- 
  putStr 
    ("f(root)-s, Viete relation, relation generator tests = "++)$ 
                                 shows (fRootsTest,vtTest,relTest)$
                                                        ("\n\n"++)$
     ("(a,b) = "++) $ shows (a,b) $ ("\n\n"++)$
     ("discr = "++) $ shows discr $ ("\n\n"++)$
                        -- we see, discriminant is not a square in k
     ("properties of E = "++)$ shows propsE $      ("\n\n"++)$
     ("roots           = "++)$ shows roots $       ("\n\n"++)$
     ("f(roots)        = "++)$ shows fRoots $      ("\n\n"++)$
     ("vieteValues     = "++)$ shows vieteValues $ ("\n\n"++)$
     ("algebraic relations between y,x: \n"++) $ shows arelsCol "\n"
    )
-}





{- Timing ----------------------------------------------------------

Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

March 1999,  DoCon-2, -Onot,  ghc-4.02,  -M9m          0.87
                      -O                               0.56
   -- REPEAT it for  tuple41 t_cubeext_

April 1999.   Hugs-98-March-1999,  Z = Int (?),  17Mbyte heap  13.6

September 1999.  ghc-4.04,  DoCon-2, Z = Integer, -O            0.6  
-}
--------------------------------------------------------------------


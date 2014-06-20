--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module Pfact1_ 

  -- Extension of a finite field.
  -- Efficient methods for  det              for matrix over k[x],  
  --                        resultant(f,g),  f,g from k[x],
  --                                               k a finite field.
  -- This is also used in factoring in  k[x,y].
  --
  -- All needed from here is reexported by Pol.

  (extendFieldToDeg, det_upol_finField, resultant_1_upol_finField)

where
import qualified Data.Map as Map (empty)

import List (transpose, (\\), genericLength, genericTake)

import Prelude hiding(maximum)

import DPrelude (InfUnn(..), Z, sum1, ct, ctr, mapmap, showsWithDom)
import Categs   (Domains1, OSet(..), ResidueE(..), Subring(..),
                 OpName_Subring(..), Operation_Subring(..)
                )
import SetGroup   (Set(..), unity, zeroS, isZero)
import RingModule (Ring(..), FactorizationRing(..), Field(),
                   PIRChinIdeal(..), eucIdeal, upEucRing, upField,
                   logInt
                  )
import VecMatr    (mtHead, mtHeight, mtWidth, resultantMt      )
import ResEuc0_   (Residue(..)                                 )
import UPol_      (PolLike(..), UPol(..), lc, cToUPol, upolMons)
import UPol0_     (upolInterpol                                )
import LinAlg     (det_euc                                     )
import Pfact0_    (vecLDeg                                     )






--------------------------------------------------------------------
extendFieldToDeg :: 
  Field k => UPol k -> Domains1 (UPol k) -> Z ->
                   (ResidueE (UPol k), Domains1 (ResidueE (UPol k)))

  -- Extension  F  of the field  k  of the given degree  d > 1:
  --
  --            s -> sDom -> d  --> (u,domF)
  --
  -- k     is given by the sample polynomial  s  over  k.
  -- sDom  is the domain description for  s,  setting it with  empty
  --         will cause its forming by new with upEucRing.
  --
  -- u     is the unity of  F = k[x]/(p),   where  p <- k[x] 
  --         is the found irreducible polynomial of sample  s,
  --         deg r = d.
  -- domF  is the domain description of F  - upField.
  --
  -- So far, this is only for a  *finite field*.
  -- METHOD:  find first  p  of degree  d  in the list (primes s)...
  --          Its cost bounds with  O( |k|^(d+1) * d^3 ).
  --          It is usable for small  d.


extendFieldToDeg s sDom d =
  if
    d < 2 then 
         error $ ("extendFieldToDeg samplePol sDom "++) $ shows d  $
                                      (":    d > 1 expected.\n"++) $
                 showsWithDom s "samplePol" "" "\n"
  else
  let  p:_ = dropWhile ((< d) . deg) $ primes s
       iI  = eucIdeal "be" p [] [] [(p, 1)] 
       unF = Rse (unity s) iI $ upEucRing s sDom
  in  
  (unF, upField unF Map.empty)

--------------------------------------------------------------------
det_upol_finField :: 
              Field k => [ResidueE (UPol k)] -> [[UPol k]] -> UPol k
                         -- ext                 mM   

  -- The degree cost method to compute  det M  over  k[x]  for a
  -- finite field  k.   
  -- For M = (fij...) of size  m,  r = sum [ri|..],  
  --                               ri = max [deg fij| j..],
  -- deg det(M) <= r,  
  -- the cost of  det  is bounded with  O( r^4*m^3*|k|^2 ).  
  --
  -- Method:  interpolation over an extension F of k,  |F| > r.
  --
  -- ext =    [s]   - F is given by its sample element s,
  --       or []    - s will be built if necessary.
  --
  -- Extend k to F = k[t]/(p),  p irreducible, 
  -- choose different  a0..ar  in  F  and  find  di = det M(ai) 
  --   for each i via usual Gauss method;
  -- restore  det M  from  di  by interpolation formula.
  -- p  is found by searching among the prime polynomials starting
  -- from degree 2 (if |k| <= r)  - the primality test applies less
  -- than  r  times to polynomials of degree less than
  -- 1 + (log r  by |k|).
  -- Optimisation:
  -- before interpolation,  interpTab  creates the table of det on
  -- ai  by grouping first  ai  into the orbits of isomorphism ^q.
  -- Then, in each orbit, d = det(M(a))  is computed once, the other
  -- det(aj)  are found as  d^(q^j).


det_upol_finField ext mM = 
  let
    ----------------------------------------------------------------
    f@(UPol _ a v dK) = mtHead mM
    (zr, un, zrX, tM) = (zeroS a, unity a, zeroS f, transpose mM)
    degMatr           = sum1 . map (vecLDeg 0)
    hasZeroRow        = any (all (== zrX))
    substInMatr mM a  = mapmap (\ f -> pValue f [a]) mM
    toCoef f          = if  isZero f  then  zr  else  lc f
                                         -- applied to constant only
    r = min (degMatr mM) (degMatr tM)  -- deg det(M) <= r
    (setK  , rK      ) = (snd $ baseSet a dK, snd $ baseRing a dK)
    (cardK , opK     ) = (osetCard setK, subringOpers rK)
    (Just q, Just wpK) = (subringChar rK, lookup WithPrimeField opK)
    listK              = case osetList setK  
                         of
                         Just xs -> xs
                         _       ->
                            error $ 
                              msg "Listing not found in OSet of k\n"

    unT       = cToUPol "t" dK un
    dT        = upEucRing unT Map.empty      -- T = k[t],  F = T/(p)
    (unF, dF) = case (ext, cardK) of 

            (e:_, _    ) -> (unity e, upField e Map.empty)
            (_  , Fin n) -> extendFieldToDeg unT dT ((logInt n r)+1)

    (zrF, iI)  = (zeroS unF, resPIdeal unF)
    (setF, rF) = (snd $ baseSet unF dF, snd $ baseRing unF dF)
    Just wpF   = lookup WithPrimeField $ subringOpers rF
    listF      = case osetList setF  
                 of
                 Just xs -> xs
                 _       -> 
                   error $ msg 
                     "Listing not found for finite extension of k\n"

    toF a = Rse (ctr unT a) iI dT    -- k -> F
    fromF = lc . resRepr   -- applied only to  Rse constNonZeroPol..

    toOverF f = UPol [(toF a, e) | (a, e) <- upolMons f] unF v dF
                                                     -- k[x] -> F[x]
    fromOverF fR = ct f [(fromF r, e) | (r, e) <- upolMons fR]
    (ff, fM)     = (toOverF f, mapmap toOverF mM)
    ----------------------------------------------------------------
    -- build interpolation table:  extList may be listK or listF

    interpTab zr' extList frobe mM = 
      let
        un'   = unity zr'
        listQ = zr': (lst un')   -- prime field
                  where 
                  lst e = if e == zr' then [] else  e: (lst (e+un'))
        
        -- take r+1 elements from extList grouping them in orbits 
        -- of isomorphism (^q):  singletons++[orbit',orbit''..]

        qPowers x = (frobe x): (qPowers $ frobe x)
        singls    = [[x] | x <- listQ]
        orbits    = 
                if r < q then  genericTake (r+1) singls
                else
                singls ++ 
                (takeEnough (r+1-q) $ moreOrbits (extList \\ listQ))
          where
          moreOrbits []     = []
          moreOrbits (b:bs) = orb:(moreOrbits (bs \\ orb))
                               where
                               orb = b:(takeWhile (/= b) $ qPowers b)
        takeEnough _ []       = []
        takeEnough n (o:orbs) =
                          if n < 1 then []
                          else         
                          let lo = genericLength o
                          in   
                          if n <= lo then [genericTake n o]
                          else            o:(takeEnough (n-lo) orbs)

        appDetValues (b:bs) = (b, d): (zip bs $ qPowers d)
                                      where
                                      d = det_euc $ substInMatr mM b
      in                           
      concat $ map appDetValues orbits
    ----------------------------------------------------------------
                               -- this section is for error messages
    (hM, wM) = (mtHeight mM, mtWidth mM)            
    msg      = msg0 . msgA . msgExtDom . msgHeadM      
    msg0     = ("det_upol_finField ext mM,"++) . 
              ("\next =   "++) .shows ext .
              ("\nmM  is  "++) .shows hM .(" x "++) .shows wM .
              ("  matrix over  A = k[_]"++)
    msgA = 
          case (mM,ext)  
          of
          ((f:_):_, _  ) -> (",\nA =  "++) . showsDomOf f 
          (_      , s:_) -> case  pirCIBase $ resPIdeal s
                            of
                            f -> (",\nA =  "++) .showsDomOf f
          _              -> ('.':)

    msgExtDom = case ext of

        []  -> id
        s:_ -> ("\nThe given extension of  k  is  "++) .showsDomOf s
                  
    msgHeadM = case mM of

            (f:_): _ -> ("\nmtHead mM =  "++) . shows f . ("\n\n"++)
            _        -> ("\n\n"++)
    ----------------------------------------------------------------
  in
  case (mM, hasZeroRow mM || hasZeroRow tM, r, cardK) 
  of
  ([]  , _   , _, _       ) -> error $ msg$ "mM = []     \n" 
  ([]:_, _   , _, _       ) -> error $ msg$ "mM = ([]:_) \n" 
  (_   , True, _, _       ) -> zrX
  (_   , _   , 0, _       ) -> case mapmap toCoef mM  
                               of
                               cM -> ctr f $ det_euc cM
  (_   , _   , _, UnknownV) ->
                             error $ msg "Failed to find  card(k)\n"
  (_   , _   , _, Fin n   ) -> 
      if  
        n > r  
      then 
        upolInterpol f $ interpTab zr listK (fst $ frobenius wpK) mM
      else  
      fromOverF $ upolInterpol ff $ 
                        interpTab zrF listF (fst $ frobenius wpF) fM

--------------------------------------------------------------------
resultant_1_upol_finField ::
     Field k
     => 
     [ResidueE (UPol k)] -> UPol (UPol k) -> UPol (UPol k) -> UPol k
     -- ext

  -- resultant f g,   f,g  from  k[t][x],  k  a finite field,
  -- ext  is as in  det_upol_finField

resultant_1_upol_finField  ext f g =
  if
    pIsConst f || pIsConst g
  then
    error $ ("resultant_1_upol_finField  ext f g"++) $
            ("\nf =  "++) $ shows f $ showsWithDom g "g" "" 
            ":\nPositive  deg f, deg g  required\n"
  else
  det_upol_finField ext (resultantMt (pToVec n f) (pToVec m g))
                                     where
                                     {n = (deg f)+1;  m = (deg g)+1}

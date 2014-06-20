--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------






module Pfact3_ ()   -- Instances of  FactorizationRing  for  k[x,y]
                    --
                    -- All needed from here is reexported by  Pol.
where
import Data.FiniteMap (addToFM)

import List       (genericDrop, genericLength, genericSplitAt)

import DPrelude   (PropValue(..), and3, eFM, lkp, showsWithDom, ct,
                   sortBy, compBy
                  )
import Categs     (Dom(..),CategoryName(..),Domain1(..),Subring(..),
                   FactrRingTerm(..), Property_FactrRing(..)
                  )
import SetGroup   (isFiniteSet, inv)
import RingModule (FactorizationRing(..), Field(), isField,
                   isPrimeIfField, upEucRing
                  )
import Permut     (Permutation(..), permutRepr, applyPermut)
import VecMatr    (Vector(..)                              )
import UPol_      (PolLike(..), UPol(..), upolMons, cToUPol, 
                   ppoComp, lexPPO
                  )
import Pol_       (Pol(..), polMons, reordPol, toUPol, fromUPol, 
                   headVarPol, fromHeadVarPol, polPermuteVars,
                   polDegs
                  )
import Pfact__    (factorUPol_finField )
import Pfact2_    (factorOverFinField_2)






--------------------------------------------------------------------
-- More  FactorizationRing instances  for  UPol, Pol
--
-- SO FAR, 
-- DoCon performs the  polynomial factorization  and  primality
-- test in  K[x1..xn]  only when 
--                                n < 3   AND  K is a finite field.



--------------------------------------------------------------------
instance (Field k) => FactorizationRing (UPol (UPol k))
  where
  -- specialization for  k[x][y],  k  a Prime Finite Field

  primes f = error $ ("primes samplePol,"++) $
                     showsWithDom f "samplePol" ""
                     ("\nCannot handle, so far. \nIn what order "++
                      "has one to list primes in k[x][y] ?\n"
                     )

  factor f =  
    let
      dK = dom $ sample f
    in
    (case  (lkp dK Set, lkp dK Ring)
     of
       (Just (D1Set s), Just (D1Ring rC)) -> ft (isFiniteSet s) rC
       _                                  -> error msg
    )
    where
    msg = ("factor f,"++) $ showsWithDom f "f" "R[_][_]"
          "\nR has to contain a Prime Finite Field description\n"

    ft isFin rC = 
      case  (isFin,isField rC,isPrimeIfField rC,subringChar rC)
      of
        (Yes,Yes,Yes,Just _) -> factorOverFinField_2 f
        _                    -> error msg


  baseFactrRing f dm =
    let
      aDom = dom $ sample f
    in
    (case  (lkp dm FactorizationRing, lkp aDom Set)
     of
       (Just (D1FactrR r), _             ) -> (dm, r)
       (_                , Just (D1Set s)) ->
                                 ftr (isFiniteSet s) $ lkp aDom Ring

       _                                   -> (dm, error msg)
    )
    where
    msg = ("baseFactrRing samplePol currentDom,"++) $
          showsWithDom f "samplePol" "R[_][_]"
          "\nR has to contain a Prime Finite Field description\n"

    ftr  No    _                  = (dm, error msg)
    ftr  _     Nothing            = (dm, error msg)
    ftr  isFin (Just (D1Ring rC)) = 
                     case  and3 (isField rC) (isPrimeIfField rC)  of
  
      No   -> (dm, error msg)
      cond -> (addToFM dm FactorizationRing $ D1FactrR r, r)
        where
        r = FactrRingTerm {factrRingProps =
                                       [(WithFactor   ,wF),
                                        (WithIsPrime  ,wF), --so far
                                        (WithPrimeList,No)  --so far
                                       ]
                          }
        wF = and3 isFin cond 


--------------------------------------------------------------------
instance (Field k) => FactorizationRing (Pol k)
  where
  primes f = error $ ("primes samplePol,"++) $ 
                     showsWithDom f "samplePol" ""
                     ("\nCannot handle, so far. \nIn what order"++
                      " has one to list primes in  k[x1..xn] ?\n"
                     )

  factor f = 
    --
    -- reduce to the case of  1 <= d1 <= d2 ..<= dn,  di = deg_xi f.
    -- Method.
    -- Bring to lexicographic order, making  f';
    -- find permutation  pm'  on power product  (PP)  which makes 
    -- degrees ordered  d1' <= d2' .. <= dn';
    -- apply  pm'  to each PP obtaining  f'';
    -- cut the initials in each PP in f'' corresponding to zero d'i 
    -- and thus obtain  fr  (free of dummy variables);
    -- factor  fr  to  [(g,k) | ...];
    -- convert each  g  to the initial domain of  f:  prepend zero
    -- pp-part, permute pp-s back,  bring monomial list to initial
    -- ordering.
    let
      (n, ds)  = (genericLength vars, polDegs [] f)
      (d's,pm) = unzip $ sortBy (compBy fst) $ zip ds [1..]
                                               -- d1' <= d2'..<= dn'
      pm'       = permutRepr $ inv $ Pm pm
      (o',cp)   = (lexPPO n, ppoComp o)
      f'        = reordPol o' f
      f''       = polPermuteVars pm' f'       --polDegs [] f'' = d's
      zn        = genericLength $ takeWhile (==0) d's
      (zvs, nzvs)  = genericSplitAt zn vars
      (zeropp,o'') = (map (const 0) zvs, lexPPO (n-zn))

      fr = Pol (map restrictMon $ polMons f'') a o'' nzvs aDom
               where
               restrictMon (a,Vec js) = (a, Vec $ genericDrop zn js)
      back g =
         ct f $ sortBy cpm [(b, Vec $ applyPermut pm (zeropp++js)) |
                            (b, Vec js) <- polMons g
                           ]                where
                                            cpm (_,p) (_,q) = cp q p
    in
    (case  (pIsConst f, ds==d's, zn)
     of
       (True, _   , _) -> []
       (_   , True, 0) -> factorMonot f        -- di ordered and > 0
       _               -> [(back g, k) | (g,k) <- factorMonot fr]
    )
    where
    (a,o,vars,aDom) = (sample f, pPPO f, pVars f, dom f) 

    factorMonot f = 
      (case  
           vars       -- here  1 <= d1 <= d2 ..<= dn,  di = deg_xi f
       of
         [_]   ->
            [(fromU p, k) | (p,k) <- factorUPol_finField $ toUPol f]
         [x,y] -> viaUPolUPol x y$ unzip$ upolMons$ headVarPol eFM f
         _     -> 
             error $ ("factor f...reduced to (factorMonot fr),"++) $ 
                     showsWithDom f "fr" "R[...]" 
                     ("\nOnly a Finite Field  R  can do so far, "++
                      "and the number of variables LESS than 3\n"
                     )
      )
      where
      (a,o,vars,aDom) = (sample f, pPPO f, pVars f, dom f)

      fromU p = Pol ms c o vs d  where  Pol ms c _ vs d = fromUPol p

      -- convert from R[x,y] to  (R[y])[x]  (UPol.UPol),  factor and 
      -- convert back:
      viaUPolUPol x y (cs,es) =
                 [(fromUU p,k) |
                  (p,k) <- factorOverFinField_2 $ UPol mons' aY x dY
                 ]
        where
        mons'    = zip (map toUPol cs) es  
        aY       = cToUPol y aDom a
        aY'      = fromUPol aY
        dY       = upEucRing aY eFM
        fromUU f =                              -- R[y][x] -> R[x,y]
             let  (cs,es) = unzip $ upolMons f
                  mons'   = zip (map fromUPol cs) es
             in   reordPol o $ fromHeadVarPol $ UPol mons' aY' x eFM


  baseFactrRing f dm =
    let
      aDom = dom f
    in
    (case  (lkp dm FactorizationRing, lkp aDom Set)
     of
       (Just (D1FactrR r), _             ) -> (dm, r)
       (_                , Just (D1Set s)) ->
                                 ftr (isFiniteSet s) $ lkp aDom Ring
 
       _                                   -> (dm, error msg)
    )
    where
    msg = ("baseFactrRing samplePol currentDom,"++) $
          showsWithDom f "samplePol" "R[...]"
          ("\nCan handle so far only with LESS than 3  variables,\n"
           ++"and  R  has to contain a  Finite Prime Field  term\n"
          )
    ftr  No    _                  = (dm, error msg)
    ftr  _     Nothing            = (dm, error msg)
    ftr  isFin (Just (D1Ring rC)) = 
                     case  and3 (isField rC) (isPrimeIfField rC)  of
  
      No   -> (dm, error msg)
      cond -> (addToFM dm FactorizationRing $ D1FactrR r, r)
        where
        r = FactrRingTerm {factrRingProps =
                                       [(WithFactor   ,wF),
                                        (WithIsPrime  ,wF), --so far
                                        (WithPrimeList,No)  --so far
                                       ]
                          }
        wF = and3 isFin cond 

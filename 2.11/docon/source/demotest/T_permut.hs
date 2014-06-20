--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




-- Demonstration, test, benchmark. 
--
-- Permutations.


module T_permut (t_permut_)
where
import qualified Data.Map as Map (empty)

import List (nub, genericLength)

import DPrelude   (InfUnn(..), Z, sum1, factorial)
import Categs     (OSet(..))
import SetGroup   (Set(..), unity)
import RingModule (GCDRing(..))
import Permut     (Permutation(..), permutCycles)

t_permut_ :: Z -> ([Bool], Permutation -> Bool)
t_permut_    n =
  let
    un      = Pm [1 .. n]      -- unity permutation
    setG    = snd $ baseSet un Map.empty
    Just ps = osetList setG
    cardG   = case osetCard setG  
              of
              Fin c -> c
              _     -> 
                error (("t_permut_ "++) $ shows n $
                       (":\nwrong cardinality for base set of "++) $
                       show un 
                      )
    cycle p = p: (cyc (p*p))  -- cyclic subgroup <p>
                     where
                     cyc x = if x == p then [] else  x:(cyc (p*x))

    testp :: Permutation -> Bool
    testp    p           = 
           let 
             (cyclicG_ofP, cycs) = (cycle p, permutCycles p)
             cardCG              = genericLength cyclicG_ofP :: Z
           in  
           cardCG <= cardG  &&  cardCG > 0   &&
           elem (unity p) cyclicG_ofP        &&  
           (nub cyclicG_ofP) == cyclicG_ofP  &&
           (sum1 $ map Pm cycs) == p         &&
           (lcM $ map genericLength cycs) == cardCG  
  in
  ([cardG == factorial n, all testp ps],   -- test, cost test, demo
   testp                                   -- extra demo
  )






{- cost test  ------------------------------------------------------


Test:  fst $ t_permut_ n   -- [cardG == factorial n, all testp ps]
       -> [True, True]

Platform:  Linux Debian, PC i586, 166MHz, 32 Mbyte RAM. 

May 1999.     Hugs98-March, Int,  20Mbyte heap   n = 6|  10 sec
                            ---                      7| 102 

August 1999.  ghc-4.04  DoCon-2, Integer, -O,            space
                                 -------
                                         n = 6|   0.8 sec  -M33k -K4
                                             7|   9.0      same
                                             8|  90.0      same


June 2001.  ghc-5.00.2  DoCon-2.02, Integer, -Onot,   
            T_permut 
            interpreted | compiled with -Onot 
         6|   1.1           1.0
         7|  11.0           9.4
         8| 111.0          96.3

            -O -fvia-C -O2-for-C,   
            T_permut 
            interpreted | compiled with -Onot | compiled with 
                                                -O -fvia-C -O2-for-C
         6|    0.9           0.8                   
         7|    8.8           7.3                  7.1
         8|   88.6          75.6
-}







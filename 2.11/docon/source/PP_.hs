--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module PP_   

  -- Operations on the Power Products.
  --
  -- See  Manual `pol.pp',  Pol.hs.
  --
  -- All needed from here is  reexported by  Pol.

  (isMonicPP, ppLcm, ppComplement, vecMax, ppMutPrime, ppDivides, 
   lexComp, lexFromEnd, degLex, degRevLex, ppComp_blockwise, 

   PowerProduct, PPComp   -- from Categs
  )

where
import List     (genericLength, genericSplitAt, sum) 
import DPrelude (Z, CompValue, lexListComp         )
import Categs   (PowerProduct, PPComp              )
import SetGroup (AddMonoid(), zeroS                )
import VecMatr  (Vector(..), vecRepr, vecHead      )
import Z        ()




--------------------------------------------------------------------
-- imported:  type PowerProduct = Vector Z
--            type PPComp       = Comparison PowerProduct
  
                  
isMonicPP :: PowerProduct -> Bool
isMonicPP =  (< 2) . genericLength . filter (/= 0) . vecRepr

vecMax, ppLcm ::  Ord a => Vector a -> Vector a -> Vector a

vecMax v = Vec . zipWith max (vecRepr v) . vecRepr
                            
ppLcm = vecMax        -- Least Common Multiple of the power products

{-# specialize vecMax :: Vector Z -> Vector Z -> Vector Z #-}

ppComplement :: PowerProduct -> PowerProduct -> PowerProduct
ppComplement    u               v            =  (ppLcm u v) - u

vecMutPrime :: AddMonoid a => Vector a -> Vector a -> Bool
vecMutPrime                   v        =  
 
    and . zipWith (\ x y-> (x == z || y == z)) (vecRepr v) . vecRepr
                                               where
                                               z = zeroS $ vecHead v

{-# specialize vecMutPrime :: Vector Z -> Vector Z -> Bool #-}


ppMutPrime, ppDivides :: PowerProduct -> PowerProduct -> Bool

ppMutPrime = vecMutPrime    -- "power products are Mutually Prime"

ppDivides p q = all (>= 0) $ vecRepr (q-p)   -- "p divides q"



--------------------------------------------------------------------
-- Some usable admissible comparisons for power products ***********


lexComp, lexFromEnd, degLex, degRevLex :: PPComp 

lexComp v = lexListComp compare (vecRepr v) . vecRepr

lexFromEnd v = 
       lexListComp compare (reverse $ vecRepr v) . reverse . vecRepr

degLex  p@(Vec ns) q@(Vec ms) =  case  compare (sum ns) (sum ms)  
                                 of
                                 EQ -> lexComp p q
                                 v  -> v

degRevLex  p@(Vec ns) q@(Vec ms) =  case compare (sum ns) (sum ms) 
                                    of
                                    EQ -> lexFromEnd q p
                                    v  -> v
  -- Mind degRevLex!  It is not so trivial.  For example, for  n = 3
  -- it is presented by the matrix [u1,-e3,-e2] = [[1, 1, 1],
  --                                               [0, 0,-1],
  --                                               [0,-1, 0]
  --                                              ]


--------------------------------------------------------------------
ppComp_blockwise :: 
  Z -> PPComp -> PPComp -> PowerProduct -> PowerProduct -> CompValue
-- m   cp        cp'       p               q  
-- compare p q according by the direct sum of comparisons cp, cp':
-- first  cp  compares the vectors of the first  m items from p,q,
-- then, if equal, the rests are compared by  cp'.

ppComp_blockwise m cp cp' (Vec js) (Vec ks) =
  let
     (js', js'') = genericSplitAt m js
     (ks', ks'') = genericSplitAt m ks
  in
  case  cp (Vec js') (Vec ks')  of  EQ -> cp' (Vec js'') (Vec ks'')
                                    v  -> v

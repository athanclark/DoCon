--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module FreeMonoid
  (
   FreeMonoid(..), FreeMOrdTerm, 
   freeMN, freeMRepr,  freeMOId, freeMOComp, freeMWeightLexComp,
   freeMGCD
   --
   -- , instance Cast FreeMonoid [(Z, Z)], 
   --   instances  Show .. MulMonoid    for  FreeMonoid
  )
where

import qualified Data.Map as Map (lookup, insert)

import Categs   
import DPrelude (Cast(..), Z, CompValue(..), Comparison, ct)
import SetGroup 
import UPol_    (PPOId)




--------------------------------------------------------------------
data FreeMonoid =  FreeM (Maybe Z) [(Z, Z)]  deriving (Show, Eq)

-- Free monoid generated by anonymous generators.
--
-- (FreeM (Just n) _)  means the generator set   {No 1, No 2...No n}
-- (FreeM Nothing  _)  means infinite generator set:  {No 1 ...} 
-- 
-- Example:  
-- (non-commutative) monomial  x1*x3^2*x6^5  <- R<x1..x11>
-- can be represented as       FreeM (Just 11) [(1,1),(3,2),(6,5)]


freeMN :: FreeMonoid -> Maybe Z
freeMN  (FreeM mn _) =  mn

freeMRepr :: FreeMonoid -> [(Z, Z)] 
freeMRepr  (FreeM _ ps) =  ps 


instance Cast FreeMonoid [(Z, Z)] 
  where
  cast _ (FreeM nm _) ps =  FreeM nm ps           -- without check ?

--------------------------------------------------------------------
instance Set FreeMonoid 
  where
  showsDomOf (FreeM mn _) = case mn of

                  Just n -> ("FreeMonoid_of(g_1,...,g_"++) . shows n
                  _      -> ("FreeMonoid_of[g_1,g_2,...]"++) 

  baseSet (FreeM mn _) dm = 
    (case 
         (Map.lookup Set dm, mn)
     of
     (Just (D1Set o), _      ) -> (dm, o)
     (_,              Nothing) -> bset mn 
     (_,              Just n ) -> 
                   if n > 0 then  bset mn  else  (dm, error $ msg n)
    )
    where
    msg n = "baseSet (FreeM (Just n) ..):    n = " ++ (shows n "\n")

    bset _ = (Map.insert Set (D1Set o) dm, o)
                       where
                       o = error "baseSet (FreeM ..):   finish it\n"

  compare_m _ _ = 
          error "compare_m  is not defined for FreeMonoid, so far\n"
  fromExpr _ = 
          error "fromExpr  is not defined for FreeMonoid, so far\n"


--------------------------------------------------------------------
instance MulSemigroup FreeMonoid 
  where
  baseMulSemigroup _ = 
                   error "baseMulSemigroup (FreeM..):   finish it\n"

  unity_m f = Just $ ct f ([] :: [(Z, Z)])

  mul (FreeM mn ps) (FreeM mn' ps') =       -- it is not commutative
                                            -- 
                                   FreeM (maxn mn mn') (mulp ps ps')
    where
    maxn Nothing  _         = Nothing
    maxn _        Nothing   = Nothing
    maxn (Just n) (Just n') = Just $ max n n'
                                          
    mulp [] ps'             = ps'  
    mulp ps []              = ps
    mulp ps ((i', j'): ps') =
                          let (i, j) = last ps 
                          in 
                          if i /= i' then  ps ++ ((i', j'): ps')
                          else         (init ps) ++ ((i, j+j'): ps')

  inv_m f =  if  f == unity f  then Just f else Nothing

  power_m = SetGroup.powerbin

  root _ (FreeM _ _) =  error "root n (FreeM..):   skipped\n"

  divide_m f g =  fmap (ct f) $ dv (freeMRepr f) (freeMRepr g)
          --
          -- q = f/g  means that  q*g = f :  g is a suffix word of f
          -- Examples:  (x*y, y) -> Just x;  (y*x, y) -> Nothing

  divide_m2 f g =  (divide_m f g, divR f g, biDiv f g)
       where
       divR f g = fmap (ct f) $ divRRepr (freeMRepr f) (freeMRepr g)


dv ps       []         = Just ps                              -- local
dv []       _          = Nothing
dv [(i, e)] [(i', e')] = case (i == i' && e >= e', e-e')
                         of
                         (False, _) -> Nothing
                         (_,     0) -> Just []
                         (_,     d) -> Just [(i, d)]
dv (p:ps)  [q]    = fmap (p:) $ dv ps [q] 
dv (p:ps)  (q:qs) = case dv ps qs of Nothing -> Nothing
                                     Just rs -> dv (p:rs) [q] 
                              
divRRepr ps ps' =                                           -- local
               fmap reverse $ dv (reverse ps) (reverse ps')

biDiv :: FreeMonoid -> FreeMonoid -> Maybe (FreeMonoid, FreeMonoid)
  --
  -- LOCAL.
  -- biDiv f g = Just (l,r),  if f= l*g*r  (any such pair returned),
  --             Nothing,     if there does not exist such pair.
biDiv f g = 
  fmap 
    (\ (l, r) -> (ct f l, ct f r)) $ bdv (freeMRepr f) (freeMRepr g)
  where
  bdv ps     []       = Just (ps, [])
  bdv []     _        = Nothing
  bdv (p:ps) (p':ps') = 
    let
       {(x, e) = p;  (x', e') = p'}
    in
    case (bdv ps (p':ps'), x == x' && e >= e')
    of
    (Just (l, r), _    ) -> Just (mul1 (x, e) l, r)
    (_,          False) -> Nothing
    _                   -> case (divRRepr ps ps', e-e')
                           of
                           (Nothing, _) -> Nothing 
                           (Just qs, 0) -> Just ([],       qs)
                           (Just qs, d) -> Just ([(x, d)], qs)

mul1 :: (Z, Z) -> [(Z, Z)] -> [(Z, Z)]                     -- local
mul1    (_, 0)    ps           = ps  
mul1    p         []           = [p]
mul1    (x, e)    ((y, d): ps) = if x == y then (x, e+d): ps 
                                 else           (x, e): (y, d): ps

--------------------------------------------------------------------
instance MulMonoid FreeMonoid
 

--------------------------------------------------------------------
freeMGCD :: FreeMonoid -> FreeMonoid -> (FreeMonoid, FreeMonoid)

  -- freeMGCD f g = (gcdl f g, gcdr f g),  
  -- where  
  -- gcdl  is the greatest left  factor in  f  which is a right 
  --       factor in  g,
  -- gcdr  is the greatest right factor in  f  which is a left  
  --       factor in  g.

freeMGCD f g = (gcdr g f, gcdr f g) 
  where
  gcdr f g = ct f $ gc (freeMRepr f) (freeMRepr g)

  gc []           _  = []
  gc ((x, e): f') g  = case g of

           []           -> []
           (x', e'): g' -> 
             if
               x /= x' then  gc f' g
             else
             case (e >= e', isprefix f' g')
             of
             (True, True) -> (x, e'): f' 
             (True, _   ) -> gc f' g
             _            -> if null f' then [(x, e)]  else  gc f' g
    
  isprefix []          _             = True
  isprefix _           []            = False 
  isprefix ((x, e): f) ((x', e'): g) =
                 x == x'
                 && e <= e' && (null f || (e == e' && isprefix f g))




-- Grading, comparison on FreeMonoid  ------------------------------

type FreeMOrdTerm = (PPOId, Comparison FreeMonoid)

freeMOId   :: FreeMOrdTerm -> PPOId
freeMOComp :: FreeMOrdTerm -> Comparison FreeMonoid
freeMOId   = fst
freeMOComp = snd


-- usable comparisons ----------------------------------------------

freeMWeightLexComp ::
                   (Z -> Z) -> FreeMonoid -> FreeMonoid -> CompValue
                   -- weight
  -- Compare non-commutative pp by  totalWeight  first, then, 
  -- if equal, compare lexicographically by  xi.
  -- totalWeight  is defined as below by the given map 
  --                                                  \x -> weight x 

freeMWeightLexComp weight pp pp' = 
  (case 
       (compare (totalWeight ps) (totalWeight qs), lcomp ps qs)
   of 
   (EQ, v) -> v  
   (v,  _) -> v
  )
  where
  (ps, qs)    = (freeMRepr pp, freeMRepr pp')
  totalWeight = sum . map (\ (x, e) -> (weight x)*e)

  lcomp []           []             = EQ
  lcomp []           _              = LT
  lcomp _            []             = GT
  lcomp ((x, e): ps) ((x', e'): qs) = 
                                   case (compare x x', compare e e')
                                   of 
                                   (LT, _ ) -> GT
                                   (GT, _ ) -> LT
                                   (_,  EQ) -> lcomp ps qs
                                   (_,  v ) -> v
  

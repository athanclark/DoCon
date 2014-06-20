--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module SetGroup   -- Set, Semigroup ... Group   categories
  (              
   AddGroup(..), OrderedAddGroup(), 
   isOrderedGroup, absValue, trivialSubgroup, isoGroup, 
   isoConstruction_Subgroup,
   MulSemigroup(..), MulMonoid(), OrderedMulSemigroup(), 
   OrderedMulMonoid(), MulGroup(..), OrderedMulGroup(),
   upAddGroup, upMulSemigroup, upMulGroup,  unity, inv, divide, 
   invertible, divides, power, powerbin,
   unfactor, isPrimeFactrz, isPrimaryFactrz, isSquareFreeFactrz,
   factrzDif, eqFactrz, gatherFactrz,
   rootZ, 
   -- instances for Integer: 
   -- MulSemigroup, MulMonoid, AddGroup, OrderedAddGroup, 

   -- from Set_
   Set(..), OrderedSet(), compareTrivially, isFiniteSet, 
   isBaseSet, intervalFromSet, card, ofFiniteSet, isoOSet, 
   props_set_full_trivOrd, listToSubset,

   -- from Semigr_  
   AddSemigroup(..),  OrderedAddSemigroup(), AddMonoid(),
   OrderedAddMonoid(), 
   upAddSemigroup, isGroup, isCommutativeSmg, isoSemigroup, 
   trivialSubsemigroup, isoConstruction_Subsemigroup, 
   zeroS, isZero, neg, sub, times
   -- ,instances for Integer:  Set .. OrderedAddMonoid
  )

where
import Data.FiniteMap (addToFM)

import Maybe (fromMaybe, isJust)            
import List  (partition        )
import Categs   
       (CategoryName(..), Domain1(..), Domains1, Subsemigroup(..),
        Property_Subsemigroup(..), Subgroup(..), 
        Property_Subgroup(..), Construction_Subgroup(..),
        AddOrMul(..),  Factorization
       )
import Prelude_  (Z, PropValue(..), MMaybe, eFM, lkp, lookupProp,
                  fmapmap
                 )
import Common_   (sum1)
import Set_
import Semigr_





--------------------------------------------------------------------
powerbin :: (MulSemigroup a) => a -> Z -> Maybe a
                                 -- generic binary method to power 
powerbin x n                     -- multiplicative semigroup element 
  | n==1      = Just x
  | n==0      = unity_m x
  | n<0       = maybe Nothing (\y->powerbin y (-n)) $ inv_m x

  | otherwise = let  Just h = powerbin x $ quot n 2  
                in
                if  even n  then  Just (h `mul` h)
                else              Just ((h `mul` h) `mul` x)


--------------------------------------------------------------------
class (AddMonoid a) => AddGroup a  where

               -- Presumed:  IsGroup==Yes, 
               --            zero,add,neg  satisfy the group axioms.
  
  baseAddGroup :: a -> Domains1 a -> (Domains1 a, Subgroup a)



class (AddGroup a,OrderedAddMonoid a) => OrderedAddGroup a 
                 --
                 -- Presumed: 
                 -- base AddGroup  contains  (IsOrderedSubgroup,Yes)
                 --
                 -- - see the Subgroup constructor.


isOrderedGroup :: Subgroup a -> PropValue
isOrderedGroup = lookupProp IsOrderedSubgroup .subgrProps
--------------------------------------------------------------------
                         -- this is correct when IsOrderedGroup==Yes
absValue :: (AddGroup a) => a -> a
absValue                    x =  
                        if  less_m x $ zeroS x  then  neg x  else  x
{-# specialize absValue :: Z -> Z #-}
--------------------------------------------------------------------
-- Make trivial subgroup in a  Non-trivial base group. 

trivialSubgroup :: a -> Subgroup a -> Subgroup a

trivialSubgroup zeroOrUnity gG = 
  Subgroup 
      {subgrType    = subgrType gG,  subgrGens = Just [zeroOrUnity],
       subgrCanonic = Just id,       subgrProps= props,
       subgrConstrs = [],            subgrOpers= []
      }
    where    
    props = [(IsCyclicGroup    , Yes),          (IsPrimeGroup , No), 
             (IsNormalSubgroup , Yes),          (IsMaxSubgroup, No),
             (IsOrderedSubgroup, isOrderedGroup gG)
            ]
--------------------------------------------------------------------
-- Given a   Subgroup G with the base set X on a type `a',
--           a map  f: a -> b  injective on X,
--             f_inv  the inverse to  f  on X,
-- produce the  Subgroup G' on the base set f(X),  such that  
-- f_restrictedTo_X  is an isomorphism between G and G'.

isoGroup:: (a -> b) -> (b -> a) -> Subgroup a -> Subgroup b
isoGroup   f           f_inv       gG         = 
  Subgroup
          {subgrType    = tp,
           subgrGens    = fmapmap f gens,
           subgrCanonic = canmap',
           subgrProps   = props,
           subgrConstrs = constrs',
           subgrOpers   = opers'
          }
    where
    Subgroup {subgrType    = tp,     subgrGens  = gens,
              subgrCanonic = canmap, subgrProps = props,
              subgrConstrs = conss,  subgrOpers = _
             }
             = gG 

    canmap' = case  canmap  of  Just cn -> Just (f .cn .f_inv)
                                _       -> Nothing

    constrs' = map (isoConstruction_Subgroup f f_inv) conss
    opers'   = []   --SO FAR
--------------------------------------------------------------------
isoConstruction_Subgroup ::  
                  (a -> b) -> (b -> a) -> Construction_Subgroup a ->
                                             Construction_Subgroup b
isoConstruction_Subgroup _f _fInv _ = ConsGroupDUMMY
  -- case constr 
  -- of Intersection_Subgroup gps ->
  --            Intersection_Subgroup (map (isoGroup f f_inv) gps)
  --  GenBySet_Subgroup xX      -> 
  --                        GenBySet_Subgroup (isoOSet f f_inv xX)    

--------------------------------------------------------------------
-- This is similar to  AddSemigroup.

class (Set a) => MulSemigroup a  where     -- may be non-commutative

  baseMulSemigroup :: a -> Domains1 a -> (Domains1 a,Subsemigroup a)

  mul       :: a -> a -> a
  unity_m   :: a -> Maybe a
  inv_m     :: a -> Maybe a
  divide_m  :: a -> a -> Maybe a
  divide_m2 :: a -> a -> (Maybe a, Maybe a, Maybe (a,a))
  power_m   :: a -> Z -> Maybe a
  root      :: Z -> a -> MMaybe a

  -- divide(_m)
  -- is for the left-side quotient: for solving for  x  of the 
  -- equation   x*a = b  in the semigroup.
  -- The solution  x  may be NOT unique. Returned is some  x,  not
  -- necessarily the "best" one.   
  -- For a Ring, we can only rely (in the general case) on that 
  -- x1-x2  is a Zero divisor for any solutions  x1,x2.  Thus  x  is
  -- unique if a ring has not zero divisors. 
  -- Similar  is  inv(_m).
  --
  -- divide_m2  
  -- generalizes divide_m. It yields left, right, and bi-sided 
  -- maybe-quotient.
  -- Example: in  FreeMonoid[a,b,c]
  --        divide_m2 abccb cb = (Just abc, Nothing, Just (abc, []))
  --        divide_m2 abccb cc = (Nothing,  Nothing, Just (ab,b))
  ------------------------------------------------------------------

  unity_m x = case  subsmgUnity $ snd $ baseMulSemigroup x eFM  of
                                                   Just u -> u
                                                   _      -> Nothing 
  inv_m  x = maybe Nothing (\un->divide_m un x) $ unity_m x
  power_m  = powerbin 

--------------------------------------------------------------------
unity :: (MulSemigroup a) => a -> a
unity                        x =  fromMaybe (error msg) $ unity_m x
          where
          msg = ("unity x   failed,"++) $ showsWithDom x "x" "" "\n"

inv :: (MulSemigroup a) => a -> a
inv                        x =  fromMaybe (error msg) $ inv_m x
             where
             msg = ("inv x  failed,"++) $ showsWithDom x "x" "" "\n"

divide :: (MulSemigroup a) => a -> a -> a
divide                        x    y = 
                                fromMaybe (error msg) $ divide_m x y
          where
          msg = ("divide x y   failed,"++) $ showsWithDom x "x" "" $
                ("y = "++) $ shows y "\n"

invertible :: (MulSemigroup a) => a -> Bool
invertible = isJust .inv_m

divides :: (MulSemigroup a) => a -> a -> Bool
divides                        x    y =  isJust $ divide_m y x

power :: (MulSemigroup a) => a -> Z -> a
power                        x    n =  
                                 fromMaybe (error msg) $ power_m x n
                 where
                 msg = ("power x "++) $ shows n $ ("   failed,"++) $
                       showsWithDom x "x" "" "\n"

{-# specialize unity  :: Z -> Z      #-}
{-# specialize inv    :: Z -> Z      #-}
{-# specialize divide :: Z -> Z -> Z #-}
{-# specialize power  :: Z -> Z -> Z #-}

--------------------------------------------------------------------
class (MulSemigroup a) => MulMonoid a 
class (MulSemigroup a) => OrderedMulSemigroup a  

class (OrderedMulSemigroup a,MulMonoid a) => OrderedMulMonoid a 

class (MulMonoid a) => MulGroup a  
  where
  baseMulGroup :: a -> Domains1 a -> (Domains1 a, Subgroup a)


class (OrderedMulMonoid a,MulGroup a) => OrderedMulGroup a 

--------------------------------------------------------------------
upAddGroup     :: (AddGroup     a) => a -> Domains1 a -> Domains1 a
upMulSemigroup :: (MulSemigroup a) => a -> Domains1 a -> Domains1 a
upMulGroup     :: (MulGroup     a) => a -> Domains1 a -> Domains1 a

upAddGroup     a = fst .baseAddGroup     a .upAddSemigroup a
upMulSemigroup a = fst .baseMulSemigroup a .fst .baseSet a
upMulGroup     a = fst .baseMulGroup     a .upMulSemigroup a
--------------------------------------------------------------------
unfactor :: (MulSemigroup a) => Factorization a -> a
                                 -- example:  [(a,1),(b,2)] -> a*b^2
unfactor []        = error "unfactor []\n"
unfactor [(a,k)]   = power a k
unfactor ((a,k):f) = mul (power a k) $ unfactor f

isPrimeFactrz, isPrimaryFactrz, isSquareFreeFactrz
                                          :: Factorization a -> Bool
isPrimaryFactrz [_] = True
isPrimaryFactrz _   = False

isPrimeFactrz [(_,1)] = True
isPrimeFactrz _       = False

isSquareFreeFactrz f = (not $ null f) && all ((==1) . snd) f

factrzDif :: 
       (Eq a) =>
       Factorization a -> Factorization a -> Maybe (Factorization a)
  -- Difference.
  -- Examples:  [(a,1),(b,2)] [(a,1),(b,2)] -> Just []
  --            [(a,1),(b,2)] [(b,1)]       -> Just [(a,1),(b,1)]
  --            [(a,1),(b,2)] [(b,3)]       -> Nothing

factrzDif f []        = Just f
factrzDif f ((a,i):g) = case  span ((/= a).fst) f  of

          (_ , []       ) -> Nothing
          (f', (_,j):f'') -> case  compare i j  
                             of
                               GT -> Nothing
                               EQ -> factrzDif (f'++f'')           g
                               _  -> factrzDif (f'++((a,j-i):f'')) g

eqFactrz :: (Eq a) => Factorization a -> Factorization a -> Bool
eqFactrz              f                  g               = 
                                                 case  factrzDif f g 
                                                 of
                                                   Just d -> null d
                                                   _      -> False

gatherFactrz :: (Eq a) => Factorization a -> Factorization a

  -- Bring to true factorization by joining the repeated factors.
  -- Example:  [(f,2),(g,1),(f,3)] -> [(f,5),(g,1)]

gatherFactrz pairs = case  pairs  of

         []       -> []
         (p,i):ps -> (p, sum1 (i:(map snd eqs))): (gatherFactrz ps')
                                where
                                (eqs,ps') = partition ((==p).fst) ps
                
                     

--------------------------------------------------------------------
--------------------------------------------------------------------
instance MulSemigroup Integer 
  where 
  mul      = (*)
  unity_m  = const $ Just 1
  inv_m  n = if  (abs n)==1  then  Just n  else  Nothing 

  divide_m x y = case (x,y)  
                 of
                   (0,_) -> Just 0
                   (_,0) -> Nothing
                   _     -> case  quotRem x y  of  (q,0) -> Just q
                                                   _     -> Nothing

  divide_m2 _ _ = error "divide_m2  for integers:  use divide_m\n"

  power_m x n = case  (x,n)  -- binary method
                of
                  (0,0) -> error "power_m (0::Z) 0\n"
                  (_,0) -> Just 1
                  (1,_) -> Just 1
                  _     -> if n > 0  then  Just (x^n)  else  Nothing

  root 1 x = Just $ Just x
  root d x = case  (d < 1, x==0 || x==1, x < 0, even d)  of

    (True, _   , _   , _    ) -> 
         error $ ("root deg x,"++) $ showsWithDom x "x" "" $
               (",ndeg = "++) $ shows d $ ":  positive deg needed\n"
               
    (_   , True, _   , _    ) -> Just $ Just x
    (_   , _   , True, True ) -> Just Nothing
    (_   , _   , True, False) -> case  root d (-x)  
                                 of 
                                   Just (Just r) -> Just $ Just (-r)
                                   v             -> v

    _                         -> let  (r,p) = rootz_ d x 
                                 in
                                 if  p==x  then  Just $ Just r
                                 else            Just Nothing

  baseMulSemigroup _ dm = case  lkp dm MulSemigroup  of

    Just (D1Smg s) -> (dm, s)
    _              -> (addToFM dm MulSemigroup $ D1Smg s, s)
      where
      s = Subsemigroup 
             {subsmgType    = Mul,      subsmgUnity = Just $ Just 1,
              subsmgGens    = Nothing,  subsmgProps = props,
              subsmgConstrs = [],       subsmgOpers = []
             }
      props = [(Commutative          ,Yes), (IsGroup          , No),
               (IsCyclicSemigroup    ,No ), (IsMaxSubsemigroup, No),
               (IsOrderedSubsemigroup,No )
              ]


instance MulMonoid Integer      

instance AddGroup Integer  
  where  
  baseAddGroup _ dm = case  lkp dm AddGroup  of

    Just (D1Group g) -> (dm, g)
    _                -> (addToFM dm AddGroup (D1Group g), g)
      where
      g = Subgroup 
             {subgrType    = Add,             subgrGens  = Just [1],
              subgrCanonic = Just (const 0),  subgrProps = props,
              subgrConstrs = [],              subgrOpers = []
             }
      props = [(IsCyclicGroup    , Yes), (IsNormalSubgroup, Yes), 
               (IsMaxSubgroup    , No ), (IsPrimeGroup    , No ),
               (IsOrderedSubgroup, Yes)
              ]


instance OrderedAddGroup Integer      


--------------------------------------------------------------------
rootZ :: Z -> Z -> (Z, Z)
      -- n    x    (r, r^n)

  -- r = intPart( root_n(x) ):
  -- integer part of  n-th degree root  of a natural  x,  n > 0.

rootZ n x 
  | n < 1 || x < 0  = error $ concat 
                                 ["rootZ ", shows n " x,", 
                                  showsWithDom x "x" "" 
                                  "\ndegree > 0, x >= 0  required\n"
                                 ]
  | n==1 || x==0 || x==1 =  (x, x)
  | otherwise            =  rootz_ n x


rootz_ :: Z -> Z -> (Z, Z)       -- here  n, a > 1
rootz_    n    a =  bi 1 1 a
  where
  -- Just bisection  (the mean point is  intPart( (l+r)/2 ) ).
  -- It reduces sufficiently fast uniformly by  n.

  bi lp l r =    -- 1 <= l < rootN(a) < r,  lp = l^n

    if  l+1 == r  then  (l, lp)
    else                let  mid = quot (l+r) 2
                        in
                        case  boundedPower mid n
                        of
                          Nothing -> bi lp l mid          -- x^n > a
                          Just p  -> if  p == a  then  (mid,p)
                                     else              bi p mid r
               

  -- x -> n -> Just (x^n),   if  x^n <= a,
  --           Nothing,      otherwise.      (x > 1)
  --
  -- This takes care to avoid unnecessary full x^n evaluation.
  --
  boundedPower x n = bp n
    where
    bp 0 = Just 1
    bp m = case  quotRem m 2  of

      (q,0) -> case  bp q
               of
               Nothing -> Nothing
               Just p  -> let p2 = p*p
                          in  if p2 > a then  Nothing  else  Just p2
      _     -> case  bp (m-1)
               of
               Nothing -> Nothing
               Just p  -> let xp = x*p 
                          in  if xp > a then  Nothing  else  Just xp

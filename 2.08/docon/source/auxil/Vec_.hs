--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module Vec_    

  -- Category  instances for the  Vector domain over `a'.
  --
  -- All needed from here is  reexported by  VecMatr.

  (Vector(..)   -- from Categs

   -- ,instances for Vector:
   -- Show, Set, OrderedSet, AddSemigroup, AddMonoid,
   -- OrderedAddSemigroup, OrderedAddMonoid, AddGroup, 
   -- OrderedAddGroup, MulSemigroup, OrderedMulSemigroup, 
   -- MulMonoid, MulGroup, Num, Fractional, Ring, CommutativeRing,
   -- OrderedRing
  )
where
import Random   (Random(..)         )
import Maybe    (fromJust, catMaybes)
import DPrelude (showsWithDom       )
import Categs   (Vector(..), vecRepr)
import SetGroup 
import Ring0_
import Vec0_
import Vec1_    (vecBaseSet,      vecBaseAddSemigroup,
                 vecBaseAddGroup, vecBaseMulSemigroup, 
                 vecBaseMulGroup, vecBaseRing
                )




--------------------------------------------------------------------
instance (Show a) => Show (Vector a)  
  where   
  showsPrec _ v = ("(Vec "++). shows (vecRepr v). (" )"++)


instance (Random a) => Random (Vector a)
  where
           -- put a random vector "between vl and vh" to have random
           -- components "between" l(i) and h(i)  for each  i
           --
  randomR (vl,vh) g = (Vec $ reverse xs, g')
       where
       (xs,g') = foldl rnd ([],g) $ zip (vecRepr vl) (vecRepr vh)

       rnd (xs,g) (l,h) = (x:xs,g')  where  (x,g') = randomR (l,h) g 
                                         
  random _ = error "random:  use randomR\n"                                
       
--------------------------------------------------------------------
instance (Set a) => Set (Vector a)  
  where   
  baseSet      = vecBaseSet
  showsDomOf v = case  vecRepr v  of
                            []  -> ("{Vec 0 ?}"++) 
                            a:_ -> ("{Vec "++) .showsDomOf a .('}':)

  fromExpr v e = case  fromExpr (vecRepr v) e  of
                                       ([ys],"" ) -> ([Vec ys], "" )
                                       (_   ,msg) -> ([]      , msg)

  compare_m u v = cmpLex (vecRepr u) (vecRepr v)
                                   -- Looks like a partial ordering.
                                   -- Be careful !
    where
    cmpLex [x]    [y]    = compare_m x y
    cmpLex (x:xs) (y:ys) = case  compare_m x y  of
                                             Nothing -> Nothing
                                             Just EQ -> cmpLex xs ys
                                             v       -> v
    cmpLex _      _      =  
      error $
        ("compare_m: u v,    for  u,v <- Vector X  of sizes\n "++) $
        shows (vecSize u) $ (", "++) $ shows (vecSize v) $ msg 
        "\n\nu, v  should be of the same non-zero size\n"

    msg = case  map vecRepr [u,v]  of
                                 [_:_, _  ] -> showsWithDom u "u" ""
                                 [_  , _:_] -> showsWithDom v "v" ""
                                 _          -> id



--------------------------------------------------------------------
instance (OrderedSet a) => Ord (Vector a) 
  where
  compare u = fromJust .compare_m u 

instance (OrderedSet a) => OrderedSet (Vector a)


                    -- Additive semigroup  A + A +...+ A   (n-times)

instance (AddGroup a) => AddSemigroup (Vector a) 
  where 
  baseAddSemigroup      = vecBaseAddSemigroup
  add (Vec xs) (Vec ys) = Vec $ zipWith add xs ys

  zero_m v    = case  zero_m $ vecHead v  of
                                       Just z -> Just $ constVec v z
  neg_m       = Just .fmap neg
  times_m v n = Just $ fmap (\x->times x n) v

--------------------------------------------------------------------
instance (AddGroup        a) => AddMonoid           (Vector a)  
instance (OrderedAddGroup a) => OrderedAddSemigroup (Vector a)
instance (OrderedAddGroup a) => OrderedAddMonoid    (Vector a)

instance (AddGroup a) => AddGroup (Vector a)  where  
                                      baseAddGroup = vecBaseAddGroup

instance (OrderedAddGroup a) => OrderedAddGroup (Vector a)


instance (MulSemigroup a) => MulSemigroup (Vector a)  
  where
  baseMulSemigroup      = vecBaseMulSemigroup
  mul (Vec xs) (Vec ys) = Vec $ zipWith mul xs ys
                           -- as in the direct product of semigroups

  unity_m v = case  unity_m $ vecHead v  of
                                       Just u -> Just $ constVec v u
                                       _      -> Nothing
  inv_m = allMaybesVec .map inv_m .vecRepr

  divide_m (Vec xs) (Vec ys) = allMaybesVec $ zipWith divide_m xs ys

  divide_m2 _ _ = error ("divide_m2 (Vec _) (Vec _):  "++
                         "not defined for vectors, so far\n"
                        )
  power_m v n = allMaybesVec [power_m x n | x <- vecRepr v]

  root n v = case  map (root n) $ vecRepr v  of

    rs-> case  ( any (==(Just Nothing)) rs, any (==Nothing) rs )
         of
          (True, _   ) -> Just Nothing
          (_   , True) -> Nothing
          _            -> Just$ Just$ Vec $ catMaybes $ catMaybes rs

--------------------------------------------------------------------
instance (OrderedMulSemigroup a) => OrderedMulSemigroup (Vector a)
instance (MulMonoid           a) => MulMonoid           (Vector a)
instance (MulGroup            a) => MulGroup (Vector a)  where  
                                      baseMulGroup = vecBaseMulGroup

instance (Ring a) => Num (Vector a)  
  where 
  negate   = fmap neg
  (+)      = add
  u-v      = add u $ fmap neg v
  (*)      = mul
  signum _ = error "signum (Vec _):  not defined for Vector\n"
  abs    _ = error "abs (Vec _):  not defined for Vector\n"
  fromInteger _ = error "fromInteger:  use  fromi, fromi_m \n"

instance (Ring a) => Fractional (Vector a)  
  where 
  (/)            = divide         
  fromRational _ = 
             error "fromRational:  use  fromi  combined with (/) \n"

--------------------------------------------------------------------
                                     -- R x R x...x R   for a ring R
instance (Ring a) => Ring (Vector a)  
  where
  baseRing    = vecBaseRing
  fromi_m v n = case  fromi_m (vecHead v) n  of 
                                       Just x -> Just $ constVec v x
                                       _      -> Nothing

instance (CommutativeRing a) => CommutativeRing (Vector a) 
instance (OrderedRing     a) => OrderedRing     (Vector a)     

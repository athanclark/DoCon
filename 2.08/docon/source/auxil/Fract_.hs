--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------




module Fract_  

  -- Operations with Fractions.
  --
  -- All needed from here is  reexported by  Fraction.

  (num, denom, zeroFr, unityFr, canFr,
   cmp_, add_, pow_, mul_, fromexpr_ 

   -- ,instances for Fraction:
   --                     Show, Dom, Ord, Set .. CommutativeRing,  
   --                     OrderedSet .. OrderedAddGroup, OrderedRing
  )

where
import Data.FiniteMap (addToFM)

import Maybe    (catMaybes             )
import Ratio    (numerator, denominator)
import Categs
import DPrelude (PropValue(..), InfUnn(..), Expression(..), Z,
                 CompValue, eFM, lkp, lookupProp, showsExpr, 
                 antiComp, fmapfmap, showsWithDom
                )
import SetGroup   
import Ring0_ 
       (CommutativeRing(), Ring(..), OrderedRing(), GCDRing(..),
        isOrderedRing, isGCDRing, isField, upGCDRing, fromi
       )  
import Z ()




--------------------------------------------------------------------
num   (n :/ _) = n    
denom (_ :/ d) = d

zeroFr, unityFr :: (Ring a) => a -> Fraction a  

zeroFr  x = (zeroS x):/(unity x)
unityFr x = (unity x):/(unity x)

{-# specialize zeroFr  :: Z -> Fraction Z #-}
{-# specialize unityFr :: Z -> Fraction Z #-}


instance Dom Fraction  
  where  
  sample = num 
  dom _  = error "dom (x:/y):   `dom' is not defined for Fraction\n"
                 
--------------------------------------------------------------------
canFr :: (GCDRing a) => String -> a -> a -> Fraction a

  -- This is for bringing the intermediate result to canonical 
  -- fraction.
  -- mode = "g"  means to cancel the pair by gcd.
  --        "i"                           by canonical invertible,
  --        ""                            by both.

canFr mode n d =
  let
    (z,u,g) = (zeroS d, unity d, gcD [n,d])

    cancel a b dv = if  dv==u  then  a:/b  else  (a/dv):/(b/dv)

    msg = ("canFr "++) .(mode++) .(" num den,"++) 
          .showsWithDom n "num" "".("den =  "++).shows d .("\n\n"++)
  in
  case  (n==z, d==z)
  of
    (_   , True) -> error $ msg "den =  0\n"
    (True, _   ) -> z:/u
    _            ->
      case  mode  
      of
        "g" -> cancel n d g
        "i" -> cancel n d $ canInv d
        ""  -> cancel n' d' $ canInv d' 
                                      where  (n':/d') = cancel n d g
        _   -> error $ msg "mode  maybe only  \"\", \"g\", \"i\" \n"

{-# specialize canFr :: String -> Z -> Z -> Fraction Z #-}

--------------------------------------------------------------------
cmp_ :: (GCDRing a) => Fraction a -> Fraction a -> Maybe CompValue
cmp_                   (n1:/d1)      (n2:/d2)   = 
  let 
     { z = zeroS d1;  g = gcD [n1,n2];  h = gcD [d1,d2] }
  in
  case  (n1==z && n2==z, compare_m g z, compare_m h z)
  of 
    (True, _       , _       ) -> Just EQ
    (_   , Nothing , _       ) -> Nothing
    (_   , _       , Nothing ) -> Nothing
    (_   , Just gcp, Just hcp) ->
                        let  [u1,u2] = map (/g) [n1,n2]
                             [v1,v2] = map (/h) [d1,d2]
                             r       = compare_m (u1*v2) (u2*v1)
                        in
                        if  gcp==hcp  then  r  else  fmap antiComp r

{-# specialize cmp_ :: Fraction Z-> Fraction Z-> Maybe CompValue #-}

   {- OLD case ( zeroS d1,  add_ (n1:/d1) ((neg n2):/d2) ) 
      of (z,n:/d) -> (case (compare_m n z, compare_m d z)
    of (Nothing, _      ) -> Nothing (_      , Nothing) -> Nothing
       (Just EQ, _      ) -> Just EQ   (Just GT, Just GT) -> Just GT
       (Just LT, Just LT) -> Just GT  _                  -> Just LT)
   -}

--------------------------------------------------------------------
add_ :: (GCDRing a) => Fraction a -> Fraction a -> Fraction a
add_                   (n1:/d1)      (n2:/d2)   =  
  let  z = zeroS d1  
  in
  case  (n1==z, n2==z) 
  of
    (True,_   ) -> n2:/d2
    (_   ,True) -> n1:/d1
    _           -> let  g   = gcD [d1,d2]  
                        dd1 = d1/g
                        dd2 = d2/g  
                        n   = n1*dd2+n2*dd1
                        gg  = gcD [n,g]
                   in   canFr "i" (n/gg) ((dd1*dd2)*(g/gg))

{-# specialize add_ :: Fraction Z -> Fraction Z -> Fraction Z #-}
--------------------------------------------------------------------
pow_ :: (GCDRing a) => Fraction a -> Z -> Maybe (Fraction a)
pow_                   (n:/d)        k =  
                                   case  (isZero n, compare k 0)  of

  (True , EQ) -> error $ ("Fract_.pow_ f 0, \n"++) $
                                     showsWithDom (n:/d) "f" "" "\n"
  (_    , EQ) -> Just $ unityFr d
  (True , _ ) -> Just $ zeroFr  d
  (_    , GT) -> Just ((power n k):/(power d k))
  _           -> Just ((power n' (-k)):/(power d' (-k)))
                                              where
                                              n':/d' = canFr "i" d n

{-# specialize pow_ :: Fraction Z -> Z -> Maybe (Fraction Z) #-}
--------------------------------------------------------------------
mul_ :: (GCDRing a) => Fraction a -> Fraction a -> Fraction a
mul_                   (n1:/d1)      (n2:/d2)   = 
  let  z = zeroS d1
  in   if  (n1==z)||(n2==z)  then  zeroFr d1
       else
         let  {g12 = gcD [n1,d2];  g21 = gcD [n2,d1];
               nn1 = n1/g12;       dd1 = d1/g21;
               nn2 = n2/g21;       dd2 = d2/g12
              }
         in   canFr "i" (nn1*nn2) (dd1*dd2) 

{-# specialize mul_ :: Fraction Z -> Fraction Z -> Fraction Z #-}
--------------------------------------------------------------------
                                                            -- LOCAL
fromexpr_ ::
      (GCDRing a) => a -> Expression String -> ([Fraction a],String)
fromexpr_            a    e                 = case  fromExpr a e  of 

                                 -- element 
                                 -- of `a' also converts to fraction
  ([n1],"") -> ( [n1:/(unity a)], "" )
  _         -> 
    (case  e  of
      (E (L ":/") [e1] [e2]) -> fr (fromExpr a e1) (fromExpr a e2)
      _                      -> 
                    ( [], "fromExpr (a:/_)  "++(showsExpr e ")\n") )
    )
    where  
    fr ([n1],"" ) ([d1],"" ) = ([canFr "" n1 d1], "" )
    fr ([_ ],"" ) (_   ,msg) = ([]              , msg)
    fr (_   ,msg) _          = ([]              , msg)
--------------------------------------------------------------------
instance (MulSemigroup a) => Show (Fraction a)
  where  
  showsPrec _ (n:/d) = if  d==(unity d)  then  shows n
                       else   
                         ('(':).shows n.('/':).shows d .(')':)

--------------------------------------------------------------------
instance (GCDRing a) => Set (Fraction a)
  where  
  -- presumed:  (IsGCDRing,Yes)  for `a'

  compare_m    = cmp_
  showsDomOf f = ("(Fr "++). showsDomOf (num f) . (')':)

  fromExpr  f@(n:/_) e = 
                      -- syntax:  <num> | <num>:/<denom>,   <num>::a
                      --
     case  isGCDRing $ snd $ baseGCDRing n eFM 
     of
       No -> error $ ("fromExpr f e, "++) $
                  showsWithDom f "f" ""   $
                  ("e = "++) $ showsExpr e
                  "\n\nGCD-ring R needed to operate in Fraction R\n"

       _  -> fromexpr_ n e   -- see below
  ------------------------------------------------------------------
  baseSet  f@(n:/_) dom = case  (lkp dom Set, upGCDRing n eFM)  of

    (Just (D1Set s), _   ) -> (dom, s)
    (_             , aDom) -> 
               (case  catMaybes $ map (lkp aDom) [Set,Ring,GCDRing]
                of
                  [D1Set aS, D1Ring aR, D1GCDR gcR] ->
                           bs 
                             aS (osetProps aS)    (membership aS)
                                (subringProps aR) (gcdRingProps gcR)
               )
    where
    bs aS sProps bel rProps gcProps =
      let
        (z,u)            = (zeroS n, unity n)
        [field,orderedR] = 
                [lookupProp p rProps | p <- [IsField,IsOrderedRing]]
        belongs' md (n:/d) =  
                        d/=z && (n,d)==(n',d') && bl md n && bl md d
                                             where  
                                             (n':/d') = canFr "" n d
                                             bl 'r'   = bel 'r' 
                                             bl _     = const True
        card' = case  field  of  Yes -> osetCard aS
                                 No  -> Infinity
                                 _   -> UnknownV
        ------------------------------------------------------------ 
        -- Lemma.  If a commutative ring  R  has unity and has not
        --         zero divisors and is not a field,  then it is 
        --         infinite.
        -- And the fraction ring for a field F is isomorphic to F.

        list' = case  (field, osetList aS)  of
                               (Yes, Just xs) -> Just $ map (:/u) xs
                               _              -> Nothing
        ------------------------------------------------------------
        props' = [(IsBaseSet,Yes),
                  (FullType ,No ),  -- say,  unity:/zero  does not 
                                    -- belong to base set
                  (Finite, fin),
                  (OrderIsTrivial, triv'), (OrderIsTotal, tot'),
                  (OrderIsNoether, noet'), (OrderIsArtin, art')
                 ]
        triv' = if  orderedR==Yes  then No   else Unknown
        tot'  = if  orderedR==Yes  then Yes  else Unknown

        [fin,noet,art] = [lookupProp p sProps | 
                           p <- [Finite,OrderIsNoether,OrderIsArtin]
                         ]
        (noet',art') = if  orderedR==Yes  then  (noet,art)
                       else                     (Unknown,Unknown)
        ------------------------------------------------------------
        (low,up,inf,sup) = osetBounds aS
        bounds'          =
            if orderedR/=Yes  then (Nothing,Nothing,Nothing,Nothing)
            else                   (low'   ,up'    ,inf'   ,sup'   )

        [low',up',inf',sup'] = map boundFraction [low,up,inf,sup]
        boundFraction        = fmapfmap (:/u)
        ------------------------------------------------------------
        constrs' =  
          if  orderedR/=Yes  then  []
          else        
            case  intervalFromSet aS
            of 
              Nothing                   -> []
              Just (Interval l cl r cr) -> 
                      [Interval (fmap (:/u) l) cl (fmap (:/u) r) cr]
        ------------------------------------------------------------
      in
      case  lookupProp WithGCD gcProps
      of
        No -> (dom,  error $ frBaseDomGCDMessg n "baseSet" "\n")
        _  -> (addToFM dom Set $ D1Set s, s)
                where
                s = OSet {osetSample  = f,
                          membership  = belongs',
                          osetCard    = card', 
                          osetPointed = Just $ Just f,
                          osetList    = list',
                          osetBounds  = bounds',
                          osetProps   = props',
                          osetConstrs = constrs',
                          osetOpers   = []
                         }                               


frBaseDomGCDMessg num str = 
                        (str++) .(" (num:/_) _, \n"++) 
                        .("num = "++) .shows num .("\n <- R =  "++)
                        .showsDomOf num .("\n\nGCD-ring R needed"++)


--------------------------------------------------------------------
instance (GCDRing a, OrderedRing a) => OrderedSet (Fraction a)


instance (GCDRing a) => AddSemigroup (Fraction a)   
  where
  -- presumed:  (IsGCDRing,Yes)  for `a'

  zero_m        = Just .zeroFr .denom
  neg_m  (n:/d) = Just ((neg n):/d)
  add           = add_ 
  sub_m x       = Just .add x .neg

  times_m (n:/d) k = let  { k' = fromi d k;  g = gcD [k',d] }  
                     in           
                     Just $ canFr "i" (n*(k'/g)) (d/g)
  ------------------------------------------------------------------
  baseAddSemigroup (n:/_) dom =
    case  
         (lkp dom AddSemigroup, upGCDRing n eFM)  
    of
      (Just (D1Smg s), _   ) -> (dom, s)
      (_             , aDom) -> 
        (case  
             catMaybes $ map (lkp aDom) [Ring,GCDRing]
         of
           [D1Ring aR, D1GCDR gcR] ->
                         semigr (subringProps aR) (gcdRingProps gcR)
        )
    where
    semigr rProps gcProps =
      let
        props' = [(Commutative          , Yes    ), 
                  (IsGroup              , Yes    ),  
                  (IsMaxSubsemigroup    , No     ), 
                  (IsCyclicSemigroup    , Unknown),  -- so far
                  (IsOrderedSubsemigroup, ord'   )  
                 ]
        ord' = case  lookup IsOrderedRing rProps  of
                                                 Just Yes -> Yes
                                                 _        -> Unknown
      in
      (case  lookupProp WithGCD gcProps
       of
         No -> 
          (dom, error $ frBaseDomGCDMessg n "baseAddSemigroup" "\n")

         _  -> (addToFM dom AddSemigroup $ D1Smg s, s)
             where
             s = Subsemigroup {subsmgType    = Add,
                               subsmgUnity   = Just$ Just$ zeroFr n,
                               subsmgGens    = Nothing, --so far
                               subsmgProps   = props',
                               subsmgConstrs = [],
                               subsmgOpers   = []
                              }
      )

--------------------------------------------------------------------
instance (GCDRing a, OrderedRing a) => 
                                    OrderedAddSemigroup (Fraction a)
instance (GCDRing a) => AddMonoid (Fraction a)


instance (GCDRing a) => AddGroup (Fraction a)
  where
  baseAddGroup  f@(n:/_) dom =  
                       case  (lkp dom AddGroup, upGCDRing n eFM)  of
    
    (Just (D1Group g), _   ) -> (dom, g)
    (_               , aDom) -> 
             (case  catMaybes $ map (lkp aDom) [Ring,GCDRing]
              of
                [D1Ring aR, D1GCDR gcR] ->
                             gr (subringProps aR) (gcdRingProps gcR)
             )
    where
    gr rProps gcProps =
      let
        zeroFr = zeroS f     
        props' = [(IsNormalSubgroup , Yes    ),
                  (IsMaxSubgroup    , No     ), 
                  (IsOrderedSubgroup, ord'   ), 
                  (IsCyclicGroup    , Unknown), --SO FAR
                  (IsPrimeGroup     , Unknown)  --
                 ]
        ord'   = case  lookup IsOrderedRing rProps  of
                                                 Just Yes -> Yes
                                                 _        -> Unknown
      in
      case  lookupProp WithGCD gcProps
      of
        No -> (dom, error$ frBaseDomGCDMessg n "baseAddGroup" "\n")
        _  -> (addToFM dom AddGroup $ D1Group g, g)
                   where
                   g = Subgroup {subgrType    = Add, 
                                 subgrGens    = Nothing, 
                                 subgrCanonic = Just $ const zeroFr,
                                 subgrProps   = props',
                                 subgrConstrs = [],
                                 subgrOpers   = []
                                }                           

--------------------------------------------------------------------
instance (GCDRing a, OrderedRing a) => OrderedAddMonoid (Fraction a)
instance (GCDRing a, OrderedRing a) => OrderedAddGroup  (Fraction a)

instance (GCDRing a, OrderedRing a) => Ord (Fraction a)
  where
  compare x y = case  compare_m x y  of

    Just c -> c
    _      -> 
      error $ ("compare x y,"++) $ showsWithDom x "x" "Fraction R" $
              ("R =  "++) $ showsDomOf (num x)
              "\n\nIn-comparable fractions over R.\n"++ 
              "Probably, R is not an Ordered Ring under compare_m\n"

--------------------------------------------------------------------
instance (GCDRing a) => MulSemigroup (Fraction a)   
  where
  unity_m (_:/d) = Just $ unityFr d

  inv_m (n:/d) = if  n==(zeroS d)  then  Nothing   
                 else                    Just $ canFr "i" d n
  mul     = mul_
  power_m = pow_

  divide_m x y = let  z = zeroS x
                 in
                 case  (x==z, y==z)  of 
                                 (True,_   ) -> Just z
                                 (_   ,True) -> Nothing
                                 _           -> Just $ mul x $ inv y

  divide_m2 _ _ = error "divide_m2  for Integer:  use  divide_m\n"

  root deg (n:/d) = case  (root deg n, root deg d)  of 

     (Just (Just r1), Just (Just r2)) -> Just$ Just$ canFr "i" r1 r2
     (Just Nothing  , _             ) -> Just Nothing
     (_             , Just Nothing  ) -> Just Nothing
     _                                -> Nothing
                                            -- ?
  ------------------------------------------------------------------
  baseMulSemigroup (n:/_) dom =  
    case 
        (lkp dom MulSemigroup, upGCDRing n eFM)  
    of
      (Just (D1Smg s), _   ) -> (dom, s)
      (_             , aDom) -> 
        (case  
              catMaybes $ map (lkp aDom) [MulSemigroup,Ring,GCDRing]
         of
           [D1Smg aS, D1Ring aR, D1GCDR gcR] ->
                              smg aS aR (gcdRingProps gcR) $ unity n
        )
    where
    smg aS aR gcProps u =
      let
        props' = 
           [(Commutative,          Yes    ), (IsGroup          ,No),
            (IsCyclicSemigroup,    No     ), (IsMaxSubsemigroup,No),
            (IsOrderedSubsemigroup,Unknown)
           ]
        gens'  = if  (isField aR)==Yes  then  
                                     case  subsmgGens aS
                                     of
                                       Just gs -> Just [x:/u| x<-gs]
                                       _       -> Nothing
                 else  Nothing  -- SO FAR
      in 
      case  lookupProp WithGCD gcProps
      of
        No -> 
          (dom, error $ frBaseDomGCDMessg n "baseMulSemigroup" "\n")

        _  -> (addToFM dom MulSemigroup $ D1Smg s, s)
            where
            s = Subsemigroup {subsmgType    = Mul,
                              subsmgUnity   = Just$ Just$ unityFr u,
                              subsmgGens    = gens',
                              subsmgProps   = props',
                              subsmgConstrs = [],
                              subsmgOpers   = []
                             }                          

--------------------------------------------------------------------
instance (GCDRing a) => MulMonoid (Fraction a)

instance (GCDRing a) => Num (Fraction a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub
  (*)    = mul
  signum _ = 
        error "signum  not defined for  (GCDRing a) => Fraction a\n"
  abs _    = 
           error "abs  not defined for  (GCDRing a) => Fraction a\n"
  fromInteger _ = error "fromInteger:   use  fromi, fromi_m\n"


instance (GCDRing a) => Fractional (Fraction a)
  where
  (/)            = divide
  fromRational r = 
           (fromInteger $ numerator r)/(fromInteger $ denominator r)

--------------------------------------------------------------------
instance (GCDRing a) => Ring (Fraction a)  
  where
  fromi_m (_:/d) k = Just ((times u k):/u)  where  u = unity d 

  baseRing (n:/_) dom = case (lkp dom Ring, upGCDRing n eFM) of

    (Just (D1Ring r), _   ) -> (dom, r)
    (_              , aDom) -> 
      (case  
            catMaybes $ map (lkp aDom) [Ring,GCDRing]
       of
         [D1Ring aR, D1GCDR gcR] ->
                           rg aR (subringChar aR) (gcdRingProps gcR) 
      )
    where
    rg aR aChar gcProps =
      let
        conss' = []    -- SO FAR.
                       -- Here the ring extension construction has
                       -- to be analyzed and transformed to the 
                       -- field extension one.

        props' = [(IsField      , Yes    ), (Factorial  , Yes),  
                  (HasZeroDiv   , No     ), (HasNilp    , No ),
                  (IsPrimaryRing, Yes    ), (PIR        , Yes),
                  (IsOrderedRing, ord    ), (IsRealField, ord),
                  (IsGradedRing , Unknown)
                 ]
        ord    = isOrderedRing aR
      in
      case  lookupProp WithGCD gcProps
      of
        No -> (dom, error $ frBaseDomGCDMessg n "baseRing" "\n")
        _  -> (addToFM dom Ring $ D1Ring r, r)
                    where
                    r = Subring {subringChar    = aChar,    
                                 subringGens    = Nothing, -- so far
                                 subringProps   = props',
                                 subringConstrs = conss',
                                 subringOpers   = []
                                }

--------------------------------------------------------------------
instance (GCDRing a) => CommutativeRing (Fraction a)  

instance (GCDRing a, OrderedRing a) => OrderedRing (Fraction a)   





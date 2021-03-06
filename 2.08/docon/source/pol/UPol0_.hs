--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module UPol0_ 

  -- The Univariate polynomial constructor.
  --
  -- All needed from here is reexported by Pol.

  (resultant_1_euc, upolSubst, upolInterpol, 
   pshowsd_  --local

   -- ,instances  
   --  Show, Random, Set, AddSemigroup, AddMonoid, AddGroup, 
   --  MulSemigroup, MulMonoid, Num, Fractional, Ring, 
   --  CommutativeRing
  )
where
import Data.FiniteMap (addToFM)

import Random     (Random(..) )
import Maybe      (catMaybes  )
import List       (genericDrop)

import DPrelude   (PropValue(..), Expression(..), InfUnn(..), Z, 
                   lkp, sum1, isOrderedBy, showsExpr, ct, ctr, 
                   allMaybes, showsWithDom
                  )
import Categs   
import SetGroup  
import RingModule (Ring(..), CommutativeRing(), EuclideanRing(..),
                   powersOfOne, diffRatios
                  )
import VecMatr    (resultantMt)

import UPol_      (PolLike(..), UPol(..), lc, lc0, deg0, varP, 
                   pHeadVar, upolMons, cToUPol, cPMul
                  )
import LinAlg     (det_euc)

import qualified UPol_ (shows_, neg_, add_, times_, mul_)





--------------------------------------------------------------------
resultant_1_euc :: (EuclideanRing a) => UPol a -> UPol a -> a
resultant_1_euc                         f         g =
  if
    pIsConst f || pIsConst g  
    then
      error $ ("resultant_1_euc f g,"++) $
              ("\nf = "++) $ shows f $
              showsWithDom g "g" "" "\ndeg f, deg g > 0  required\n"
  else
    let  { n = (deg f)+1;  m = (deg g)+1 }
    in   det_euc $ resultantMt (pToVec n f) (pToVec m g)

--------------------------------------------------------------------
instance (Ring a) => Show (UPol a) where  showsPrec _ = UPol_.shows_ 


instance (CommutativeRing a, Random a) => Random (UPol a)  
  where
  -- put a random polynomial "between l and h" to have random 
  -- coefficients "between" coef(i,l) and coef(i,h),
  -- for each  i <- [0 .. (max (deg l) (deg h)]]

  randomR (l,h) g = 
               let  d      = succ $ maximum $ map (deg0 '_' 0) [l,h]
                    [u,v]  = map (Vec .pToVec d) [l,h]  
                    (w,g') = randomR (u,v) g  
               in   (pFromVec l $ vecRepr w, g')

  random _ = error "random:  use  randomR\n" 

--------------------------------------------------------------------
instance (CommutativeRing a) => Set (UPol a)  
  where
  showsDomOf  = pshowsd_
  fromExpr    = upolfromexpr_ 
  compare_m   = compareTrivially
  baseSet     = upolBaseSet

pshowsd_ :: (Set a,PolLike p) => p a -> String -> String
pshowsd_                         f   =  
                              showsDomOf (sample f) .shows (pVars f) 

--------------------------------------------------------------------
instance (CommutativeRing a) => AddSemigroup (UPol a)  
  where
  add      = UPol_.add_
  zero_m f = Just $ ctr f $ zeroS $ sample f

  neg_m     = Just .UPol_.neg_
  times_m f = Just .(UPol_.times_ times f)

  baseAddSemigroup f dm =  
    (case
          (lkp dm AddSemigroup, lkp (dom f) AddSemigroup)
     of
       (Just (D1Smg s), _              ) -> (dm, s)
       (_             , Just (D1Smg aS)) -> semig aS $ zeroS f
       _                                 -> (dm, error msg)
    )
    where 
    msg = ("baseAddSemigroup f dom'"++) $
          showsWithDom f "f" ""
          ("\nAddSemigroup term should present in the coefficient "
           ++"domain \nand have  isGroup /= No \n"
          )
    semig aS zp = case  isGroup aS  
                  of
                    No -> (dm, error msg)
                    _  -> (addToFM dm AddSemigroup $ D1Smg s, s)
      where
      s = Subsemigroup 
           {subsmgType    = Add,      subsmgUnity = Just $ Just zp,
            subsmgGens    = Nothing,  subsmgProps = props,
            subsmgConstrs = [],       subsmgOpers = []
           }
      props = 
        [(Commutative          , Yes    ), (IsGroup          , Yes),
         (IsMaxSubsemigroup    , No     ), (IsCyclicSemigroup, No ),  
         (IsOrderedSubsemigroup, Unknown)  
        ]


instance (CommutativeRing a) => AddMonoid (UPol a)

instance (CommutativeRing a) => AddGroup (UPol a)
  where
  baseAddGroup f dm = 
    (case  
         (lkp dm AddGroup, lkp (dom f) AddSemigroup)
     of
       (Just (D1Group g), _              ) -> (dm, g)
       (_               , Just (D1Smg aS)) -> gr aS $ zeroS f
       _                                   -> (dm, error msg)
    )
    where
    msg = ("baseAddGroup f dom',"++) $
          showsWithDom f "f" ""
          ("\nAddSemigroup term should present in the coefficient "
           ++"domain  \nand have  isGroup /= No \n"
          )
 
    gr aS zp = case  isGroup aS  of
                          No -> (dm, error msg)
                          _  -> (addToFM dm AddGroup $ D1Group g, g)
      where
      g = Subgroup 
             {subgrType    = Add,              subgrGens  = Nothing,
              subgrCanonic = Just $ const zp,  subgrProps = props,
              subgrConstrs = [],               subgrOpers = []
             }
      props = [(IsCyclicGroup    , No     ), (IsNormalSubgroup,Yes),
               (IsMaxSubgroup    , No     ), (IsPrimeGroup    ,No ),
               (IsOrderedSubgroup, Unknown)
              ]

--------------------------------------------------------------------
instance (CommutativeRing a) => MulSemigroup (UPol a)   
  where
  mul       = UPol_.mul_
  unity_m f = fmap (ct f) $ unity_m $ sample f

  inv_m f = if  isZero f || not (pIsConst f)  then  Nothing
            else                          fmap (ct f) $ inv_m $ lc f

  divide_m f g = 
         let  { zeroP = zeroS f;  (q,r) = pDivRem f g }
         in
         case  (f==zeroP, g==zeroP)
         of
           (True, _   ) -> Just zeroP  
           (_   , True) -> Nothing
           _            -> if  isZero r  then  Just q  else  Nothing

  divide_m2 _ _ = 
               error "divide_m2  for ..=> UPol a :   use divide_m\n"
  root _ _ = error "root n (UPol _)  is not defined so far, sorry\n"

  -- power  is the default
  ------------------------------------------------------------------
  baseMulSemigroup f dm = case  (lkp dm MulSemigroup, dom f)  of

    (Just (D1Smg s), _ ) -> (dm, s)
    (_             , aD) ->
      (case  
           catMaybes [lkp aD AddSemigroup, lkp aD MulSemigroup]
       of
         [D1Smg aAS, D1Smg aMS] ->
                           semig (subsmgProps aAS) (subsmgProps aMS)
         _                      -> (dm, error $ msg msg')
      )
      where
      msg   = ("baseMulSemigroup f dom',"++) .showsWithDom f "f" "" 

      msg'  = "\nAddSemigroup  or  MulSemigroup term  not found"
              ++" in the coefficient domain\n"
      msg'' = "\nCommutative ring required for coefficients\n"

      semig aASProps aMSProps =
        case 
            (lookup IsGroup aASProps, lookup Commutative aMSProps)
        of
          (Just No, _      )-> (dm, error $ msg msg'')
          (_      , Just No)-> (dm, error $ msg msg'')
          _                 -> (addToFM dm MulSemigroup$ D1Smg s, s)
      s =
        Subsemigroup {subsmgType    = Mul,      subsmgUnity = un',
                      subsmgGens    = Nothing,  subsmgProps = props,
                      subsmgConstrs = [],       subsmgOpers = []
                     }
      un'   = fmap Just $ unity_m f
      props = 
       [(IsMaxSubsemigroup    ,No     ),(Commutative      ,Yes    ),
        (IsGroup              ,No     ),(IsCyclicSemigroup,Unknown),
        (IsOrderedSubsemigroup,Unknown)
       ]
      
--------------------------------------------------------------------
instance (CommutativeRing a, MulMonoid a) => MulMonoid (UPol a)

instance (CommutativeRing a) => Num (UPol a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul
  signum _ = 
            error "signum (UPol _):   not defined for polynomials\n"
  abs    _ = error "abs (UPol _):   not defined for polynomials\n"
  fromInteger _ = error "fromInteger:   use  fromi, fromi_m\n"

instance (CommutativeRing a) => Fractional (UPol a)  
  where
  (/) = divide
  fromRational _ = error ("fromRational  to (UPol _):   "++
                          "use  fromi  combined with  divide_m\n"
                         )

instance (CommutativeRing a) => Ring (UPol a) 
  where
  baseRing  = upolBaseRing
  fromi_m f = fmap (ctr f) .fromi_m (sample f)


instance (CommutativeRing a) => CommutativeRing (UPol a)

--------------------------------------------------------------------
upolSubst :: 
       (CommutativeRing a) => UPol a -> UPol a -> [UPol a] -> UPol a

  -- Substitute  g  for the variable into  f,  f,g <- R[x].
  --
  -- The powers [g^2,g^3 ..] are either given in  gPowers
  -- or  gPowers = [],  and they are computed by the Horner scheme.

upolSubst f g gPowers = 
  let
     { (cs,js) = unzip $ upolMons f;  ps = powers js gPowers }
  in
  if  pIsConst f  then  f
  else                             -- f = c1*x^j1 +..+ ck*x^jk,  so
    sum1 $ zipWith cPMul cs ps     -- [g^j1..g^jk] have to be formed
      where                        -- here  j1>j2>..>jk >= 0  in js
      powers js [] = powersOfOne js g               -- Horner method
      powers js ps = reverse $ pp (reverse js) ps
                  where
                  pp []     _  = []
                  pp (0:js) ps = (unity g):(pp js ps)
                  pp (1:js) ps = g:(pp js ps)
                  pp (j:js) ps = let  (p:ps') = genericDrop (j-2) ps
                                      js'     = [i+1-j | i <- js]
                                 in   p:(pp js' ps')

--------------------------------------------------------------------
upolInterpol :: (CommutativeRing a) => UPol a -> [(a,a)] -> UPol a
                                       -- smp     tab

  -- Interpolate (rebuild) polynomial  y = y(x),  of degree n, 
  -- x,y <- a,  given by the table  tab = [(x0,y0)..(xn,yn)], 
  -- xi do not repeat,  and by the sample polynomial  smp.
  --
  -- Required:  `a' should have unity.
  -- Example:  
  -- for Z[x],  upolInterpol _ [(0,1),(1,-2),(2,-1)] = 2*x^2 -5*x +1
  -- METHOD.
  -- Newton interpolation formula with the difference ratios:
  -- p(x) =
  --      y0 + (x-x(0))*y(01) +...+ (x-x(0))*..*(x-x(n-1))*y(01..n),
  --
  -- where  y(01..k)  is the difference ratio of order k:
  -- y01 = (y1-y0)/(x1-x0),  y012 = (y12-y01)/(x2-x0), ...
  --                                               - see  diffRatios

upolInterpol  smp@(UPol _ a v aDom)  tab =  
  (case  tab
   of
     []      -> error $ msg "\n\ntab = []\n"
     [(_,y)] -> fromCoef y        
     _       ->
       if  hasRepetition xs  then  
                              error $ msg "\n\nx_i repeat in  tab\n"
       else
         interp (map fromCoef xs) $ map head $ diffRatios (/) tab
  )
  where
  xs       = map fst tab
  fromCoef = cToUPol v aDom 
  msg      = ("upolInterpol smp tab,"++) .showsWithDom smp "smp" "" 

  hasRepetition (x:xs) = elem x xs || hasRepetition xs
  hasRepetition _      = False

  interp (x0:xs) dRs = y0 + (x-x0)*(intp xs $ map fromCoef dRs)

  y0 = fromCoef $ snd $ head tab
  x  = varP (unity a) smp

  intp _       []       = zeroS smp
  intp (xi:xs) (dr:drs) = dr + (x-xi)*(intp xs drs)

--------------------------------------------------------------------
upolfromexpr_ :: (CommutativeRing a) => 
                    UPol a -> Expression String -> ([UPol a],String)

  -- Read univariate polynomial given a sample polynomial and 
  -- expression.
  -- So far, it requires a ring `a' with UNITY.

upolfromexpr_ f e = rd e
  where
  v = pHeadVar f
  u = unity $ sample f

  rd e = case  fromExpr u e  of    -- first try coefficient

    ([c],"") -> ([ctr f c], "")
    _        -> 
      (case  e  of
        (E (L "-") []   [e2]) -> p "-u" ([],"") (rd e2)
        (E (L "-") [e1] [e2]) -> p "-"  (rd e1) (rd e2)
        (E (L "+") [e1] [e2]) -> p "+"  (rd e1) (rd e2)
        (E (L "*") [e1] [e2]) -> p "*"  (rd e1) (rd e2)
        (E (L "/") [e1] [e2]) -> p "/"  (rd e1) (rd e2)
        (E (L "^") [e1] [e2]) -> pw (rd e1) $ fromExpr (1::Z) e2
        (L s)                 -> variable s v
        _                     -> ([], msg "\n\nWrong expression.")
      )
      where
      msg = ("upolfromexpr smp expr,"++)
              .showsWithDom f "smp" "" .("\nexpr = "++) .showsExpr e

      p "-u" _        ([f],"") = ( [-f],  "" )
      p "-"  ([f],"") ([g],"") = ( [f-g], "" )
      p "+"  ([f],"") ([g],"") = ( [f+g], "" )
      p "*"  ([f],"") ([g],"") = ( [f*g], "" )
      p "/"  ([f],"") ([g],"") = case  divide_m f g  of

                Just q -> ([q], "")
                _      -> ([], msg "\n\nFailed to divide with `/'.")

      p _    ([_],"") pair     = pair
      p _    pair     _        = pair

      pw ([f],"" ) ([n],"" ) = ([f^n], "" )
      pw ([_],"" ) (_  ,msg) = ([]   , msg)
      pw (_  ,msg) ([_],"" ) = ([]   , msg)
 
                           -- read monomial polynomial from variable
                           --
      variable s v = if  s==v  then  ([ct f (u,1::Z)], "")
                     else
                       ([], msg $ ("\n\n"++) $ shows s
                                    "  is not in the variable list."
                       )


--------------------------------------------------------------------
upolBaseSet :: 
   (CommutativeRing a)
   => 
   UPol a -> Domains1 (UPol a) -> (Domains1 (UPol a), OSet (UPol a))

upolBaseSet  f@(UPol _ c v aD)  dm =
  (case  
       (zeroS c, lkp aD Set, lkp dm Set)  
   of
     (_, _              , Just (D1Set s)) -> (dm, s)
     (z, Just (D1Set aS), _             ) -> 
                                     pset z aS $ lkp aD AddSemigroup
     _                                    -> (dm, error msg)
  ) 
  where
  msg = ("baseSet smp dm,"++) $ showsWithDom f "smp" "" $
        ("\nSet, AddSemigroup terms  should present in the "++
         "coefficient domain, \nthe latter with  isGroup /= No \n"
        )
  pset _ _  Nothing             = (dm, error msg)
  pset z aS (Just (D1Smg aSmg)) = case  isGroup aSmg  of  

    No -> (dm, error msg)
    _  -> (addToFM dm Set $ D1Set s, s)
     where
     s =
       let  
         bel                     = membership aS
         bel' md (UPol ms _ u _) = 
                                  let  (coefs,exps) = unzip ms 
                                  in
                                  u==v  &&  all (/=z) coefs       &&
                                  isOrderedBy (flip compare) exps &&
                                  bl coefs
             where  
             bl = if  md=='r'  then  all (bel 'r')  else  const True

         props' = [(Finite,       No ), (IsBaseSet,      Yes),
                   (FullType,     No ), (OrderIsTrivial, Yes),
                   (OrderIsTotal, No ), (OrderIsNoether, Yes), 
                   (OrderIsArtin, Yes)
                  ]
       in
       OSet {osetSample  = f,           membership  = bel',
             osetCard    = Infinity,    osetPointed = Just $ Just f,
             osetList    = Nothing,
             osetBounds  = (Nothing,Nothing,Nothing,Nothing),
             osetProps   = props',
             osetConstrs = [],          
             osetOpers   = []
            }



--------------------------------------------------------------------
-- :: (CommutativeRing a) => 
-- UPol a->Domains1 (UPol a)-> (Domains1 (UPol a,Subring (UPol a))


upolBaseRing  smp@(UPol _ a _ aD)  dm =
  (case
       (lkp dm Ring, lkp aD Ring)
   of
     (Just (D1Ring r), _               ) -> (dm, r)
     (_              , Just (D1Ring aR)) ->
             rg aR $ 
                catMaybes $ map (lkp aD) [AddSemigroup,MulSemigroup]
     _                                   -> 
        (dm, 
         error $ msg "\nRing term not found in coefficient domain\n"
        )
  )
  where
  msg  = ("baseRing smp dm,"++) .showsWithDom smp "smp" ""

  msg' = "\nAddSemigroup, MulSemigroup terms  should present in"++
         " the coefficient domain, \nwith the properties  "++
         "IsGroup, Commutative /= No\n"

  rg aR [D1Smg addS, D1Smg mulS] = 
                       rg' aR (isGroup addS) $ isCommutativeSmg mulS
                                          -- test partially  Ring(a)

  rg _  _                        = (dm, error $ msg msg')
  
  rg' aR isG isComm =
             if  isG==No || isComm==No  then  (dm, error $ msg msg')
             else                    (addToFM dm Ring $ D1Ring r, r)
    where
    r =
      let  
        (zr,un)               = (zeroS a, unity a)
        x                     = varP un smp
        xPowers               = x:(map (x*) xPowers)
        (charC,propsC,opersC) = 
                  (subringChar aR, subringProps aR, subringOpers aR)
                   --
                   -- possibility:  aRP = baseRingToUPolSubring v aR
                   -- coefficient subring inside  P = R[v]...
        ------------------------------------------------------------
        constrs' = []  

        {-  do we need explicit  FinGenExt for polynomials ?
         One of constructions is that   P   is  generated  by  the
         indeterminate elements over RP corresponding to   vars  -
         with the zero algebraic relation ideal. 
         The maps between  f <- P   and its polynomial 
         representation over RP are given by toPolOverP,fromPolOverP
         which are almost identity ones in this case. 
               [ (FinGenExt_subring "" rRP indeterminates [] 
                                          toPolOverP fromPolOverP )]
          where  toPolOverP f = let (cs,exps) = unzip $ polMons f
                             cs'     = map (\c-> cToPol c cp vars) ?
                         in  Pol (zip cs' ? exps) cp vars
          fromPolOverP f = let  (cs,exps) = unzip $ polMons f
                           in   Pol (zip (map lc cs) exps)  cp vars
        -}
        ------------------------------------------------------------
        names = [IsField,HasZeroDiv,HasNilp,IsPrimaryRing,Factorial]
        propVs = 
          case  allMaybes [lookup p propsC | p <- names]
          of
            Just xs -> xs
            Nothing -> error $ msg ("\nSome property names skipped"
                                    ++" in the coefficient ring\n"
                                   )   
        [field,hasZD,hasNilp,primary,fact] = propVs

        props' = 
              completeProps  ringAxioms
                [(IsField     , No     ), (HasZeroDiv   , hasZD   ),
                 (HasNilp     , hasNilp), (IsPrimaryRing, primary'),
                 (Factorial   , fact   ), (PIR          , field   ),
                 (IsRealField , No     ), (IsOrderedRing, Unknown ),
                 (IsGradedRing, No     )
                                      -- so far
                ]
        ringAxioms          = []   -- so far
        completeProps  _ ps = ps   --

        primary' = primary         -- Lemma...
        ------------------------------------------------------------
        opers'   = case  lookup WithPrimeField opersC  of

          Nothing -> []
          Just wp -> [(WithPrimeField, wp')]
            where
            wp' = WithPrimeField' {frobenius            = fr',
                                   dimOverPrime         = Infinity,
                                   primeFieldToZ        = toz',
                                   primeFieldToRational = tor',
                                   primitiveOverPrime   =
                                      case  dimOverPrime wp
                                      of
                                        Fin 1 -> (xPowers,[],toPol')
                                        _     -> undefined  --SO FAR
                                  }
            toz'     = primeFieldToZ wp .lc0 zr 
            tor'     = primeFieldToRational wp .lc0 zr
            toPol' f = [(ct smp a, e)| (a,e) <- upolMons f]
            fr' = 
              let  (pp,ppInv) = frobenius wp
              in
              case  charC
              of
                Nothing -> undefined
                Just 0  -> undefined
                Just p  -> (pp',ppInv')
                  where
                  pp'    f = ctr smp [(pp c,e*p)| (c,e)<-upolMons f]
                  ppInv' f = 
                    let  
                      (cs,es) = unzip $ upolMons f
                      (qs,rs) = unzip [quotRem e p | e <- es]
                    in
                    if  any (/=0) rs  then  Nothing  
                    else              --more precise: Just Nothing ?
                      case  allMaybes $ map ppInv cs
                      of
                        Nothing  -> Nothing
                        Just cs' -> 
                          case  allMaybes cs'  
                          of
                            Just bs -> 
                                    Just $ Just $ ct smp $ zip bs qs
                            _       -> Nothing 
        ------------------------------------------------------------
      in
      Subring {subringChar  = charC,   subringGens    = Nothing,
               subringProps = props',  subringConstrs = constrs',
               subringOpers = opers'
              }

 ;







{- reserve  ***********************************************
instance (Convertible a b, Ring b) => Convertible a (UPol b)   
  where cvm a f= case cvm a (sample f)  of  Just c -> Just$ ctr f c
                                            _      -> Nothing
instance(Convertible a b,AddGroup b)=>Convertible (UPol a) (UPol b)
  where
  cvm  (UPol mons a v _)  g@(UPol _ b v' _) =
    -- (f converts to domain of g) = 
    --                         f,g are of same variable  AND
    --                         coef(f) converts to domain of coef(g)
    -- The conversion means converting coefficient in each 
    -- monomial and removal of the new zero ones. 
    case  (v==v' && isJust (cvm a b))
    ofFalse -> Nothing
      _     -> Just $ ctr g $ [(cv a b,p) | (a,p) <- mons]
***********************************************
-}











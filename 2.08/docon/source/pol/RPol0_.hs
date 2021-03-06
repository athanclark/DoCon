module RPol0_   

  -- Continuation of  RPol_.
  --
  -- All needed from here is reexported by  Pol.
  --
  -- instances for RPol:
  -- Set, AddSemigroup, AddMonoid, AddGroup, MulSemigroup, 
  -- MulMonoid, Num, Fractional, Ring, CommutativeRing, GCDRing

where
import Data.FiniteMap (addToFM)

import List      (genericLength)

import DPrelude  (Expression(..), PropValue(..), InfUnn(..), Z, eFM,
                  ct, ctr, showsExpr, eFM, lkp, allMaybes, 
                  showsWithDom 
                 )
import Categs   
import SetGroup 
import RingModule (Ring(..), CommutativeRing(), GCDRing(..),
                   isGCDRing, upGCDRing
                  )
import UPol_      (PolLike(..), lc, cPMul)
import RPol_      
       (RPol'(..), RPol(..), rpolRepr, rvarsTermCp, rvarsTermRanges,
        rpolVPrefix, rpolVRanges, cToRPol, varToRPol, rHeadVarPol,
        rFromHeadVarPol
       )
import qualified RPol_ (add_, mul_               )
import qualified Pgcd_ (gcdTerm_, upolGCD_generic)
import qualified Pol1_ (set_, asmg_, agr_, msmg_ )





--------------------------------------------------------------------
-- The below instances for  RPol  are almost same as for  Pol.


instance (CommutativeRing a) => Set (RPol a)  
  where
  compare_m    = compareTrivially
  fromExpr     = rpolfromexpr_
  showsDomOf f = let  a    = sample f
                      pref = rpolVPrefix f
                      rgs  = rpolVRanges f
                 in   showsDomOf a .('[':) .(pref++)
                                   .(' ':) .shows rgs .(']':)

  baseSet  f@(RPol _ c t aDom)  dom =

    -- differs from the Pol case only in `membership': it tests 
    -- variables and ordering in another way
    let
      (z, (cp,pref,ranges)) = (zeroS c, t)
      bel                   = membership $ snd $ baseSet c aDom

      bel' md (RPol g' _ t' _) =  
        let
          (cp',pref',ranges') = t'
          inRange v           =
                    and $ zipWith (\i (l,h)-> i>=l && i<=h) v ranges

          bl = if  md=='r'  then  bel 'r'  else  const True

          belg (CRP _)         = True
          belg (NRP v n cf tl) = n > 0     &&  inRange v   &&
                                 corrCf cf &&  lessMon tl  &&
                                 belg cf   &&  belg tl
            where              
            corrCf (CRP b)       = b /= z  &&  bl b
            corrCf (NRP u _ _ _) = (cp v u)==GT &&  (cp' v u)==GT

            lessMon (CRP _)       = True
            lessMon (NRP u m _ _) = 
                               r==r' && r/=LT && (r==GT || n > m)
                                                     where 
                                                     r  = cp  v u
                                                     r' = cp' v u
        in  (pref',ranges')==(pref,ranges)  &&  belg g'
    in
    Pol1_.set_ (showsDomOf f "") dom aDom f bel'



--------------------------------------------------------------------
instance (CommutativeRing a) => AddSemigroup (RPol a)
  where
  zero_m f = Just $ ct f $ zeroS $ sample f
  neg_m  f = Just $ ct f $ fmap neg $ rpolRepr f

  add (RPol f a t _) g = 
                       ct g $ RPol_.add_ (zeroS a) cp f $ rpolRepr g
                                                  where
                                                  cp = rvarsTermCp t
  times_m f n = Just $ ct f $ tm $ rpolRepr f
    where
    z                 = zeroS $ sample f
    tm (CRP a)        = CRP $ times a n
    tm (NRP v m c tl) = let  { tl' = tm tl;  c' = tm c }
                        in
                        if  c'==(CRP z)  then  tl'
                        else                   NRP v m c' tl'

  baseAddSemigroup  f@(RPol _ c t aDom)  dom =
      Pol1_.asmg_ 
               (showsDomOf f "") dom aDom $ cToRPol t aDom $ zeroS c

--------------------------------------------------------------------
instance (CommutativeRing a) => AddMonoid (RPol a)

instance (CommutativeRing a) => AddGroup (RPol a)
  where
  baseAddGroup  f@(RPol _ c t aDom)  dom = 
       Pol1_.agr_ 
               (showsDomOf f "") dom aDom $ cToRPol t aDom $ zeroS c
  
--------------------------------------------------------------------
instance (CommutativeRing a) => MulSemigroup (RPol a)
  where
  unity_m f = fmap (ct f) $ unity_m $ sample f

  inv_m  f@(RPol (CRP a) _ _ _) = fmap (ct f) $ inv_m a
  inv_m  _                      = Nothing 

  mul (RPol f a vt _) g = ct g $ RPol_.mul_ z cp f $ rpolRepr g
                                                 where
                                                 z  = zeroS a
                                                 cp = rvarsTermCp vt
  divide_m f g = let  (q,r) = pDivRem f g 
                 in   if  isZero r  then  Just q  else  Nothing

  divide_m2 _ _ = error "divide_m2 (RPol ..) _:  use  divide_m\n"
  root _ _      = 
             error "root _ (RPol ..):  not defined, so far, sorry\n"

  -- power  is the default

  baseMulSemigroup  f@(RPol _ c _ aDom) dom =  
    Pol1_.msmg_ 
          (showsDomOf f "") dom aDom $ fmap (Just .ct f) $ unity_m c

--------------------------------------------------------------------
instance (CommutativeRing a, MulMonoid a) => MulMonoid (RPol a)

instance (CommutativeRing a) => Num (RPol a)  
  where  
  negate = neg
  (+)    = add
  (-)    = sub
  (*)    = mul
  signum      _ = error "signum (RPol _):   it is senseless there\n"
  abs         _ = error "abs (RPol _):   it is senseless there\n"
  fromInteger _ = error "fromInteger _  to (Pol ..):   use  fromi\n"

instance (CommutativeRing a) => Fractional (RPol a)  
  where
  (/) = divide
  fromRational _ = error ("fromRational _  to (Pol ..):  \n"++
                          "use  fromi  combined with  divide_m\n"
                         )

--------------------------------------------------------------------
instance (CommutativeRing a) => Ring (RPol a)
  where
  fromi_m  f = fmap (ct f) .fromi_m (sample f) 

  baseRing f fdom = 
    (case
         (lkp fdom Ring, dom f)
     of
       (Just (D1Ring r), _ ) -> (fdom, r)
       (_              , aD) ->
          rg (lkp aD AddSemigroup, lkp aD MulSemigroup, lkp aD Ring)
    )
    where
    (zr, pDomString) = (zeroS $ sample f, showsDomOf f "")

    rg (Just (D1Smg addS), Just (D1Smg mulS), Just (D1Ring aR)) =
                                                    rg' addS mulS aR
    rg _                                                        =
                                            (fdom, error $ msg msg')
    msg   = ("baseRing sampleP pDom,"++)
            .(("\nsampleP <-  "++pDomString)++)
    msg'  = "\n\nRing or subsemigroup terms not found "++
            "in the coefficient domain\n"
    msg'' =  
       "\n\nAddSemigroup, MulSemigroup terms  aS, mS  should reside"
       ++"\nin the coefficient domain,\n"++
       "aS  with  (IsGroup,Yes),  mS  with  (Commutative,Yes) \n"

    msgPropsSkipped =
         "\n\nSome property names skipped in the coefficient ring\n"

    rg' addS mulS aR = 
      (case 
           (isGroup addS, isCommutativeSmg mulS) 
       of                                   --test partially Ring(a)
         (Yes,Yes) -> (addToFM fdom Ring $ D1Ring r, r)
         _         -> (fdom, error $ msg msg'')
      )
      where
      r = Subring {subringChar  = charC,   subringGens   = Nothing,
                   subringProps = props',  subringConstrs= constrs',
                   subringOpers = opers'
                  }
      constrs' = []  
            -- do we need explicit FinGenExt construction for RPol ?

      (charC,propsC,opersC) =
                  (subringChar aR, subringProps aR, subringOpers aR)
                    --
                    -- possibility:  aRP = baseRingToPolSubring v aR
                    -- - coefficient subring inside  P = R[vars]...
      props' = 
       let
        names = [IsField,HasZeroDiv,HasNilp,IsPrimaryRing,Factorial]

        propVs = case  allMaybes [lookup p propsC | p <- names]  of
                              Just xs -> xs
                              Nothing -> error $ msg msgPropsSkipped

        [field,hasZD,hasNilp,primary,fact] = propVs

        ringAxioms          = []   -- so far
        completeProps  _ ps = ps   --

        pir'     = if  field==No  then No  else Unknown
                                           -- for it is multivariate
        primary' = primary   -- Lemma...
       in
       completeProps ringAxioms
               [(IsField      , No     ), (HasZeroDiv   , hasZD   ),
                (HasNilp      , hasNilp), (IsPrimaryRing, primary'),
                (Factorial    , fact   ), (PIR          , pir'    ), 
                (IsRealField  , No     ), (IsOrderedRing, Unknown ), 
                (IsGradedRing , No     )  -- so far
               ]

      opers' = case  lookup WithPrimeField opersC  of

        Nothing -> []
        Just wp -> [(WithPrimeField, wp')]
          where
          wp' = WithPrimeField' {frobenius            = fr',
                                 dimOverPrime         = Infinity,
                                 primeFieldToZ        = toz',
                                 primeFieldToRational = tor',
                                 primitiveOverPrime   = error msg 
                                }
          msg = "primitiveOverPrime  not defined for RPol  "++
                                                  "(unlike UPol) \n"
          msgFrobChar = 
               "Frobenius map for R[x1..xn]:  char(R) > 0  needed\n"
          toz' f = case  rpolRepr f  of  CRP a -> primeFieldToZ wp a
          tor' f = case  rpolRepr f  of  CRP a -> 
                                           primeFieldToRational wp a
          fr' = 
            let  (pp,ppInv) = frobenius wp
            in
            case  charC  
            of
              Nothing -> error msgFrobChar
              Just 0  -> error msgFrobChar
              Just p  -> (pp',ppInv')
                where
                pp' g = ctr f $ ppow $ rpolRepr g
                  where
                  ppow (CRP a)         = CRP $ pp a
                  ppow (NRP v n cf tl) = 
                    let
                        cf' = ppow cf
                    in 
                    if  cf'==(CRP zr)  then  ppow tl
                    else                   NRP v (n*p) cf' (ppow tl)

                ppInv' g = case  inv' $ rpolRepr g
                           of
                             Just (Just h) -> Just $ Just $ ctr g h
                             _             -> Nothing

                inv' (CRP a) = case  ppInv a  
                               of
                                Just (Just b) -> Just $ Just $ CRP b
                                _             -> Nothing
  
                inv' (NRP v n cf tl) = 
                  let
                     (q,r) = quotRem n p 
                  in
                  if  r /= 0  then  Nothing
                  else
                    case  (inv' cf, inv' tl)
                    of
                      (Just (Just cf'), Just (Just tl')) ->
                                       Just $ Just $ NRP v q cf' tl'
                      _                                  -> Nothing



--------------------------------------------------------------------
instance (CommutativeRing a) => CommutativeRing (RPol a)


instance (GCDRing a) => GCDRing (RPol a)
  where
  baseGCDRing f = Pgcd_.gcdTerm_ (shows f "") (showsDomOf f "") f

  -- canInv,canAssoc  presume  
  -- ***(WithCanAssoc,Yes)***  for the coefficient ring

  canInv f = if  isZero f  then  error $ ("canInv 0 \nin  "++) $ 
                                                   showsDomOf f "\n"
             else                ct f $ canInv $ lc f

  canAssoc f = if  isZero f  then  f
               else                cPMul (inv $ canInv $ lc f) f

  gcD []     = error "gcD []  :: RPol a \n"
  gcD (f:fs) = 
    let
      { z = zeroS f;  aR = snd $ baseGCDRing (sample f) $ dom f }
    in
    case  isGCDRing aR
    of
      Yes -> foldl rpolgcd_ z $ filter (/=z) (f:fs)
      _   -> 
          error $ ("gcD fs,"++) $
              ("\nlength fs =  "++) $ shows (genericLength (f:fs)) $
              showsWithDom f "head fs" "" 
              "\n(IsGCDRing,Yes)  needed for the coefficient ring\n"

  hasSquare _ = 
      error "hasSquare (RPol ..):  not implemented, so far, sorry\n"
  toSquareFree _ = 
   error "toSquareFree (RPol ..):  not implemented, so far, sorry\n"



rpolgcd_ :: (GCDRing a) => RPol a -> RPol a -> RPol a
  -- LOCAL.  
  -- GCD for R = RPol a.  It is similar to gcd for Pol:  
  -- if  u = leadingVar(f)  >  v = leadingVar(g)  then   gcd g cs,
  -- where  ci <- R   are the coefficients of  f  respectively to  u
  -- - similar is the case  u < v.
  -- If  u = v  then bring f,g to univariate fu,gu from  R[u],  find
  -- upolGCD fu gu,  - here  rpolgcd_  recurses to r-pols smaller in
  -- leading variable, - and return from R[u] to R.


rpolgcd_  r@(RPol f a t aDom) (RPol g _ _ _) = toR $ gc f g
  where
  cp    = rvarsTermCp t
  rDom  = upGCDRing r eFM
  toR x = RPol x a t aDom
 
  gc (CRP a)           g                   = 
                                           CRP $ gcD (a:(pCoefs g))
  gc f                 (CRP a)             = 
                                           CRP $ gcD (a:(pCoefs f))

  gc f@(NRP u _ cf tl) g@(NRP v _ cf' tl') = case  cp u v  of

    LT -> foldl gc (gc f cf') $ coefs v tl'
    GT -> foldl gc (gc g cf ) $ coefs u tl 
    _  -> rpolRepr $ rFromHeadVarPol u $ Pgcd_.upolGCD_generic fu gu
                        where
                        [fu,gu] = map (rHeadVarPol rDom . toR) [f,g]
              
  coefs _ (CRP a)           = [CRP a]
  coefs u f@(NRP v _ cf tl) = if  u==v  then  cf:(coefs u tl)
                              else            [f]



--------------------------------------------------------------------
rpolfromexpr_ :: (CommutativeRing a) => 
                    RPol a -> Expression String -> ([RPol a],String)

  -- Parse r-polynomial given a sample r-polynomial and expression.
  --
  -- In the input string the variables are the substrings of kind
  -- pref++indexString  - like the ones produced by  showsRPolVar.
  --
  -- SO FAR, it requires a ring `a' with UNITY.
  -- Example:
  -- expression <-->  " 2*(u_31_0+u_1_4)^2 "

rpolfromexpr_  smp@(RPol _ c vt _)  e =  
  case 
      (unity c, rvarsTermRanges vt)
  of
    (un,ranges) -> rd e
      where
      rd e = case  fromExpr un e  of    -- first try coefficient

        ([c],"") -> ([ct smp c], "")
        _        -> 
          (case  e  of
            (E (L "-") []   [e2]) -> rd' "-u" ([],"") (rd e2)
            (E (L "-") [e1] [e2]) -> rd' "-"  (rd e1) (rd e2)
            (E (L "+") [e1] [e2]) -> rd' "+"  (rd e1) (rd e2)
            (E (L "*") [e1] [e2]) -> rd' "*"  (rd e1) (rd e2)
            (E (L "/") [e1] [e2]) -> rd' "/"  (rd e1) (rd e2)
            (E (L "^") [e1] [e2]) -> pw (rd e1) $ fromExpr (1::Z) e2
            (L s)                 -> variable $ dropWhile (/= '_') s
            _                     -> ([], msg "Wrong expression\n")
          )
          where
          msg = ("rpolfromexpr_ samplePol exr,"++)
                .("\nin      "++) .showsDomOf smp
                .("\nexpr =  "++) .showsExpr e .("\n\n"++)

          rd' "-u" _        ([f],"") = ( [-f],  "" )
          rd' "-"  ([f],"") ([g],"") = ( [f-g], "" )
          rd' "+"  ([f],"") ([g],"") = ( [f+g], "" )
          rd' "*"  ([f],"") ([g],"") = ( [f*g], "" )
          rd' "/"  ([f],"") ([g],"") = 
                case  
                     divide_m f g  
                of
                  Just q -> ([q], "")
                  _      -> ([],  msg "Failed to divide with `/'\n")

          rd' _    ([_],"") pair     = pair
          rd' _    pair     _        = pair

          pw  ([f],"" ) ([n],"" ) = ([f^n], "" )
          pw  ([_],"" ) (_  ,msg) = ([]   , msg)
          pw  (_  ,msg) ([_],"" ) = ([]   , msg)
 
                      -- parse r-variable expression to r-polynomial 
          variable (_:d:xs) = indexStrToRPol (d:xs)
          variable s        = ([], msg$ ("Variable expression  "++)$
                                        shows s $ "  needs index\n"
                              )
          indexStrToRPol xs = 
            let  
                         -- example:  separate "12_03_0" = [12,34,0]
              separate xs = case  span (/= '_') xs
                            of
                              (ys, _:zs) -> ys:(separate zs)
                              (ys, []  ) -> [ys]

              readZ s = case  reads s  :: [(Z,String)]  of
                                                 [(n,"")] -> Just n
                                                 _        -> Nothing
            in
            case  allMaybes $ map readZ $ separate xs
            of
              Nothing -> 
                    ([], msg "\n\nFailed to parse variable index\n")
              Just v  -> 
                   if  isInRange v  then  ([varToRPol smp un v], "")
                   else
                     ([], msg "\nr-variable index out of range\n")

          isInRange js = 
               and $ zipWith (\j (l,h)-> l <= j && j <= h) js ranges

  ;















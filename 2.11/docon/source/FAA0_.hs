--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module FAA0_    

  -- Free Associative Algebra  (non-commutative polynomials)
  -- over a Commutative Ring
  (
   module FreeMonoid,

   FAA(..), FAAMon, FAAVarDescr,
   faaMons, faaFreeMOrd, faaVarDescr, faaN, faaVMaps, faaFreeMOId,
   faaFreeMOComp, faaLM, faaLeastMon, faaLPP, reordFAA ,
   faaMonMul, faaMonFAAMul, cToFAA, faaToHomogForms

   -- instances for FAA :
   --   Dom, Eq, Show,  Cast (FAA a) (FAAMon a), 
   --                   Cast (FAA a) [FAAMon a], Cast (FAA a) a,
   --   PolLike FAA,    Set .. Ring, Fractional
  )

where
import qualified Data.Map as Map (lookup)

import Maybe (catMaybes) 

import DPrelude (Cast(..), ct, ctr, PropValue(..), Expression(..), 
                 Z, Comparison, sortBy, allMaybes, partitionN, 
                 less_m, showsExpr
                )
import Categs
import SetGroup
import RingModule
import UPol_      (PolLike(..), PPOId, PolVar, lc)
import FreeMonoid




--------------------------------------------------------------------
type FAAMon a = (a, FreeMonoid) 

type FAAVarDescr = (Maybe Z, (Z -> Maybe PolVar, PolVar -> Maybe Z))
  --                mn        toStr              fromStr     
  --
  -- mn       is as in FreeMonoid.
  -- variable indices range in   iRange = [1 .. upp],  
  -- upp = n  (case mn = Just n)  or  infinity  (case mn = Nothing).
  -- toStr    shows variable as string, it is defined on iRange  and 
  --          produces  Just str  for some (showable) indices.  
  -- fromStr  is the reverse to  toStr,  it produces  Just index
  --          for a variable name which corresponds to some index
  --          in iRange. 


data FAA a =  FAA [FAAMon a] a FreeMOrdTerm FAAVarDescr (Domains1 a)
  --
  -- (element of) Free associative algebra 
  -- - Non-commutative polynomial.



instance Dom FAA where  dom    (FAA _ _ _ _ d) = d
                        sample (FAA _ c _ _ _) = c

faaMons         :: FAA a -> [FAAMon a]
faaFreeMOrd     :: FAA a -> FreeMOrdTerm
faaVarDescr     :: FAA a -> FAAVarDescr
faaN            :: FAA a -> Maybe Z
faaVMaps        :: FAA a -> (Z -> Maybe PolVar, PolVar -> Maybe Z)
faaFreeMOId     :: FAA a -> PPOId
faaFreeMOComp   :: FAA a -> Comparison FreeMonoid

faaMons     (FAA ms _ _ _  _) = ms
faaFreeMOrd (FAA _  _ o _  _) = o
faaVarDescr (FAA _  _ _ vd _) = vd
faaN                          = fst . faaVarDescr 
faaVMaps                      = snd . faaVarDescr 

faaFreeMOId   = freeMOId   . faaFreeMOrd
faaFreeMOComp = freeMOComp . faaFreeMOrd

faaLM, faaLeastMon :: Set a => FAA a -> FAAMon a

faaLM f = case faaMons f 
          of
          m:_ -> m
          _   -> error $ ("faaLM 0  in  FAA R"++) $ 
                         (",\nR = "++) $ showsDomOf (sample f) "\n"

faaLeastMon f = case faaMons f of

         m:ms -> last (m:ms)
         _    -> error $ ("faaLeastMon 0  in  FAA R"++) $
                         (",\nR = "++) $ showsDomOf (sample f) "\n"

faaLPP :: Set a => FAA a -> FreeMonoid
faaLPP               f     =  case faaMons f of

       (_, p): _ -> p
       _         -> error $ ("faaLPP 0  in  FAA R"++) $ 
                          (",\nR = "++) $ showsDomOf (sample f) "\n"


instance Eq a => Eq (FAA a) where  
                            f == g =  (faaMons f) == (faaMons g)


reordFAA :: FreeMOrdTerm -> FAA a -> FAA a 
                                          -- bring to given ordering
                                          --
reordFAA o (FAA ms c _ vd dom) = FAA (sortBy cmp ms) c o vd dom
                                    where
                                    cmp (_, p) (_, q) = cp q p
                                    cp                = freeMOComp o


--------------------------------------------------------------------
instance AddGroup a => Cast (FAA a) (FAAMon a)
  where
  cast mode (FAA _ c o vd d) (a, p) =  FAA mons c o vd d
          where
          mons = if  mode == 'r' && isZero a  then []  else [(a, p)]


instance AddGroup a => Cast (FAA a) [FAAMon a]
  where
  cast mode (FAA _ c o vd d) mons =  FAA ms c o vd d
    where                                       -- order NOT checked
    ms = if  mode /= 'r'  then  mons
         else                   filter ((/= z) . fst) mons
    z  = zeroS c


instance AddGroup a => Cast (FAA a) [(a, [(Z, Z)])]
  where
  cast mode f preMons = 
 
           cast mode f [(a, FreeM (faaN f) ps) | (a, ps) <- preMons]

instance Ring a => Cast (FAA a) a
  where
  cast mode (FAA _ _ o vd d) a =  case (mode, isZero a) of

                ('r', True) -> FAA []                       a o vd d
                _           -> FAA [(a, FreeM (fst vd) [])] a o vd d



--------------------------------------------------------------------
instance PolLike FAA
  where
  pPPO     _   = error "pPPO (FAA _):   use  faaNCPPO  instead\n"
  lm       _   = error "lm (FAA _):   use  faaLM  instead\n"
  lpp      _   = error "lpp (FAA _):  use  faaLPP  instead\n"
  pCoef    _ _ = error "pCoef  is not defined for  FAA R\n"
  pFromVec _ _ = error "pFromVec  is not defined for  FAA R\n"
  pToVec   _ _ = error "pToVec  is not defined for  FAA R\n"
  pDeriv   _   = error ("pDeriv (FAA _):   derivative skipped, so "
                        ++"far, for non-commutative polynomial\n"
                     )
  pMapPP  _ _ = error "pMapPP f (FAA _):  not defined\n"
  pDivRem _ _ = error "pDivRem  is not defined so far for  FAA R\n"
  pValue  _ _ = error "pValue   is not defined so far for  FAA R\n"

  pIsConst f = case faaMons f of (_, p): _ -> p == unity p
                                 _         -> True

  pVars f = catMaybes $ map toStr js  
                   where 
                   (mn, (toStr, _)) = faaVarDescr f
                   js               = case mn of Just n -> [1 .. n]
                                                 _      -> [1 ..  ]
  pCoefs  = map fst . faaMons

  pTail f = case faaMons f of

           _:ms -> ct f ms
           _    -> error $ ("pTail 0  in  FAA R"++) $ 
                           (",\nR = "++)$ showsDomOf (sample f) "\n"

  pFreeCoef (FAA mons c _ _ _) =
                  let 
                    {z = zeroS c;  (a, p) = last mons}
                  in
                  if null mons then  z
                  else               if  p == unity p  then a else z

  ldeg f = case faaMons f
           of
           (_, p): _ -> sum $ map snd $ freeMRepr p
           _         -> error $ ("ldeg 0  in  FAA R"++) $ 
                          (",\nR = "++) $ showsDomOf (sample f) "\n"

  deg f = case  map (sum . map snd . freeMRepr . snd) $ faaMons f
          of
          d:ds -> maximum (d:ds)
          _    -> error $ ("deg 0  in  FAA R"++) $ 
                          (",\nR = "++) $ showsDomOf (sample f) "\n"

  degInVar for0 i f =
    --
    -- Put degree of i-th variable in monomial to be the sum of
    -- degrees of its occurences. 
    -- Example:   if    faaMons f = [(1,1),(2,2),(5,3),(2,6)] 
    --            then  degInVar _ 2 f = 8
    (case  
         (i >= 0, faaMons f)
     of
     (False, _ ) -> error $ msg "\n\nPositive i needed\n"
     (_,     []) -> for0
     (_,     ms) -> maximum $ map (degInMon i . freeMRepr . snd) ms
    )
    where
    degInMon i = sum . map snd . filter ((== i) . fst)

    msg = ("degInVar for0 i f,  \ni = "++) . shows i .
          ("\nf <- FAA R,  R = "++) . showsDomOf (sample f) 


  pCDiv f c = let (cs, pps) = unzip $ faaMons f
              in
              case allMaybes [divide_m a c | a <- cs]
              of
              Just quots -> Just $ ct f $ zip quots pps
              _          -> Nothing

  pMapCoef mode f g = 
                      cast mode g [(f a, pp) | (a, pp) <- faaMons g]
 
  varPs a f = [ctr f [(a, FreeM mn [(i, 1)])] | i <- range]
                               where
                               mn    = faaN f
                               range = case mn of Just n -> [1 .. n]
                                                  _      -> [1 ..  ]

--------------------------------------------------------------------
neg_ :: AddGroup a => FAA a -> FAA a                    -- f -> -f
neg_                  f =  ct f [(neg a, pp) | (a, pp) <- faaMons f]
 
add_ :: AddGroup a => FAA a -> FAA a -> FAA a

add_ (FAA monsF c o _ _) g =  ct g $ pa monsF $ faaMons g
  where
  (z, cp) = (zeroS c, freeMOComp o)

  pa []      msG     = msG
  pa msF     []      = msF
  pa (m:msf) (n:msg) =
      let
         {(a, p) = m;  (b, q) = n;  d = add a b}
      in
      case cp p q
      of
      GT -> m:(pa msf (n:msg))
      LT -> n:(pa (m:msf) msg)
      _  -> if d == z then  pa msf msg  else  (d,p):(pa msf msg)

--------------------------------------------------------------------
faaMonMul :: Ring a =>  a -> FAAMon a -> FAAMon a -> [FAAMon a]
                     -- zero

faaMonMul z (a, p) (b, q) = let c = a*b in  if c == z  then  []
                                            else      [(c, mul p q)]


faaMonFAAMul :: Ring a => FAAMon a -> FAA a -> (FAA a, FAA a)
  --
  -- multiply FAA element f by FAA monomial m forming the pair 
  -- (m*f, f*m)
  --
faaMonFAAMul (a, p) f = 
                      (ctr f [(a*b, mul p q) | (b, q) <- faaMons f],
                       ctr f [(b*a, mul q p) | (b, q) <- faaMons f]
                      )

times_ :: Ring a => (a -> i -> a) -> FAA a -> i -> FAA a
times_              t                f        n =
                      
                            ctr f [(t a n, p) | (a, p) <- faaMons f]
  -- t = `times' for `a'

                                               -- coefficient to FAA
cToFAA :: Ring a => 
          FreeMOrdTerm -> FAAVarDescr -> Domains1 a -> a -> FAA a
cToFAA    ord             varDescr       dom           a =

      FAA mons a ord varDescr dom
      where 
      mons = if isZero a then [] else [(a, FreeM (fst varDescr) [])]
                       

faaToHomogForms ::
         (AddGroup a, Eq b) => (FreeMonoid -> b) -> FAA a -> [FAA a]
                               -- weight map
faaToHomogForms w f =

 map (ct f) $ partitionN (\ (_, p) (_, q) -> w p == w q) $ faaMons f
       --
       -- (non-ordered) list of homogeneous forms of non-commutative 
       -- polynomial over `a'  with respect to 
       -- weight :: PowerProduct -> b



instance Ring a => Show (FAA a) 
  where 
  showsPrec _ (FAA mons c _ varDescr dom) = 

  -- If  a  is and Ordered ring, then the mode `ord'  is set which
  -- writes ..- m  instead of ..+(-m) for the negative coefficient
  -- monomials.
  -- If  a  has unity  then unity coefficient images  are skipped.

   (case (zeroS c, unity_m c, Map.lookup Ring dom)
    of
    (zr, unM, Just (D1Ring rR)) -> ss zr unM $ isOrderedRing rR
    _                           ->
      error $ msg "\n\nRing term  not found in coefficient domain\n"
   )
   where
   msg  = ("shows f str,  \nf <- FAA R,  R = "++) . showsDomOf c . 
          (",\nPower products = "++) . 
          shows (map (freeMRepr . snd) mons)

   msg' = ("\n\nWrong representation for  f:\n"++)

   ss zr unM ordered =  ('(':) . wr mons' . (')':)
     where
     mons' = [(c, freeMRepr v) | (c, v) <- mons]

     wr mons = case (ordered, mons) of

       (_  , []           ) -> ('0' :)
       (_  , [m]          ) -> wMon m
       (Yes, m: (c, p): ms) ->
         if
           less_m c zr  then  
                        wMon m . (" - "++) . wr ((neg c, p): ms)
         else           wMon m . (" + "++) . wr ((c, p)    : ms)

       (_,   m:ms         ) -> wMon m . (" + "++) . wr ms

     wMon (c, pp) =
       let 
          pp_str = wpp varDescr pp ""
       in
       case (unM, pp_str)
       of
       (_      , []) -> shows c
       (Nothing, _ ) -> shows c . ('*':) . (pp_str++)
       (Just un, _ ) -> if c == un then (pp_str++)
                        else           shows c . ('*':) . (pp_str++)

     wpp :: FAAVarDescr -> [(Z, Z)] -> String -> String
                                          -- writing `power product'
     wpp _  []           = id
     wpp vd ((x, e): pp) = 
       case 
           (e > 0, fits x $ fst vd, fst $ snd vd) 
       of
         (False, _,     _     ) -> 
                       error $ msg $ msg' 
                         "non-positive exponent for some variable\n"
         (_,     False, _     ) -> error $ msg $ msg'
                                     "variable index out of range\n"
         (_,     _,     vToStr) ->
           case 
               (vToStr x, e, pp)
           of
           (Nothing, _, _) -> 
                error $ msg $ msg' $
                  ("unprintable variable index:  "++) $ shows x "\n"

           (Just str, 1, []) -> (str++)
           (Just str, 1, pp) -> (str++) . ('*':) . wpp vd pp
           (Just str, n, []) -> (str++) . ('^':) . shows n
           (Just str, n, pp) -> 
                     (str++) . ('^':) . shows n . ('*':) . wpp vd pp

     fits x (Just n) = 0 < x && x <= n
     fits x _        = 0 < x 


--------------------------------------------------------------------
instance CommutativeRing a => Set (FAA a)
  where
  compare_m    = compareTrivially
  fromExpr     = fromexpr_
  showsDomOf f = ("FAA("++) . shows (faaN f) . (',':) . 
                 showsDomOf (sample f) . (')':)

  baseSet _ _ = error "finish  baseSet (FAA..)\n"

 

fromexpr_ :: CommutativeRing a =>
                     FAA a -> Expression String -> ([FAA a], String)
  -- LOCAL.
  -- Parse from expression non-commutative polynomial given a sample 
  -- one.
  -- So far, it requires a ring `a' with UNITY.

fromexpr_ smp e =  case (unity $ sample smp, faaVarDescr smp) of

  (u, vd) -> rd e
    where
    rd e = case fromExpr u e of   -- first try coefficient

      ([c], "") -> ([ctr smp c], "")
      _         ->
        (case  e  of
          (E (L "-") []   [e2]) -> rd' "-u" ([],"") (rd e2)
          (E (L "-") [e1] [e2]) -> rd' "-"  (rd e1) (rd e2)
          (E (L "+") [e1] [e2]) -> rd' "+"  (rd e1) (rd e2)
          (E (L "*") [e1] [e2]) -> rd' "*"  (rd e1) (rd e2)
          (E (L "/") [e1] [e2]) -> rd' "/"  (rd e1) (rd e2)
          (E (L "^") [e1] [e2]) -> pw (rd e1) (fromExpr (1::Z) e2)
          (L s)                 -> variable s vd 
          _                     ->
                                ([], msg "\n\nWrong expression\n")
        )
        where
        msg = ("fromExpr sampleFAA expr,"++) . 
              ("\nsampleFAA =   "       ++) . shows smp . 
              ("\n <-  "                ++) . showsDomOf smp .
              ("\nexpr =  "             ++) . showsExpr e

        rd' "-u" _        ([f],"") = ([-f ], "")
        rd' "-"  ([f],"") ([g],"") = ([f-g], "")
        rd' "+"  ([f],"") ([g],"") = ([f+g], "")
        rd' "*"  ([f],"") ([g],"") = ([f*g], "")
        rd' "/"  ([f],"") ([g],"") = case divide_m f g of

               Just q -> ([q], "")
               _      -> ([], msg "\n\nFailed to divide with `/'\n")

        rd' _    ([_], "") pair     = pair
        rd' _    pair      _        = pair
 
        pw ([f], "" ) ([n], "" ) = ([f^n], "" )
        pw ([_], "" ) (_,   msg) = ([],    msg)
        pw (_,   msg) ([_], "" ) = ([],    msg)

                                   -- read nc-monomial from variable
        variable s (mn, (_, fromStr)) =
          case
              fromStr s   
          of
          Nothing -> 
               ([], msg ("\n\nUnreadable variable:  " ++ s ++ "\n"))

          Just i  -> ( [ct smp (u, FreeM mn [(i, 1)])],  "" )


--------------------------------------------------------------------
instance CommutativeRing a => AddSemigroup (FAA a)
  where
  add       = add_
  zero_m f  = Just $ ctr f $ zeroS $ sample f
  neg_m     = Just . neg_
  times_m f = Just . (times_ times f)

  baseAddSemigroup _ _ = error "finish  baseAddSemigroup (FAA..)\n"

instance CommutativeRing a => AddMonoid (FAA a)

instance CommutativeRing a => AddGroup (FAA a)
  where
  baseAddGroup _ _ = error "finish  baseAddGroup (FAA..)\n"
                
--------------------------------------------------------------------
instance CommutativeRing a => MulSemigroup (FAA a)
  where
  unity_m f = fmap (ct f) $ unity_m $ sample f

  mul f g = case faaMons f of 
                       []  -> zeroS f
                       m:_ -> (fst $ faaMonFAAMul m g) + (pTail f)*g

  inv_m f = if  isZero f || not (pIsConst f)  then  Nothing
            else                          fmap (ct f) $ inv_m $ lc f

  divide_m f g =
    let
       zeroP = zeroS f
    in
    case (f == zeroP, g == zeroP)
    of
    (True, _   ) -> Just zeroP
    (_   , True) -> Nothing
    _            -> let (q, r) = pDivRem f g
                    in  
                    if isZero r then Just q  else Nothing

  divide_m2 _ _ =
          error "divide_m2  is not defined for ..=> FAA a  so far\n"
  root _ _ = error "root  is not defined for ..=> FAA a  so far\n"

  -- power  is the default

  baseMulSemigroup _ _ = error "finish  baseMulSemigroup (FAA..)\n"


instance (CommutativeRing a, MulMonoid a) => MulMonoid (FAA a)

instance CommutativeRing a => Num (FAA a)  
  where 
  negate = neg
  (+)    = add
  (-)    = sub
  (*)    = mul
  signum _ = error ("signum  is not defined for ..=> FAA a  "++
                    "\n(non-commutative polynomials)\n"
                   ) 
  abs    _ = error ("abs  is not defined for ..=> FAA a  "++
                    "\n(non-commutative polynomials)\n"
                   ) 
  fromInteger _ = 
             error "fromInteger  to (FAA _):  use  fromi, fromi_m\n"


instance CommutativeRing a => Fractional (FAA a) 
  where
  (/) = divide
  fromRational _ = 
             error ("fromRational  to (FAA _):  \n"++
                    "use  fromi, fromi_m  combined with  divide_m\n"
                   )

instance CommutativeRing a => Ring (FAA a)
  where
  fromi_m f = fmap (ctr f) . fromi_m (sample f)

  baseRing _ _ = error "finish  baseRing (FAA..)\n"


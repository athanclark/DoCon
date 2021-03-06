--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module Pfact2_ (factorOverFinField_2)

  -- Polynomial factorization.  Case  F[t][x],  F any finite field.
  -- This is the implementation support for the instance
  --                                          Factorization (Pol a).
  -- All needed from here is reexported by Pol.

where
import qualified Data.Map as Map (empty)

import Maybe (fromJust)
import List  (find    )

import Prelude hiding(maximum)

import DPrelude (Z, Comparison, maximum, ct, ctr, allMaybes,
                 showsWithDom
                )
import Categs (Dom(..),ResidueE(..), Factorization, Subring(..),
               Operation_Subring(..), OpName_Subring(..)
              )
import SetGroup   (unity, zeroS, isZero, divides, gatherFactrz)
import RingModule (Ring(..), GCDRing(..), FactorizationRing(..),
                   Field(), remEuc, eucIdeal, upField
                  )
import ResEuc0_ (Residue(..))
import UPol_    (PolLike(..), UPol(..), lc, pCont, varP, cToUPol,
                 upolMons, deg0, pmul
                )
import UPol0_  (upolSubst)
import Pgcd_   (upolGCD_Chinese                   )
import Pfact0_ (henselLift, smallInLattice_triang_)
import Pfact__ 
       ( factorUPol_finField  {- ,FactorizationRing UPol-} )





--------------------------------------------------------------------
factorOverFinField_2 :: 
        Field fF => UPol (UPol fF) -> Factorization (UPol (UPol fF))

{- 
factors  f <- A[x],  A = F[t],  F  a finite field.

COST < O( r^4*|f|^3 + r^4*(log_q r)^3*|f|^2 +
          r^3*|f|*(log (r*|f|))^3*s*q*(log q)
        )                                         operations in F,
where  r = deg_x f, |f| = deg_t f, card F = q^s.

METHOD 
(see [Me3,'a'], and [Me3] adopts the method by [CG,section ?].

Step sq  Reduce the task to factoring of a square free  f, 
-------  deg f > 1,  content f = 1,  lc (lc f) = 1

Step p   Find irreducible over  F  p  in  GF(q)[t]  for separating
------   projection:  
         p  does not divide  lc f  and  f mod p  is square free

Step f   Factor over  FF = A/(p)
------   Factor  f mod p  to  [(h1 mod p)...]  by Berlekamp method. 
         If (f mod p) is prime, then f is prime. It remains the case
         l1 = deg h1 < deg f = r,   h1 <- A[x]  is representative
         for (h1 mod p), coefficients reduced by p.

Step h0  Find unique prime factor  h0  of  f  such that 
-------                               (h1 mod p) divides (h0 mod p)
  This loop stops at  m = deg h0 <= r.
  For  m = l1, l1+1 ...  do
   {
    {h0-k}  k = min [ k':  |p|*k'*l1 > m*|f| + r*|f| ]     
                           -- condition (A-h0-1) ---        (A-h0-1)
    {h0-h}  h = HenselLift p f k h1
            so that h = h1 (mod p), (h mod p^k) divides (f mod p^k)
                    lc_x h = 1, deg h = l1

    {h0-l}  Build basis  M  for lattice  L = L(m,k)  over  A
            L= {v<-A[x]: deg v <= m,(h mod p^k) divides (v mod p^k)}
            is generated by 
                           M = [h*x^(m-l1) .. h, p^k*x^m .. p^k].
            Consider here  v <- A[x]  as vector of coefficients.

    {h0-lt}  Bring M to special upper-triangular regular  B  of size
             (m+1)x(m+1),  rows of B  generating the same lattice  L

    {h0-sv}  Search for small non-zero vector  b  in L  - 
             for  u <- A^(m+1)  such that 0 /= b = u*B  satisfies
                      |p|*k*l1 > m*|f| + r*|b|              (A-h0-2)
             This is done by deriving from B  the bounds for  |u(i)|
             and putting linear equations on unknown  u(i)(j) <- F.

    {h0-e}  If  b  with the condition (A-h0-2) it is not found, then 
                                              continue with next  m.
            Otherwise,  b/h0 <- A,  and  h0 = b/content(b).
   }
Addition
--------
The below program finds the factorization  hRs = [h1R,..]  for 
fR = (f mod p)  and then repeats  Step h0  is the following manner.
It finds  h0  corresponding to  h1R,  removes the factorization of
(h0 mod p)  from  hRs  obtaining  new_hRs,  and continues  Step h0  
with  new_f = f/h0,  new_hRs.  That is the further  h1, l1, 
Hensel lift, L  ... are built for  new_f, h1R' = head new_hRs.
This accumulates the factorization  [h0..]  of  f  so that  Step p, 
Step f  perform only once.
This is correct because the first found  p  at  Step p  separates
all factors in  f.
-}
--------------------------------------------------------------------

factorOverFinField_2 f =
  if
    isZero f  then  error $ msg "f = 0\n"
  else
    let  c     = pCont f    -- gcd(coeffs)
         g     = divByCoef f c
         pairs = [(ct f b, i) | (b, i) <- factorUPol_finField c]
    in   
    pairs++(factorPrimitive $ canAssoc g)
  where
  msg = ("factorOverFinField_2 f,"++) . showsWithDom f "f" "" . 
        ('\n':)
  (a, dA, v)     = (sample f, dom f, head $ pVars f)
  rA             = snd $ baseRing a dA      
  (Just q, opsA) = (subringChar rA, subringOpers rA)
  divByCoef f    = fromJust . pCDiv f 

  -- :: (Field fF, FactorizationRing (UPol fF)) => 
  --               UPol (UPol fF) -> Factorization (UPol (UPol fF))

  factorPrimitive f =              -- here f is non-zero, primitive,
    let                            -- in canonical associated form
      Just wpA  = lookup WithPrimeField opsA
      invFrobA  = snd $ frobenius wpA
      substXq h = 
               ct h [(b, e*q) | (b, e) <- upolMons h]  -- h-> h(x^q)
      divideTExps h = 
        let 
             -- for h <- A[x] find q-root in A for each coefficient,
             -- or return (False,h) if this is impossible
          (cs, es) = unzip $ upolMons h 
        in
        case allMaybes $ map invFrobA cs   
        of
        Nothing  -> (False, h)
        Just mbs -> case  allMaybes mbs
                    of
                    Just c's -> (True , ct f $ zip c's es)
                    _        -> (False, h)

      mons          = upolMons f
      (coefs, exps) = unzip mons
      (quots, rems) = unzip [quotRem n q | n <- exps]
      --------------------------------------------------------------
    in
    case (deg f, lc f)
    of
    (1, _) -> [(f, 1)]
    (0, a) -> if deg a == 0 then []                    -- f <- F\{0}
               else              [(f, 1)]
    _      ->            -- reducing to square free f [Me3,'ap.sq2']
      if any (/= 0) rems  
      then
          let  
            f'    = pDeriv [(1, 1)] f       -- df/dx /=0
            g     = upolGCD_Chinese f f'
            fQuot = canAssoc (f/g)
          in  
          if deg g == 0 then [(p, 1) | p <- factorSquareFree f]
          else     
          gatherFactrz
                    ((factorPrimitive g) ++ (factorPrimitive fQuot))
      else 
          -- f = f1(x^q)
      let
        mons'    = zip coefs quots          -- f1 = sum[ci*x^(i/q)..]
        f1       = ct f mons'
        (hs, js) = unzip $ factorPrimitive f1
                                             -- f1 is smaller in deg
                             -- f = product [(hk(x^q))^jk | k <- js]

        pairs = zip (map divideTExps hs) js

            -- For each item ((True,h),j) from  pairs,
            -- h is a factor (not necessarily prime) for f of
            --                                     multiplicity j*q;
            -- for  ((False,h),j),  h(x^q) is a prime factor for f
            -- with multiplicity j

        factorFurther ((False, h), j) = [(substXq $ canAssoc h, j)]
        factorFurther ((True,  h), j) = 
                           [(p, i*j*q) | 
                            (p, i) <- factorPrimitive $ canAssoc h]
      in
      gatherFactrz $ concat $ map factorFurther pairs


  -- :: (Field fF..) => UPol (UPol fF) -> [UPol (UPol fF)]
  --
  factorSquareFree f =  
    --
    -- Here  f  is non-zero, primitive, square free, in canonical
    -- associated form. See  Step p.
    -- A bit of optimization applied: for the widely met case of
    -- p = t + a,  the substitution applies to reduce the task to
    -- the case  p = t.
    let                 
      msgFactorSquareFree =
         ("factorSquareFree g,"++) . showsWithDom f "g" "" . ('\n':)
      (c, dF)            = (sample a, dom a)
      (zr, un, zrA, unA) = (zeroS c, unity c, zeroS a, unity a)
      (zrAX, zrFX)       = (zeroS f, cToUPol v dF zr)
      (t, x)             = (varP un a, varP unA f)
      degT f = if isZero f then 0                 -- | |  for A[x]
               else           maximum $ map (deg . fst) $ upolMons f

      polHasSquare f =                -- here f <- k[x],  deg f > 1,
                hasSq $ 
                map snd $ upolMons f  -- k a finite field of char= q
                            where
                            hasSq exps = all (divides q) exps ||
                                         deg (gcD [f, f']) > 0
                            f' = pDeriv [(1, 1)] f  -- df/dx  (/= 0)

      p = fromJust $ find separates $ primes unA
                               -- Step p: find separating prime in A
           where
           separates g = not ((divides g $ lc f) || polHasSquare fG)
             where
             fG = UPol (filter ((/= zrByG) . fst) 
                               [(toByG a, e) | (a, e) <- upolMons f]
                       ) zrByG v dByG
             gI      = eucIdeal "be" g [] [] [(g, 1)]          
             zrByG   = Rse zrA gI dA  
             dByG    = upField zrByG Map.empty
             toByG a = Rse (remEuc 'c' a g) gI dA      -- A -> A/(g)

      (oP, pc0) = (deg p, pFreeCoef p)                  -- |p| ...
      pc0p      = ct p pc0
      toShift   = oP == 1  &&  pc0 /= zr
      (pS, fS)  =
             if toShift then
                (t, pMapCoef '_' (\ c -> upolSubst c (t-pc0p) []) f)
             else (p, f)

      iI      = eucIdeal "be" pS [] [] [(pS, 1)] 
      unFF    = Rse unA iI dA  
      dFF     = upField unFF Map.empty
      unFFX   = cToUPol v dFF unFF                     -- 1 of FF[x]
      toFFX f = ctr unFFX [(ctr unFF a, e) | (a, e) <- upolMons f]
                                                      -- A[x]->FF[x]
      fromFFX fR = ct f [(resRepr r, e) | (r, e) <- upolMons fR]
      --------------------------------------------------------------
      -- A bit of specialization for  pS = t.
      -- Here  FF = A/(pS) =iso= F,   iI  is implicit.
      -- This small optimization is used only in finding  fRfactn.

      toOverF f = ctr zrFX [(pFreeCoef a, e) | (a, e) <- upolMons f]
                                                   -- A[x] <-> F[x]
                                                   -- for F =iso= FF
      fromOverF fR = ct f $ [(ctr unA r, e) | (r, e) <- upolMons fR]
                            -- ct ?
      (fR, fR_1) = (toFFX fS, toOverF fS)
      fRfactn   =                    -- Step f: factoring over A/(p)
            if  
              oP > 1  then  map fst $ factorUPol_finField fR 
            else 
            map (toFFX . fromOverF . fst) $ factorUPol_finField fR_1
      --------------------------------------------------------------
      -- Steps h0-lt, h0-sv.
      -- Build the lattice L(m,k,h) and search there for the non-
      -- zero vector  b  such that  |b| <= bBound.  

      smallInBoundedLattice h m pp bBound =   
                                         -- --> Nothing | Just b ...
        let
          (m1, l1, opp) = (m+1, deg h, deg pp)

          -- It starts  Step h0-lt:  reducing M = [h*x^(m-l1)..]
          -- to special triangular basis B =  E | T'
          --                                  00| pp*E'
          -- The whole program really processes only the part for 
          -- T',  the rest is presented by  l1 <- Z,  pp <- A.

          mT' = map (pToVec l1) $ toTriang 1 [pTail h]
                                                   -- |pTail h| < l1
          toTriang i (g:gs) =  
                        -- Prepending B1 part.
                        -- See [Me3, 'pr.h0-lt' (h0lt), 'cb.2h0-lt']
            if  i == (m1-l1)  then  g:gs
            else                    toTriang (i+1) ((x*g-ch):g:gs)
              where
              ch = if  deg0 'l' (-1) g < l1-1  then  zrAX
                   else               pMapCoef 'r' (mulRem (lc g)) h
              mulRem f g =
               if                               -- (f*g) mod pp in A
                  not toShift  then  remEuc '_' (f*g) pp
               else           
                -- optimization for  pp = t^k
                ct unA $ pmul zr cp mapMon (upolMons f) (upolMons g)
                  where
                  cp           = compare :: Comparison Z
                  mapMon (a,i) = if i < opp then (a, i) else (zr, 0)
        in
        smallInLattice_triang_ pp l1 bBound mT'
      --------------------------------------------------------------
      -- In  liftToPrimesOverA f' hRs
      -- f' is obtained from initial  fS  by dividing by previousely 
      -- found prime factors  h0(i)  of  fS.  
      -- See (METHOD, Addition) in comments above.

      liftToPrimesOverA _  []        = []
      liftToPrimesOverA f' [_]       = [f']
                                     --prime (f' mod pS) => prime f'
      liftToPrimesOverA f' (h1R:hRs) =
        let
          (r, f'R) = (deg f', toFFX f')
          (h1, g1) = (fromFFX h1R, fromFFX (f'R/h1R))   -- f'==h1*g1
          v1       = divByCoef (f'-h1*g1) pS            -- (mod pS)
          (oF, l1) = (degT f', deg h1)                  -- (|f'|,l1)
          
          smallInLattices m (h1, g1, v1, k1, ppS1) =     -- Step h0.
            if                   -- h1R is the proper factor for f'R
              m == r then  f'
            else
            let 
              (l1p, mf) = (l1*oP,m*oF)
              k         = 1 + (quot (mf+r*oF) l1p)  
                                           -- Step h0-k: min [k:...]
              (h, g, v, ppS) =
                          henselLift f' h1 g1 (Just v1) pS ppS1 k1 k
              bBound = 
                     let (qb, rb) = quotRem (l1p*k-mf) r
                     in
                     case compare rb 0  
                     of
                     EQ -> qb-1 
                     GT -> qb
                     _  -> error $ msg $ msgFactorSquareFree $
                                   msgLTPOverA
                                   ("liftToPrimesOverA:  "++
                                    "rem (l1p*k-mf) r  < 0  - ?\n"
                                   )  
            in
            case smallInBoundedLattice h m ppS bBound
            of              
            Nothing -> smallInLattices (m+1) (h, g, v, k, ppS)
            Just b  -> canAssoc $ divByCoef g (pCont g)
                                      where             -- Step h0-e
                                      g = pFromVec f' b 

          msgLTPOverA = ("liftToPrimesOverA f',"++) .
                                   showsWithDom f' "f'" "" . ('\n':)
          h0  = smallInLattices l1 (h1, g1, v1, 1, pS)
          h0R = toFFX h0
        in
        if  lc h1 == unA  then  
                          h0: (liftToPrimesOverA (f'/h0) 
                               [h | h <- hRs, not $ divides h h0R]
                              )
        else  error $ msg $ msgFactorSquareFree $ msgLTPOverA 
               ("liftToPrimesOverA:  (lc h1) /= 1.  \n"++
                "Maybe, factor (fS mod pS) produced some not normed"
                ++" polynomials from FF[x]. \n"
                ++"If so, then it is a DoCon bug\n"
               )  
      --------------------------------------------------------------
    in
    case (deg f < 2, toShift)
    of
    (True, _    ) -> [f]  
    (_   , False) -> liftToPrimesOverA f fRfactn
    _             ->
             map (pMapCoef '_' (\ c -> upolSubst c (t+pc0p) [])) $
                                        liftToPrimesOverA fS fRfactn






{- NOT READY  ***************************************************  

       Factoring in  F[x_1..x_t],  F any finite field.
           A.K.Lenstra method [Le].
This is reduction to the case of  F[x,y].
Denotations:  d(i) = deg_x(i),  d i f = deg_x(i) (f),  n(i) = d i f
Method
------
(Sqp)   Reduce to the case of a square-free  f  primitive by  x_1.
(Init)  Reduce to the case  1 < n(1) <= .. <= n(t)
        N(j) = product [n(i)+1 | i <- [j..t]
        k(j) = product [2*n(1)*n(i) - 1 | i <- [2..j-1]]
                                                     for j <- [3..t]
        f' = f modulo [x(j)-x(2)^k(j) | j <- [3..t]]  <- F[x1,x2]
(Factor2)  case  factor f'
           of
             [_] -> f   -- f is irreducible
             h's -> h' = find ((> 0). d 1) h's;  l1 = d 1 h'
(h0)  Lifting  h'  to irreducible factor  h0  of  f.
      Find the unique irreducible factor  h0  of  f  such that  
      h' divides h0'.
  for  m <- [l1 .. n(1)-1]
  do
    (h0.L) build the lattice basis
      L = {g <- F[x1..xt] | d 1 g <= m, d i g <= n(i) for i<-[3..t],
                            h' divides g' in F[x1,x2]
          }
      bs = {h'*x1^(i-l1) | i <- [l1..m]} ++ 
           {x1^i*product[ (x(j)-x2^k(j))^i(j) | j <- [3..t] ] | 
                                  i <- [0..m],
                                  i(j) <- [0..n(j)] for j <- [3..t],
                                  (i3..i(t)) /= 0
           } is a basis for L over F[x2]
      dim L over F(x2) = M = (m+1)*N(3)
      For  g <- F[x1..xt]  |g| =def= d 2 g
      rank L in (F[x2])^M = M - l1
      Represent  b(i) <- bs   as the elements of  F[x2][x1,x3..xt];
      y =def= x2
      A = F[y]
      Components of vector  b(i)  are numerated first by multiindex 
      al = [al(1),al(3)..al(t)]  being a power product in
      [x1,x3..xt].  Then all the multiindices in  bs  are joint and
      enumerated by the Integer index  j  with the maps  toMulty, 
      fromMulty.
    (h0.sv) search for small vector. 
      Reducing the basis bs, search for non-zero b  in  L  such that
      |b| < n2     (Basis reduction algorithm):
      case  search bs
      of
        Nothing -> m = m+1;  repeat loop
        Just b  -> 
                 h0 = b/c,  c = cont b w.r.to [x3..xt]  <- F[x3..xt]
      The indices in the found  b  are converted first to 
      multiindices by applying  fromMulty,  then the sparse vector
      converts to polynomial of  F[x1,x2...xt] ...
(Fin)  if  Step (h0)  yields  h0 /= 0  then  h0:(factor (f/h0))
       else                                  f  -- irreducible

data Multiindex = M [Integer] deriving(Eq,Show)            -- LOCAL
fromM (M js) = js                                          --
intLexComp :: Comparison [Z]                               --
intLexComp = lexListComp compare                           --
instance Ord Multiindex where                              --
                        compare (M js) (M ks) = intLexComp js ks 

factorOverFinField :: (Field fF) => Pol fF -> Factorization (Pol fF)
factorOverFinField  f@(Pol _ a o vars dF) = 
  -- Reduce to the monotoneous, positive degree case
  -- (that is                          1 <= n(1) <= n(2) ..<= n(t) )
  -- by the following method.
  -- Bring to lexicographic order, making  f';
  -- find permutation  pm'  on power product  (PP)  which makes
  -- degrees ordered  d1' <= d2' .. <= dt';
  -- apply  pm'  to each PP obtaining  f'';
  -- cut the initials in each PP in f'' corresponding to zero d'i
  -- and thus obtain  fr  (free of dummy variables);
  -- factor  fr  to  [(g,k) | ...];
  -- convert each  g  to the initial domain of  f:  prepend zero
  -- pp-part, permute pp-s back,  bring monomial list to initial
  -- ordering.
  let       
    (t, ns)   = (genericLength vars, polDegs [] f)
    (n's, pm) = unzip $ sortBy (compBy fst) $ zip ns [1..]
                                               -- n'(1) <=..<= n'(t)
    pm'       = permutRepr $ inv $ Pm pm
    (o',cp)   = (lexPPO t, ppoComp o)
    f'        = reordPol o' f
    f''       = polPermuteVars pm' f'         --polDegs [] f'' = n's
    zn        = genericLength $ takeWhile (==0) n's
    (zvs, nzvs)  = genericSplitAt zn vars
    (zeropp,o'') = (map (const 0) zvs, lexPPO (t-zn))
    fr = Pol (map restrictMon $ polMons f'') a o'' nzvs dF
               where
               restrictMon (a,Vec js) = (a, Vec $ genericDrop zn js)
    back g =
         ct f $ sortBy cpm [(b, Vec $ applyPermut pm (zeropp++js)) |
                            (b, Vec js) <- polMons g
                           ]                where
                                            cpm (_,p) (_,q) = cp q p
  in
  (case  (pIsConst f, ns==n's, zn)   of
     (True, _   , _) -> []
     (_   , True, 0) -> 
            [(canAssoc $ reordPol o p, i) | (p,i) <- factorMonot f']
                                             -- n(i) ordered and > 0
     _               -> 
                  [(canAssoc $ back g, i) | (g,i) <- factorMonot fr]
  )
  where
  un = unity a 
  removeHeadVar (Pol mons a _ vs dm) =
                     Pol
                       [(c,Vec $ tail ns) | (c,Vec ns) <- mons]
                       a
                       (lexPPO ((genericLength vs)-1)) (tail vs) dm
  prependHeadVar v (Pol mons a _ vs dm) =
                        Pol
                          [(c,Vec (0:ns)) | (c,Vec ns) <- mons]
                          a
                          (lexPPO ((genericLength vs)+1)) (v:vs) dm

  factorMonot f =                   -- here  1 <= n(1) <= .. <= n(t)
    (case                           -- f  is in  lexComp
         vars 
     of
      [_]   -> [(fromU p, k) | (p,k) <- factorUPol_finField $ toUPol f]
      [x,y] -> viaUPolUPol x y $ unzip $ upolMons $ headVarPol Map.empty f
      _     -> toCaseOfSquareFree f
    )
    where
    (o,vars) = (pPPO f, pVars f)
    fromU p = Pol ms c o vs d  where  Pol ms c _ vs d = fromUPol p
                            -- convert from R[x,y] to  (R[y])[x] 
                            -- (UPol.UPol),  factor and convert back
    viaUPolUPol x y (cs,es) =
                 [(fromUU p,k) |
                  (p,k) <- factorOverFinField_2 $ UPol mons' aY x dY
                 ]
      where
      mons'    = zip (map toUPol cs) es
      aY       = cToUPol y dF a
      (aY',dY) = (fromUPol aY, upEucRing aY Map.empty)
      fromUU f =                                -- R[y][x] -> R[x,y]
                 let  (cs,es) = unzip $ upolMons f
                      mons'   = zip (map fromUPol cs) es
                 in   fromHeadVarPol $ UPol mons' aY' x Map.empty
                                         -- reordPol o  not needed ?
    ----------------------------------------------------------------
    -- Reduce to case of square free  f. 
    -- Here  1 <= n(1) <= .. <= n(t),   f  is in  lexComp.

     Replace it with generic  polSquareFree_finField  ****

    toCaseOfSquareFree f = 
         case  span (> 0) $ qMults $ map (vecRepr . snd) $ polMons f
         of
           (mls,  []   ) ->         -- all components in all 
                           let      -- exponents are multiples of  q
                             m0 = minimum mls       -- f = f1^(q^m0)
                           in
           (poss, 0:mls) ->
    ----------------------------------------------------------------
    toCaseOfPrimitive f =        -- Reduce to case of primitive f.   
                                 -- Here  f <- a[x_1...x_t],  t > 2,
      let                        --          1 <= n(1) <= .. <= n(t)
                   -- it recurses to factoring in variables  x2...xt
        f'  = removeHeadVar f
        dm' = upGCDRing f' Map.empty      
        c'  = pCont $ headVarPol dm' f
        v   = head $ pVars f
        c   = prependHeadVar v c'
      in
      if  pIsConst c  then  toCaseOfSquareFree f 
      else
        [(prependHeadVar v p, i) | (p,i) <- factorOverFinField c']
        ++ (factorOverFinField (f/c))
              -- It 
              -- might be  toCaseOfSquareFree (f/c).  But we have 
              -- again to reduce to case that  1 <= n(1) <=..<= n(t)
    ----------------------------------------------------------------
    factorSquareFree f = 
      let                                               -- Step init
                                           -- before `in',  2 <= n_1 
        n1:n2:ns3 = polDegs [] f
        k j       = 
            product [2*n1*ni - 1 | ni <- genericTake (j-2) (n2:ns3)]
                                            -- ni = n(2)...n(j-1),
                                            -- only for  j <- [3..t]
        vars        = pVars f
        v1:v2:vars3 = vars 
        x1:x2:xs3   = varPs un f
        t           = genericLength vars
        f'          = 
            polSubst 'l' f (x1:x2:[power x2 (k j) | j <- [3..t]]) []
                                                      -- of F[x1,x2]
        unX2 = cToUPol v2 dF un                   -- modelling F[x2]
        dX2  = upEucFactrRing unX2 Map.empty            --
        swapX1X2 (Pol mons a o (u:v:vs) dR) = 
                      reordPol o (Pol (map sw mons) a o (v:u:vs) dR)
                            where
                            sw (a, Vec (i:j:js)) = (a, Vec (j:i:js))
        toSparseMVec f = [(js,a) | (a,Vec js) <- 
                            polMons $ toOverHeadVar dX2 $ swapX1X2 f
                         ]
             -- (f <- F[x1..xt]) <--> vector over F[x2], 
             -- components indexed by power products in [x1,x3...xt]
             --
        fromSparseMVec v = 
          swapX1X2 $ fromOverHeadVar
            (Pol [(c, Vec js) | (js,c) <- v] unX2 o' (v1:vars3) dX2)
                                                   where
                                                   o' = lexPPO (t-1)
        cont_by_x2 f = 
         let
             f' = swapX1X2 f
             f2 = removeHeadVar f'
             dm = upGCDRing f2 Map.empty
         in  swapX1X2 $ prependHeadVar v2 $ pCont $ headVarPol dm f'
      in
      case  (n2 < 2, factorOverFinField f')             
      of
        (True, _  ) -> [f]
        (_   , [_]) -> [f]                                -- Step 
        (_   , ps ) ->                                    -- Factor2
          let 
            h' = fromJust $ find ((> 0) . degInVar 0 1) $ map fst ps
                            -- 
                            -- = head ps  ?

            l1 = degInVar 0 1 h'
            --------------------------------------------------------          
            -- Step h0. Find the unique irreducible factor h0  of  f
            -- such that  h' divides h0.  For  m <- [l1 .. n1-1] ...

            to_h0 m = 
              if
                 m == n1  then  f
              else
                let
                  iss = tail $ iss' ns3 
                    -- [is= [i(3)...i(t)]| i(j) <- [0..n(j)], is/=0]
                    where
                    iss' []       = [[]]
                    iss' (nj:njs) =
                               [i:is | i <- [0..nj], is <- iss' njs]
                  dxs = 
                   zipWith (\ j xj-> xj-(power x2 (k j))) [3..t] xs3

                                                        -- Step h0-l
                  pols = ([h'*(power x1 (i-l1)) | i <- [l1..m]]
                          ++
                          [(power x1 i)*(ppr dxs is) | 
                                              i <- [0..m], is <- iss
                          ]
                         ) 
                     where  
                     ppr dxs is = product1 
                                  ((unity f):(zipWith power dxs is))
                  mVecs      = map toSparseMVec pols
                  givenMInds = map M $ delMultiples $ 
                               sortBy intLexComp $ concat $ 
                                                    mapmap fst mVecs 
                  delMultiples []     = []  
                                    -- uses that the list is ordered
                  delMultiples (x:xs) =
                              x:(delMultiples (dropWhile (== x) xs))
                  mIndTab    = listToFM $ zip [(1::Z)..] givenMInds
                  indTab     = listToFM $ zip givenMInds [(1::Z)..] 
                  toMInd k   = fromJust $ lookupFM mIndTab k
                  fromMInd k = fromJust $ lookupFM indTab k 
                  toIVec v   = 
                       reverse [(fromMInd (M mi), a) | (mi,a) <- v]
                  bs         = map toIVec mVecs
                  sparseVecToPol v = 
                     fromSparseMVec $
                       reverse [(fromM $ toMInd j, a) | (j,a) <- v]
                in
                case  fst $ reduceLattice_UPolField (n2-1) bs
                of
                  []  -> to_h0 (m+1)
                  [v] -> let  h0' = sparseVecToPol v
                         in   h0'/(cont_by_x2 h0')
            --------------------------------------------------------
            h0 = to_h0 l1
          in
          h0:(map fst $ factorOverFinField (f/h0))   -- ?
********************************************************************
-}

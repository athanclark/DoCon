--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------








--------------------------------------------------------------------
{-          Operations with Symmetric Functions  

            (symmetric polynomial-like functions)


                       Preface
                       -------

DoCon implements the symmetric function transformations  M(u,v)  
described in the book 
[Ma]  I.G.Macdonald  "Symmetric Functions and Hall Polynomials",
SEE first [Ma] and Manual. 

METHOD.
There are used the three basic operations:

  K             matrix of Kostka numbers,
  C             matrix of irreducible Character values for the 
                  permutation group S(w),
  M(m,p) = NS   algorithm which we call here the Newton-Serret
                  formula.

Below we denote and abbreviate:

  t(X)       = transpose(X),
  iK         = inv(K),  
  X --> J*X  conjugation of a matrix, that is permutation of its 
               list of rows corresponding to the conjugation of
               partition indices,
  X --> X*J  same operation applied to the columns.

The generic transformation scheme is:

             - - < - K - - - - 
          /                    \
        /                       \
      {m}  ----->  {p}  ----->   {s}   ------>  {e}
        \   NS           t(C)   /  \  J*t(iK)         
          \                    /    \  
            - - - - iK - > - -       \ 
                                      \ t(K)
                                        - -<- - {h}    
That is
  M(p,s) = t(C)         ( permGroupCharColumn )
  M(h,s) = t(K)         ( kostkaColumn        )
  M(e,s) = t(K)*J     
  M(m,s) = iK     
  M(s,h) = t(iK)     
  M(s,e) = J*t(iK)     
  M(s,m) = K                              
  M(s,p) = inv(t(C))    - "easy" inversion of orthogonal matrix.
  M(m,p) = NS formula 

Each symmetric function transformation has the format

                transTab -> f -> (newTab, h)

transTab  contains the pairs  (w, (pts,tC,tK)),
   
   w    the integer weight,
   pts      all partitions of  w  listed decreasingly by pLexComp,
   tC       transposed irreducible character ptp-matrix S(n),
   tK       transposed Kostka ptp-matrix  - see  SymFTransTab.

   - these matrices are for the weight  w.
   And they are the  ptp-matrices,
   that is the tables of type     FiniteMap Partition [Z],
   the row being looked up by the partition index.

The inversion of  tC  is almost the same as the transposition  - for
its rows are mutually orthogonal.
inv(tK)  inverses the lower-uni-triangular matrix, that typically 
contains hundreds of rows.  Though the nature of  K  is so that  the 
numbers grow very little with the grow of  w.

--------------------------------------------------------------------
The generic transformation format is
                             to_<v>      mode tab     f --> (tab, h)
or
                             to_<v>_pol  mode tab ppo f --> (tab, h)     

  <v> <-  ['e','h','m','p','s'].

  mode   is a string  u:t  of one or two letters,

    u <-  ['e','h','m','p','s']   is the name of basis,  

    t  is either  []  or "n",  it is a proper mode.

    So far,  "n"  may be used ONLY in the case of  to_e(_pol) "mn"

(T2) differ from (T1)  in that they convert the result to Polynomial
- in the given  pp-ordering  ppo.

t = []  is effective when  
                K,C  are not too large 
                and  there are many repeating monomial weights in f.


Variable list
-------------
The result polynomial of  to_<v>_pol  is in the variables

   [ <v>1, <v>2, ... , <v>n ],   n = max( symPolWeight(f), 1 )

- rename if necessary.

Coefficient ring
----------------
              to_p   requires a field of zero characteristic,

              all the others need any Commutative ring R with unity.


Generic computation method:   to_<v> mode tab f
---------------------------

is done, according to the above diagram, either by  
                                          <u>_to_<v> 
for some  u, or by a composition of       <u>_to_<s> and <s>_to_<v>.

Each  <u>_to_<v>  splits  f into homogeneous parts:
                             f = sum( f(w)|  w <-[0..totalDeg(f)] ),
decomposes each f(w) to h(w) and sums up h(w).
Each     
                   f(w) = sum( c(la)*u(la)| ...) 
converts according to the appropriate row (column)  of  one  of  the
matrices from table corresponding to  w.  Here the dense integer row
converts to sym-polynomial over R - see  intListToSymPol.
The matrices are completed, if necessary, and restored.
-}
--------------------------------------------------------------------






module AlgSymmF 

  -- This is the head, wrapping module. The true implementation is
  -- in
  -- Partit_.hs, HookBand_.hs, Partition.hs, Sympol_.hs, SymmFn*.hs
  --
  -- See first  Partition.hs, Sympol_.hs


  (toSymPol, symmSumPol, symmetrizePol, fromSymPol,
   to_e, to_e_pol,  to_h, to_h_pol,  to_m, to_m_pol, 
   to_p, to_p_pol,  to_s, to_s_pol,   
   symmSumPol_direct_test,
 
   -- from Sympol_
   SymPol(..), SymMon, symPolMons, symPolPrttComp, symLm, symLdPrtt,
   cToSymPol, reordSymPol, monToSymMon, symPolHomogForms, 
   -- , instances for SymPol:
   -- Show, Eq, Dom, Cast, PolLike, Set .. AddGroup, Num,
  
   -- from SymmFn_
   PrttParamMatrix, SymFTransTab, ptpMatrRows, transpPtP, 
   h'to_p_coef, elemSymPols, hPowerSums, toDensePP_in_symPol, 
   fromDensePP_in_pol, intListToSymPol
  )

where
import List       (partition, genericLength, genericTake,
                   genericDrop, genericReplicate
                  )
import DPrelude   (eFM, ct, ctr, factorial, sum1, product1,
                   showsWithDom, sortBy, compBy
                  )
import Categs     (Dom(..), Domains1                )
import SetGroup   (zeroS, times                     )
import RingModule (CommutativeRing(), Field(), fromi)
import VecMatr    (Vector(..)                       )
import Permut     (permutRepr, allPermuts           )

import Pol        (PolLike(..), Pol(..), PPOrdTerm, polMons, lexPPO,
                   reordPol, deg0, polSubst
                  )
import Partition  (PrttComp, pLexComp, prttLength) 
import Sympol_    
       (SymPol(..), SymMon, symPolMons, symLm, symPolPrttComp,
        monToSymMon,symLdPrtt,reordSymPol,symPolHomogForms,cToSymPol
       )
import SymmFn_    
       (SymFTransTab, PrttParamMatrix, transpPtP, ptpMatrRows, 
        h'to_p_coef, elemSymPols, hPowerSums, toDensePP_in_symPol, 
        fromDensePP_in_pol, intListToSymPol, pToS_, hToS_, mToS_, 
        eToS_
       )  
import SymmFn0_   (sToE_, sToM_, sToP_, mToP_, sToH_)
import SymmFn1_   (mToEViaP_pol_                    )








--------------------------------------------------------------------
toSymPol :: (Eq a) => PrttComp -> Pol a -> Maybe (SymPol a)
                      -- pcp      f               symF

  -- Given a polynomial f, symmetric under the permutations of its
  --   variables  vars,  
  -- partition comparison  pcp, 
  -- produce the sym-polynomial  symF  by collecting each monomial 
  -- orbit into corresponding sym-monomial.
  -- Yields  Just symF  for the symmetric f,
  --         Nothing    for non-symmetric f.
  -- Method.
  -- The monomials convert to list of sym-monomials. In this list
  -- each (a,p) should repeat  mt(p,n) times,
  --              mt(p,n) =  n! / product(k!| k<-multiplicities(p)],
  -- n = |vars|,  k  the multiplicity of the item in partition. 
  -- All such repetitions are replaced with one.

            
toSymPol pcp (Pol mons c _ vars dA) =  toSP [] sms 
  where
  sms = map monToSymMon mons 

  toSP smons []             =  
                      Just $ reordSymPol pcp $ SymPol smons c pcp dA
  toSP smons ((a,p):smons') = 
    let 
      l                = prttLength p 
      monMultiplicity  =  
                    foldl (/) nft $ map (factorial .snd) ((0,n-l):p)

      (copies,smons'') = partition ((==p).snd) smons'
    in
    if  ((genericLength copies)+1)==monMultiplicity
        &&
        all ((==a).fst) copies  then  toSP ((a,p):smons) smons''
    else                              Nothing

  (n,nft) = (genericLength vars, factorial n)

--------------------------------------------------------------------
symmetrizePol :: 
        (CommutativeRing a) => PrttComp -> Pol a -> Maybe (SymPol a)

  -- Convert polynomial  f  to symmetric form polynomial under the 
  -- given partition ordering pcp.
  -- It sums up the symmetric orbit and divides by  n!, 
  --                                                n = length vars.
  -- REQUIRED:  n! /= 0  in `a'.
  -- Also if the above quotient by n!  does not exist, the result is 
  --                                                        Nothing.
  -- Examples:
  -- for a field `a' with  char > n  the result is of kind  Just sf;
  -- for  a = Z/4,  n = 3,  symmetric  f,      it is      Just sf;
  --                        non symmetric  f,  it may be  Nothing.

symmetrizePol pcp f = pCDiv (symmSumPol pcp f) nFactorial
  where
  nFactorial = fromi (sample f)$ factorial $ genericLength $ pVars f


--------------------------------------------------------------------
symmSumPol :: (CommutativeRing a)=> PrttComp -> Pol a -> SymPol a
                                    -- pcp      f        symF

  -- symF = n!*(symmetrizePol f),  n = length vars,
  --                    symF under the given partition ordering pcp.
  -- Method.
  -- Convert power products pp to partitions [i,j..].
  -- Gather pp-s of same orbit, that is of same partition.
  -- Each  orbit(i,j..)  sum  is       c(i,j..)*m[i,j..],  
  -- with the appropriate coefficient  c(i,j..) = stabilizator order
  -- of pp  (i,j..)  in the group  S(n).

symmSumPol pcp (Pol mons c _ vars dA) = 
                                      toSP [] $ map monToSymMon mons
  where
  (z,n) = (zeroS c, genericLength vars) 

  toSP smons []             = reordSymPol pcp$ SymPol smons z pcp dA
  toSP smons ((a,p):smons') =
                   let
                     (copies,smons'') = partition ((==p).snd) smons'
                     a'               = sum1 (a:(map fst copies))
                     a''              = times a' $ stabilizOrder p
                   in
                   if  a''==z  then  toSP smons smons''
                   else              toSP ((a'',p):smons) smons''

  stabilizOrder partit = let  mps = map snd partit
                              n0  = n - (sum mps)
                         in   product1 $ map factorial (n0:mps)


--------------------------------------------------------------------
fromSymPol :: (CommutativeRing a) => 
                      Pol a -> Domains1 (Pol a) -> SymPol a -> Pol a
                      -- smp   dP                  f

  -- Expand sym-polynomial to polynomial of the given sample  smp.
  -- Method:
  -- f converts to  h(e1,e2..),   ei the elementary symmetrics; then
  -- the expressions  ei(vars)  are substituted in  h.
  -- Here it is set  ei = 0  for  i > n = |vars|.
  --
  -- CAUTION:  this may be very expensive, think before applying it.


fromSymPol smp dP f = 
  let 
    (o,vars) = (pPPO smp, pVars smp)
    n        = genericLength vars 
    olex     = lexPPO n
    polL     = reordPol olex smp
    elems    = elemSymPols smp dP
    (_,h)    = to_e_pol "mn" eFM olex f
    dn       = n - (genericLength (pVars h))  
    zeroes   = if  dn < 0  then  []  else  genericReplicate dn 0

    restrMon (c,Vec js) = (c, Vec (genericTake n js))
                                             -- restrict monomial to
                                             -- first n variables

    restrict f = ctr polL $ sumsim $ map restrMon $ 
                                         filter isInVars $ polMons f
       -- Restrict polynomial.
       -- It sums similar mon-s appearing after restricting of pp-s.
       where
       isInVars (_, Vec js) = all (==0) (genericDrop n js)
                  --
                  -- "monomial does not depend on variables after n"

       sumsim []           = []       
       sumsim ((a,p):mons) =  
                      let  (sims,mons') = partition ((==p).snd) mons
                           b            = sum1 (a:(map fst sims))
                      in   (b, complete p):(sumsim mons')

       complete (Vec js) = if  dn <= 0  then  Vec js
                           else               Vec (js++zeroes)
  in
  reordPol o (polSubst 'l' (restrict h) elems [])

--------------------------------------------------------------------
symmSumPol_direct_test :: (CommutativeRing a) => Pol a -> Pol a

  -- Only for testing. 
  -- Symmetrizes polynomial without converting it to SymPol form.
  -- Maybe expensive.

symmSumPol_direct_test f = case  (polMons f, pVars f)  of

  ([]  , _   ) -> zeroS f
  (mons, vars) -> sum1 $ map sysumMon $ mons
    where
    sysumMon (a,Vec js) =
                 sum1 [ct f (a, Vec$ applyPermut pm js)| pm<- pmts]
    ordList = map fst $ zip [1 ..] vars
    pmts    = map permutRepr $ allPermuts ordList

    applyPermut ks js = map snd $ sortBy (compBy fst) $ zip ks js


--------------------------------------------------------------------
to_e, to_h, to_m, to_s ::  
  
      (CommutativeRing a)
      => 
      String -> SymFTransTab -> SymPol a -> (SymFTransTab, SymPol a)


to_p :: (Field k)   -- REQUIRED is  char(k) = 0
        =>  
        String-> SymFTransTab-> SymPol k-> (SymFTransTab, SymPol k)



composeViaTab map1 map2 tab f = map2 tab' g                  --LOCAL
                                        where  (tab',g) = map1 tab f

to_e mode tab f = case  mode  of 

  'h':_ -> composeViaTab hToS_ sToE_ tab f
  'p':_ -> composeViaTab pToS_ sToE_ tab f
  's':_ -> sToE_ tab f
  "m"   -> composeViaTab mToS_ sToE_ tab f
  "mn"  -> (tab,  
            fromDensePP_in_pol pLexComp $ mToEViaP_pol_ f
           )                                  --avoids Kostka matrix

  _     -> error $ ("to_e "++) $ (mode++) $ (" table f,"++) $ 
                  showsWithDom f "f" "" 
                  "\nmode  may be \"h\",\"p\",\"s\",\"m\",\"mn\" \n"


to_h mode tab f = case  mode  of

  "e" -> to_e "h" tab f                  -- e <-involution omega-> h
  "m" -> composeViaTab mToS_ sToH_ tab f
  "p" -> composeViaTab pToS_ sToH_ tab f
  "s" -> sToH_ tab f
  _   -> error $ ("to_h "++) $ (mode++) $ (" table f,"++) $ 
                showsWithDom f "f" "" 
                "\n mode  may be  \"e\",\"m\",\"p\",\"s\"  \n"

to_m mode tab f = case  mode  of

  "e" -> composeViaTab eToS_ sToM_ tab f
  "h" -> composeViaTab hToS_ sToM_ tab f
  "p" -> composeViaTab pToS_ sToM_ tab f
  "s" -> sToM_ tab f
  _   -> error $ ("to_m "++) $ (mode++) $ (" table f,"++) $ 
                showsWithDom f "f" ""
                "\n mode  may be  \"e\",\"h\",\"p\",\"s\"  \n"

to_s mode tab f = case  mode  of

  "e" -> eToS_ tab f
  "h" -> hToS_ tab f 
  "m" -> mToS_ tab f  
  "p" -> pToS_ tab f
  _   -> error $ ("to_s "++) $ (mode++) $ (" table f,"++) $ 
                showsWithDom f "f" ""
                "\n mode  may be  \"e\",\"h\",\"m\",\"p\"  \n"

to_p mode tab f = case  mode  of

  "e" -> composeViaTab eToS_ sToP_ tab f
  "h" -> composeViaTab hToS_ sToP_ tab f
  "m" -> (tab, mToP_ f)
  "s" -> sToP_ tab f
  _   -> error $ ("to_p "++) $ (mode++) $ (" table f,"++) $ 
                showsWithDom f "f" ""
                "\n mode  may be  \"e\",\"h\",\"m\",\"s\"  \n"



--------------------------------------------------------------------
to_e_pol, to_h_pol, to_m_pol, to_s_pol ::  

  (CommutativeRing a)
  => 
  String -> SymFTransTab -> PPOrdTerm -> SymPol a -> 
                                             (SymFTransTab, Pol a)


to_p_pol :: (Field k)   -- REQUIRED is  char(k) = 0
            =>  
            String -> SymFTransTab -> PPOrdTerm -> SymPol k ->  
                                             (SymFTransTab, Pol k)


  -- These  to_<v>_pol  functions differ from  to_<v>  
  --
  -- in that they return Polynomial - in the given  
  --   pp ordering  o,  
  --   variables    [ <v>1, <v>2, ... , <v>n ],  n = max (1, deg f).
  -- EXAMPLE:
  -- for  f = m[2] + m[1,1],   o = (("",3),degLex,[])
  --
  -- to_e     "m" tab   f  --> SymPol (e[3]-2*e[2]+e[1^2]) ...
  -- to_e_pol "m" tab o f  --> Pol    ("e1"^2 - 2*"e2" + "e3") ...
  --
  -- Method.
  -- to_<v>_pol  consists mostly of  to_<v>.
  -- Only in the end it is applied   toDensePP_in_symPol o vars
  -- which converts each partition  la  from  symPol 
  -- into the power product of the length  n  by  prttToPP. 
  -- Then the polynomial is reordered to  o.


to_e_pol mode tab o f =  
  if  
     mode=="mn"  then  (tab, reordPol o $ mToEViaP_pol_ f)
                                        -- "mn" avoids Kostka matrix
  else  topol 'e' to_e mode tab o f


topol ch toX mode tab o f =              -- LOCAL
  let
    (tab',g) = toX mode tab f 
    n        = max 1 (deg0 '_' 0 g)  
    vars     = map ((ch:).show) [1..n]   -- say, 21 -> "e21"
  in
  (tab', toDensePP_in_symPol o vars g)


to_h_pol = topol 'h' to_h 
to_m_pol = topol 'm' to_m 
to_p_pol = topol 'p' to_p 
to_s_pol = topol 's' to_s 

 ;










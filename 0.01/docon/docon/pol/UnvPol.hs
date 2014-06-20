------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- Univariate Polynomial  





module  UnvPol   where

import  PreludeInteger
import  Categ
import  Categ1
import  Generic
import  PP
import  Pol
import  Matrix
import  IParse



type  Mon1 a =  (a,Integer)
data  Pol1 a =  Pol1 [Mon1 a]   deriving (Eq,Text)



lc1  (Pol1 ms) =  fst (head ms)
deg  (Pol1 ms) =  snd (head ms)



pol1ToPol :: PPComp -> Pol1 a -> Pol a
           
                -- Imbed  f :: (Pol1 a)  to  Pol a.

                -- Example:  pol1ToPol  lex (Pol1 [(4,2),(4,0)])
                --           ->                   
                --           Pol [(4, PP [2] lex), (4, PP [] lex)]

pol1ToPol  cp (Pol1 mons) =  Pol (pol mons)
  where 
  pol  []         =  [] 
  pol  [(a,0)]    =  [ (a, PP [] cp) ]
  pol  ((a,n):ms) =  (a, PP [n] cp) : (pol ms)




polToPol1 :: CommutativeRing a =>  Pol a -> Pol1 a

          -- Project  f:: Pol a  to  Pol1 a  substituting  unity
          -- instead of all variables except the first.

          -- This is and imbedding inverse to  pol1ToPol  
          -- -  when restricted to the subring of polylomials de-
          -- pending only on the first variable.

          -- Example:   2*x^2*y^3 + y + 1   ->   2*x^2 + 2 

polToPol1  (Pol mons) =  p1 mons
  where 
  p1  []         = Pol1 [] 
  p1  ((a,p):ms) = case  ppP p  of
                           []    -> Pol1 [(a,0)]
                           (n:ns)-> pol1Add (Pol1 [(a,n)]) (p1 ms)


pol1Neg :: AddSemigroup a =>  Pol1 a -> Pol1 a

pol1Neg  (Pol1 mons) =  Pol1  (map (\(a,n)->(neg a,n)) mons)



pol1Add, pol1Sub, pol1Mul :: 
                  CommutativeRing c =>  Pol1 c -> Pol1 c -> Pol1 c

pol1Add  (Pol1 [])        g        =  g
pol1Add  (Pol1 ((a,n):f)) (Pol1 g) = 
                                   Pol1  (pa (zero a) ((a,n):f) g)
  where
  pa  _  []        g         =  g
  pa  _  f         []        =  f
  pa  zr ((a,n):f) ((b,m):g) =  case  compare n m  of  
      
    GT ->  (a,n) : (pa zr f         ((b,m):g))
    LT ->  (b,m) : (pa zr ((a,n):f) g        )
    _  ->  let  c = add a b  in  if c==zr then  pa zr f g  
                                 else           (c,n):(pa zr f g)



pol1Sub f g =  pol1Add f (pol1Neg g)


mon1Mul :: Ring a =>  a -> Mon1 a -> Mon1 a -> [Mon1 a]
mon1Mul  zero (a,n) (b,m) =                              
                  let  c = mul a b  
                  in         if  c==zero  then []  else  [(c,n+m)]


mPol1Mul :: Ring a =>  Mon1 a -> Pol1 a -> Pol1 a

mPol1Mul  (a,n) (Pol1 ms) =  Pol1 (mpm (zero a) ms)
  where
  mpm _ []       =  []
  mpm z (mon:ms) =  (mon1Mul z (a,n) mon)++(mpm z ms)


pol1Mul (Pol1 [])  _          = Pol1 []
pol1Mul (Pol1 fms) (Pol1 gms) = pm (zero (lc1 (Pol1 fms))) fms gms
  where
  pm  _ []     _      =  Pol1 []   
  pm  _ _      []     =  Pol1 []   
  pm  z (m:ms) (n:ns) =  
    let
      (Pol1 ms1) = pol1Add (mPol1Mul m (Pol1 ns)) (pm z ms (n:ns))
    in
      Pol1  ((mon1Mul z m n)++ms1)
------------------------------------------------------------------

vectorToPol1 :: AddMonoid a =>  [a] -> Pol1 a

              -- actually this converts dense vector to sparse one

vectorToPol1  (x:xs) =  Pol1 (sparse (zero x) (x:xs))
  where
  sparse  zr xs =  s  xs ((genericLength xs)-1)  
                                               --set current deg,
    where                                      --make polynomial 
    s []     _ =  []
    s (x:xs) d =  if  x==zr  then  s xs (d-1)       --skip zero x
                  else             (x,d):(s xs (d-1))
------------------------------------------------------------------

pol1ToVector :: Set a =>    a -> Integer -> Pol1 a -> [a]
                         --zero  lng

                   -- Inverse:  make Vector.  Also prepend zeroes 
                   -- up to the given length lng - if  lng /= 0. 

pol1ToVector  zr lng (Pol1 mons) = 
  let
         -- Coefficients from f are extracted and set into vector.
         -- k  is the current degree.  If (lpp f) < k  then  (k-e)
         -- zeroes are inserted, where  e = lpp (tail f).
         --
    vec k []         =  (copy k zr)++[zr] 
    vec k [(a,0)]    =  (copy k zr)++[a] 
    vec k ((a,e):ms) =  
           if  e==k  then  a : (vec (k-1) ms) 
           else            (copy (k-e) zr)++(a:(vec (e-1) ms))
                                   -- absent 
                                   -- power makes zeroes in vector 
  in
    let  l = (deg (Pol1 mons))+1
    in
      if  (lng<l) && (lng/=0)  then  
                    error ( ((w "(pol1ToVector  " ).(w zr).(' ':).
                             (w lng)                               
                            )
                            " _)   0 /= lng < deg(pol)+1" 
                          )
      else  
        if  lng==0  then  vec (l-1) mons 
        else              (copy (lng-l) zr)++(vec (l-1) mons)
------------------------------------------------------------------

cPol1Mul ::  Ring c =>  c -> Pol1 c -> Pol1 c

cPol1Mul c (Pol1 mons) =  Pol1 (cpm (zero c) mons)
  where
  cpm _ []         = []
  cpm z ((a,p):ms) = let  b= mul c a  in  if b==z then  cpm z ms
                                          else    (b,p):(cpm z ms)
------------------------------------------------------------------

pol1CoefDiv :: Ring c =>  Pol1 c -> c -> [Pol1 c]

                    -- returns  []  if  f  is not a multiple of  c
pol1CoefDiv  (Pol1 mons) c  =      
  let
    cQuotsPar =  map (\a-> divide_l a c) (map fst mons)
  in
    if  any null cQuotsPar  then  []  
    else     
      [ Pol1  (zip (map head cQuotsPar) (map snd mons)) ]
------------------------------------------------------------------


pol1Times:: Ring c => Pol1 c -> Integer -> Pol1 c

pol1Times (Pol1 [])         _ = Pol1 []
pol1Times (Pol1 ((a,p):ms)) n = Pol1 (tm (zero a) ((a,p):ms))
  where
  tm _ []         = []
  tm z ((a,p):ms) = let  b = times a n  in  if b==z then  tm z ms
                                            else   (b,p):(tm z ms)
------------------------------------------------------------------

pol1DivRem :: 
        CommutativeRing c =>  Pol1 c -> Pol1 c -> (Pol1 c, Pol1 c)

                                                -- See  polDivRem
pol1DivRem _          (Pol1 [])           = 
                             error "(pol1DivRem _ (Pol1 [])) \n\n"
pol1DivRem (Pol1 fms) (Pol1 ((b,pp):gms)) = d fms (Pol1 []) 
  where
  d []            q = (q, Pol1 [])   
  d ((a,pp1):fms) q = let  dpp = pp1-pp  in 

    if  dpp < 0  then  (q, Pol1 ((a,pp1):fms))   
    else
      case  divide_l a b  
      of
        []  -> (q, Pol1 ((a,pp1):fms)) 
        [c] -> 
          let  (Pol1 ms) = 
                  pol1Sub (Pol1 fms) (mPol1Mul (c,dpp) (Pol1 gms))
          in
               d  ms (pol1Add (Pol1 [(c,dpp)]) q)










{-
******  Unnecessary ?  *******



---------------------------  Set  --------------------------------



instance  Ring a =>  Set (Pol1 a)   where

  card _ =  []

  w =  shows

  -- r

  setTerm ((c,_):_) = 
     (setDomFuncs  (funcNames "set")  
          (setDomCons  (UnivPol (ringTerm c))  trivialDomain
     ))




------------------------  AddGroup  ------------------------------


instance  CommutativeRing a =>  AddSemigroup (Pol1 a)   where

  addSmgTerm ((c,p):_) =   let  f =  [(c,p)]  in

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+",cyclicAdd f),("gr+",groupAdd f),
           ("ord+",ordAdd f)
         ]
         (setDomCons (UnivPol (ringTerm c)) trivialDomain)
    ) )

  cyclicAdd _ =  No
  groupAdd  _ =  Yes
  ordAdd    _ =  No

  add         =  pol1Add
  zero _      =  []
  zero_l  _   =  [[]]
  neg         =  pol1Neg
  neg_l   f   =  [pol1Neg f]
  sub_l   f g =  [pol1Sub f g]
  times_l f n =  [pol1Times f n]

instance  CommutativeRing a  =>  AddMonoid (Pol1 a)
instance  CommutativeRing a  =>  AddGroup  (Pol1 a)





----------------------  MulSemigroup  ----------------------------


instance  CommutativeRing c =>  MulSemigroup (Pol1 c)
  where

  mulSmgTerm ((c,p):_) =   let  f =  [(c,p)]  in

    (setDomFuncs  (funcNames "mulSmg")  
      (setDomProps
         [ ("comm", commutative c),  ("cyc*", Unknown),
           ("gr*", No)
         ]
         (setDomCons (UnivPol (ringTerm c)) trivialDomain)
    ) )

  commutative ((c,_):_) =  commutative c
  groupMul    _         =  No
  cyclicMul   _         =  Unknown

  mul =  pol1Mul

  unity_l  ((c,_):_) =  case  unity_l c  of  []   -> []
                                             [un] -> [ [(un,0)] ]

  inv_l  [(c,n)] =  if  n/=0  then  []
                    else      case  inv_l c  of  [] -> []
                                                 [a]-> [ [(a,0)] ]


  divide_l f g =  case  pol1DivRem f g  of  (q,[]) -> [q]
                                            _      -> []

  -- power  is defined automatically




instance  (CommutativeRing c, MulMonoid c) =>  MulMonoid (Pol1 c)





--------------------------  Ring  --------------------------------


instance  (CommutativeRing c) =>  Ring (Pol1 c)
  where

  ringTerm ((c,p):_) =   let  f = [(c,p)]  in

    (setDomFuncs      (funcNames "ring")
      (setDomProps    (polRing_props (ringTerm c) ["1"])
         (setDomCons  (UnivPol (ringTerm c))  trivialDomain)
    ) )
    where
    polRing_props cTerm vars =
                    polPrs  (domProps cTerm) (domCons cTerm) vars
      where
      polPrs  cProps cCons vars =  []
                              --  (polRingAxioms vars) ...




  hasZeroDiv ((c,_):_) =  hasZeroDiv c         -- TO BE PROVED
  hasNilp    ((c,_):_) =  hasNilp c            -- ?

  field            _         =  No
  euclidean        ((c,_):_) =  field c    
  princIdeals                =  euclidean 
  syzygySolvable   ((c,_):_) =  syzygySolvable c
  factorial        ((c,_):_) =  factorial c
  factorizeIsTotal _         =  No
                                  --SO FAR

--  factorizeIsTotal ((c,_):_) =  
--                     case  (field c, card c)  of  (Yes,[n]) -> Yes
--                                                  _         -> No

  hasGrBas        ((c,_):_) =  euclidean c
  moduloIsCanonic ((c,_):_) =  euclidean c
  minNormRemValid _         =  Yes


  i_l  ((c,_):_) n  =  case  (i_l c n, zero c)  of
                                           ([] , _) -> []
                                           ([a], z) -> [ [(a,0)] ]
  char ((c,_):_) =  char c 



instance CommutativeRing c =>  CommutativeRing (Pol1 c)

instance  Text c =>  Text (Pol1 c)   

instance  CommutativeRing (Pol1 c) =>  Num (Pol1 c)  where
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul
  (/) f  = fst.(pol1DivRem f)      



----------------------  Module over  c  --------------------------
        

--instance  Ring c =>  ModuleOver (Pol1 c) c    where  
-- moduleTerm _ =  
--  cMul = cPol1Mul 




-------------------  SyzygySolvableRing  -------------------------



instance  (SyzygySolvableRing c, Num c) => 
                                       SyzygySolvableRing (Pol1 c)
  where


            -- canInv, gcD, lcM  are total if  (factorial c)==Yes
 
  -- lcM  is the default one

  canInv []        =  error "canInv []"  
  canInv ((c,_):f) =  [(canInv c, 0)]

  canAssoc []        =  []
  canAssoc ((c,p):f) =  cPol1Mul (inv (canInv c)) ((c,p):f)

  divRem _ f g  =  let  (q,r) = pol1DivRem f g  in  [q,r]

  factorize _  =  error "no polynomial factorization yet"

  gcD =  gcdL pol1GCD






------------------------------------------------------------------
------------------------------------------------------------------
--              Univariate Polynomials with Variable            --
------------------------------------------------------------------
------------------------------------------------------------------


instance  Eq (Pol1 c) =>  Eq (VarPol1 c)   where

  (VarP1 f _)==(VarP1 g _) =  f==g 

              -- we presume that all operations take polynomials 
              -- supplied with in the Same variable.

------------------------------------------------------------------

instance  Set (Pol1 c) =>  Set (VarPol1 c)   where

  card _ = []

  w  (VarP1 f v) =  showsPol [v] (pol1ToPol lex f)

  -- r

  setTerm (VarP1 ((c,_):_) v) = 
      (setDomFuncs  (funcNames "set")
         (setDomCons  (UnivPol (ringTerm c)) trivialDomain
      ))

------------------------------------------------------------------


instance  AddSemigroup (Pol1 c) =>   AddSemigroup (VarPol1 c)
  where

  addSmgTerm (VarP1 ((c,p):f) v) =   
         (setDomCons  
            (UnivPol (ringTerm c))  (addSmgTerm ((c,p):f))
         ) 

  cyclicAdd (VarP1 f _) =  cyclicAdd f 
  groupAdd  (VarP1 f _) =  groupAdd  f 
  ordAdd    _           =  No

  add     (VarP1 f v) (VarP1 g _)  =  VarP1 (add f g) v
  zero    (VarP1 f v)              =  VarP1 (zero f)  v
  zero_l  (VarP1 _ v)              =  [ (VarP1 [] v) ]
  neg     (VarP1 f v)              =  VarP1 (neg f) v
  neg_l   (VarP1 f v)              =  varp1Emp v (neg_l f)
  sub_l   (VarP1 f v) (VarP1 g _)  =  varp1Emp v (sub_l f g)
  times_l (VarP1 f v) n            =  varp1Emp v (times_l f n)


instance  AddMonoid (Pol1 c) =>  AddMonoid (VarPol1 c)
instance  AddGroup  (Pol1 c) =>  AddGroup  (VarPol1 c)



------------------------------------------------------------------

instance  MulSemigroup (Pol1 c) =>  MulSemigroup (VarPol1 c)
  where

  mulSmgTerm  (VarP1 ((c,p):f) v) =   
         (setDomCons  
            (UnivPol (ringTerm c))  (mulSmgTerm ((c,p):f))
         ) 

  commutative (VarP1 f _) =  commutative f
  cyclicMul   (VarP1 f _) =  cyclicMul   f 
  groupMul    (VarP1 f _) =  groupMul    f

  mul  (VarP1 f v) (VarP1 g _) =  VarP1 (mul f g) v

  unity_l  (VarP1 f v)             =  varp1Emp v (unity_l f)
  inv_l    (VarP1 f v)             =  varp1Emp v (inv_l   f)
  divide_l (VarP1 f v) (VarP1 g _) =  varp1Emp v (divide_l f g)


instance  MulMonoid (Pol1 c) =>  MulMonoid (VarPol1 c)

------------------------------------------------------------------


instance  Ring (Pol1 c) =>  Ring (VarPol1 c)
  where

  ringTerm  (VarP1 ((c,p):f) v) =   
           (setDomCons  
              (UnivPol (ringTerm c))  (ringTerm ((c,p):f))
           ) 

  hasZeroDiv       (VarP1 f _) =  hasZeroDiv       f
  hasNilp          (VarP1 f _) =  hasNilp          f
  field            (VarP1 f _) =  field            f
  euclidean        (VarP1 f _) =  euclidean        f
  princIdeals      (VarP1 f _) =  princIdeals      f     
  syzygySolvable   (VarP1 f _) =  syzygySolvable   f
  factorial        (VarP1 f _) =  factorial        f
  factorizeIsTotal (VarP1 f _) =  factorizeIsTotal f  
  hasGrBas         (VarP1 f _) =  hasGrBas         f
  moduloIsCanonic  (VarP1 f _) =  moduloIsCanonic  f
  minNormRemValid  (VarP1 f _) =  minNormRemValid  f

  char (VarP1 f _)   =  char f
  i_l  (VarP1 f v) n =  varp1Emp v (i_l f n)

 

instance CommutativeRing (Pol1 c) =>  CommutativeRing (VarPol1 c)

instance  Text (Pol1 c) =>  Text (VarPol1 c)   

instance  Num  (Pol1 c) =>  Num  (VarPol1 c)   
  where
  negate  (VarP1 f v)       =  VarP1 (negate f) v
  (VarP1 f v) + (VarP1 g _) =  VarP1 (f+g) v
  (VarP1 f v) - (VarP1 g _) =  VarP1 (f-g) v
  (VarP1 f v) * (VarP1 g _) =  VarP1 (f*g) v
  (VarP1 f v) / (VarP1 g _) =  VarP1 (f/g) v 

------------------------------------------------------------------

--instance  ModuleOver (Pol1 c) c =>  ModuleOver (VarPol1 c) c
--  where
-- moduleTerm (VarP1 f v) = 
--  cMul c (VarP1 f v) =  VarP1 (cMul c f) v

------------------------------------------------------------------

instance  SyzygySolvableRing (Pol1 c) => 
                                    SyzygySolvableRing (VarPol1 c)
  where

  canInv    (VarP1 f v) =  VarP1 (canInv f) v

  divRem _ (VarP1 f v) (VarP1 g _) =
            let  [q,r] = divRem "" f g  in  [VarP1 q v, VarP1 r v]

  factorize (VarP1 f v) = 
                   map  (\(g,n)-> ((VarP1 g v),n) )  (factorize f)

  gcD  ((VarP1 f v):fs) =  VarP1  (gcD  (f:(map fromVarP1 fs)) ) v
  ----------------------------------------------------------------
  moduloBasis  modes vgs (VarP1 f v) = 
               VarP1  (moduloBasis modes (map fromVarP1 vgs) f)  v

  moduloBasis_q  modes vgs (VarP1 f v) = 
    let
      (r,qs) =  moduloBasis_q modes  (map fromVarP1 vgs)  f
    in
      (VarP1 r v, map (toVarP1 v) qs)
  ----------------------------------------------------------------
  grBasis _    []                =  []
  grBasis mode ((VarP1 f v):vfs) = 
           map (toVarP1 v) (grBasis mode (f:(map fromVarP1 vfs)) )

  grBasis_q _    []                =  ( [], Mt [] )
  grBasis_q mode ((VarP1 f v):vfs) = 
    let
      (gs, Mt rows) =  grBasis_q mode (f: (map fromVarP1 vfs))
    in
      ( map (toVarP1 v) gs,  
        Mt  (map (\row-> map (toVarP1 v) row) rows)
      )
  ----------------------------------------------------------------

-}
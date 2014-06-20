------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




--  Operations on  Polynomials   and  

--  Instances for the  Pol  constructor.





module  Pol  where

import  PreludeList
import  PreludeInteger
import  Categ
import  Categ1
import  Generic
import  PP
import  ExprPol
import  VarPol
import  PolGCD
import  Matrix
import  NF
import  GrBas
import  RelBas
import  IParse





type  Mon c =  (c,PP)                          -- see  "pp.gs"
                   
data  Pol c =  Pol [Mon c]   deriving (Eq,Text)




      ----------------------------------------------------------
      -- Pol c   is the UNION of all the rings  c[x1,...,xn],
      --         n = 1,2,...
      ----------------------------------------------------------

      -- Example:  2*x*z^2 + y^4  is represented as
 
      --     Pol  [ (2, PP [1,0,2] lex), (1, PP [0,4] lex) ]   

      -- - if we choose  lex  comparison for PowPr,  and

      --     Pol  [ (1, PP [0,4] degLex), (2, PP [1,0,2] degLex) ]

      -- - under degLex.
      ------------------------------------------------------------


    -- Pol, VarPol  contain univariate polynomials.
    
    -- ************  Probabaly, UNNECESSARY  ****************
    -- Still  Pol1, VarPol1  constructors are introduced specially
    -- for the univariate polynomials.
    -- ***********************************************************

                          --type Mon1 c = (c,Integer)
                          --type Pol1 c = Pol1 [ Mon1 c ]  
                          --            3*x^2+4 <--> [(3,2),(4,0)]
                          --data VarPol1 c = VarP1 (Pol1 c) String


------------------------------------------------------------------
type  VecPol a =  (Pol a, [Pol a])

    -- Vec-polynoamial  fv = (f,fs)  is supplied with the
    -- polynomial vector  fs.  
    --   fs  is often used to accumulate the coefficients  fi  of
    -- f  relatively to some initial basis  gs: 
    -- f = f1*g1+...+fm*gm.
    --   This serves for  _q  versions of  moduloBasis, 
    -- groebnerBasis  functions.


mVecPolMul  m (f,fs) =  ( mPolMul m f,  map (mPolMul m) fs )

vecPolAdd (f,fs) (g,gs) =  (polAdd f g, binOpList polAdd fs gs)

vecPolSub (f,fs) (g,gs) =  ( polSub f g, 
                             binOpList polAdd fs (map polNeg gs)
                           )
------------------------------------------------------------------


isZeroPol  (Pol mons) =  null mons


lm  (Pol (m:_)) =  m                    
lm  _           =  error "lm (Pol []) \n\n" 

lc  (Pol (m:_)) =  fst m
lc  _           =  error "lc (Pol []) \n\n" 

lpp (Pol (m:_)) =  snd m              -- full PP (with comparison)
lpp _           =  error  "lpp (Pol []) \n\n"

polTail  (Pol (_:ms)) =  Pol ms
polTail  _            =  error "polTail (Pol []) \n\n"

           
totalDeg  f =  sum (ppP (lpp f))


numOfVars (Pol []  ) =  0 :: Integer
numOfVars (Pol mons) =  maximum (map (genericLength.ppP.snd) mons)



cToPol :: AddGroup c =>   c  ->  PPComp  ->  c   ->  Pol c
                        --zero   cp          coef  

cToPol  zr cp c =  if  c==zr  then  Pol [] 
                   else             Pol [(c, PP [] cp)]




      ---------------------------------------------------------

      -- ATTENTION: 
      -- Monomials  equal to Zero  are Always being  Cancelled.

      -- Therefore the   Polynomial Equalities    f==g,  f==[]

      -- coinside with the  ==  from the Standard GOFER prelude

      ---------------------------------------------------------



polNeg :: AddGroup c => Pol c -> Pol c

polNeg (Pol mons) =  Pol  (map (\(c,p)->(neg c,p)) mons)



      -- The power products  p,q, ... :: PP   have the comparison 
      -- inside them.  
      -- Still we apply  p+q, p< q  etc.  on them - because PP is
      -- supplied with the Ordered group structure - see pp.gs.


polAdd, polSub, polMul :: 
                     CommutativeRing c =>  Pol c -> Pol c -> Pol c


polAdd  (Pol [])        g       =  g
polAdd  (Pol ((a,p):f)) (Pol g) =  Pol  (pa  (zero a) ((a,p):f) g)
  where
  pa  _  []    g     =  g
  pa  _  f     []    =  f
  pa  zr (m:f) (n:g) =
    let (a,p) = m 
        (b,q) = n
    in  
      case  compare p q  
      of
        GT ->  m:(pa zr f (n:g))  
        LT ->  n:(pa zr (m:f) g)
        _  ->  let  c = add a b  in  if c==zr then  pa zr f g  
                                     else        (c,p):(pa zr f g)



polSub f g =  polAdd f (polNeg g)



monMul :: Ring c =>  c -> Mon c -> Mon c -> [Mon c]

monMul  zero (a,p) (b,q) =                              
                  let  c = mul a b  
                  in   if  c==zero  then  []  else  [(c, add p q)]


mPolMul ::  Ring c =>  Mon c -> Pol c -> Pol c

mPolMul  (a,p) (Pol f) =  Pol (mpm (zero a) f)  
  where
  mpm _ []    = []
  mpm z (n:f) = (monMul z (a,p) n)++(mpm z f)



cPolMul ::  Ring c =>  c -> Pol c -> Pol c

cPolMul  c (Pol f)  =  Pol (cpm (zero c) f)
  where
  cpm _ []        =  []
  cpm z ((a,p):f) =  let  b= mul c a  in  if b==z then  cpm z f
                                          else     (b,p):(cpm z f)


------------------------------------------------------------------
polCoefDiv :: Ring c =>  Pol c -> c -> [Pol c]

                    -- returns  []  if  f  is not a multiple of  c
polCoefDiv  (Pol mons) c  =      
  let
    cQuotsPar =  map (\a-> divide_l a c) (map fst mons)
  in
    if  any null cQuotsPar  then  []  
    else     
      [ Pol  (zip (map head cQuotsPar) (map snd mons)) ]
------------------------------------------------------------------



polTimes:: Ring c => Pol c -> Integer -> Pol c

polTimes  (Pol [])        _ =  Pol []
polTimes  (Pol ((a,p):f)) n =  Pol (tm (zero a) ((a,p):f))
  where
  tm  _ []        =  []
  tm  z ((a,p):f) =  let  b = times a n  in  if b==z then  tm z f
                                             else   (b,p):(tm z f)



polMul (Pol [])        _       =  Pol  []
polMul (Pol ((a,p):f)) (Pol g) =  Pol  (pm (zero a) ((a,p):f) g)
  where
  pm  _ []    _     =  []   
  pm  _ _     []    =  []   
  pm  z (m:f) (n:g) =  
      let  
        (Pol ms) = polAdd (mPolMul m (Pol g)) (Pol (pm z f (n:g)))
      in
        (monMul z m n) ++ ms



polDivRem :: CommutativeRing c => Pol c -> Pol c -> (Pol c, Pol c)

        --  f g --> (quotient,remainder).
        --  It is the Euclid's division in the case  c  is a Field 
        --  and vars= [v].
        --  Uses divide_l to divide coefficients. Stops when lm(g)
        --  does not divide  lm(currentRemainder).
        --  Example:   x y --> (0,y)

polDivRem  _       (Pol [])         =  
                               error "(polDivRem _ (Pol [])) \n\n"
polDivRem  (Pol f) (Pol ((b,pp):g)) =  d f (Pol []) 
  where
  d  []          q  =  (q, Pol [])   
  d  ((a,pp1):f) q  =  
    let 
      dpp = sub pp1 pp   
    in 
      if  any (<0) (ppP dpp)  then  (q, Pol ((a,pp1):f))   
    else
      case  divide_l a b  
      of
        []  ->  (q, Pol ((a,pp1):f))
        [c] -> 
          let  (Pol ms) = polSub (Pol f) (mPolMul (c,dpp) (Pol g))
          in
            d  ms  (polAdd (Pol [(c,dpp)]) q)
------------------------------------------------------------------

sPol :: SyzygySolvableRing a => 
                           Pol a -> Pol a -> (Pol a, Mon a, Mon a)

               -- S-polynomial  for Non-zero polynomials over a  
               --               Euclidean Ring a :    m1*f1-m2*s2.
               -- It returns also the corresponding  Complementory 
               -- monomial factors  m1, m2.

sPol f g =  let  a    = lc  f                        
                 b    = lc  g                        
                 p    = lpp f                        
                 comp = ppCp p
                 ppf  = ppP p                      
                 ppg  = ppP (lpp g)                
                 ppfc = PP (ppCompl ppf ppg) comp
                 ppgc = PP (ppCompl ppg ppf) comp
                 d    = gcD [a,b]  
                 m1   = (divide b d, ppfc)
                 m2   = (divide a d, ppgc)
            in
              ( polSub (mPolMul m1 f) (mPolMul m2 g),  m1,  m2 )
------------------------------------------------------------------

sVecPol :: SyzygySolvableRing a =>
                  VecPol a -> VecPol a -> (VecPol a, Mon a, Mon a)

sVecPol (f,fs) (g,gs) =             -- s-polynomial for  VecPol a
  let  
    (sp,m1,m2) =  sPol f g
    f1      =  polSub (mPolMul m1 f) (mPolMul m2 g)
    fs1     =  map (mPolMul m1) fs
    gs1     =  map (mPolMul m2) gs
  in
    ( (f1, binOpList polAdd fs1 (map polNeg gs1)),  m1,  m2 )

------------------------------------------------------------------


monLcm :: (SyzygySolvableRing a, Num a) => Mon a -> Mon a -> Mon a

               -- for the  Field(a)  it is better to compute this 
               -- directly as   (unity a,  ppLcm ...)

monLcm (a,p) (b,q) =  let  g  = gcD[a,b]  
                           p1 = ppP  p
                           q1 = ppP  q
                           cp = ppCp p
                      in      
                        ( a*(divide b g),  PP (ppLcm p1 q1) cp )





--------------------  for  Pol (a,b)  ----------------------------


toPairOfPol :: (AddMonoid a, AddMonoid b) => 
                                        Pol (a,b) -> (Pol a,Pol b)

toPairOfPol  (Pol []  ) =  (Pol [], Pol [])
toPairOfPol  (Pol mons) =  
  let
    (a,b) = lc (Pol mons)
    za    = zero a
    zb    = zero b
  in  
    pcp  za zb mons
      where
        pcp _  _  []            =  (Pol [], Pol [])
        pcp za zb (((a,b),p):f) =  
          let 
            (Pol ms1, Pol ms2) = pcp za zb f  
            (ms1',ms2')        = 
               case  (a==za,b==zb)  of 
                        (True ,True ) ->  ( ms1      , ms2       )
                        (False,True ) ->  ( (a,p):ms1, ms2       )
                        (True ,False) ->  ( ms1      , (b,p):ms2 )
                        _             ->  ( (a,p):ms1, (b,p):ms2 )
          in
            (Pol ms1', Pol ms2')
------------------------------------------------------------------


showsPol ::  Ring c =>  [String] -> Pol c -> String -> String
                     -- vars        f        s

       -- Writing polynomial in given variables. 
       -- Prepends the polynomial image to the initial string  s.
       --   If  c  is Ordered, then the mode  `ord'  is set which 
       -- writes   ...- m  instead of  ....+ m   for the Negative 
       -- coefficient monomials.
       --   If  c  has unity  then  unity coefficient images  are 
       -- skipped.

showsPol  _    (Pol []) =  ('0':)
showsPol  vars f        =  wr  u ord mons    where

  (Pol mons) =  f 
  u          =  unity_l (lc f)
  ord        =  if  (ordAdd (lc f))==Yes  then  True  else False
    
  wr  u mode mons =   
    let   
      wMon (c,pp) =  
        let  
          pp_str =  wpp vars (ppP pp) ""
        in
          case  (u,pp_str)  of 
                 (_   , [] ) ->  w c
                 ([]  , _  ) ->  (w c).('*':).(w pp_str)
                 ([un], _  ) ->  if c==un then  (w pp_str)  
                                 else      (w c).('*':).(w pp_str)

      wpp  _      []     =  id
      wpp  []     pp     =  
             error "wpp:  power product exheeds variable list\n\n"
      wpp  _      [0]    =  
                       error "wpp: power product ends with 0 \n\n"
      wpp  (v:vs) (0:pp) =  wpp vs pp
      wpp  (v:vs) (1:pp) =  (v++).(wpp vs pp)
      wpp  (v:vs) (n:pp) =  (v++).('^':).(w n).(wpp vs pp)
    in 
      case  (mode,mons) 
      of
        (_    , []          ) -> ('0':) 
        (_    , [m]         ) -> wMon m
        (False, (m:ms)      ) -> (wMon m).(" + "++).(wr u mode ms)
        (True , (m:(c,p):ms)) ->
            if  (compare c (zero c))==LT  then 
                     (wMon m).(" - "++).(wr u mode ((neg c,p):ms))
            else     (wMon m).(" + "++).(wr u mode ((c,p)    :ms))






------------------------------------------------------------------
------------------------------------------------------------------


-----  Instances  for the  polynomial constructor  (Pol c)  ------





{-
  hasZeroDiv ((c,_):_) =  hasZeroDiv c         -- TO BE PROVED

  hasNilp    ((c,_):_) =  hasNilp c            -- ?

  field       _ = No
  euclidean   _ = No       -- the variable list is infinite ...
  princIdeals _ = No     

  syzygySolvable ((c,_):_) =  syzygySolvable c
  factorial      ((c,_):_) =  factorial c
  factorizeIsTotal _       =  No

--  factorizeIsTotal ((c,_):_) =  
--                     case  (field c, card c)  of  (Yes,[n]) -> Yes
--                                                  _         -> No

  hasGrBas        ((c,_):_) =  euclidean c
  moduloIsCanonic ((c,_):_) =  euclidean c
  minNormRemValid _         =  No
     
-}







---------------------------  Set  --------------------------------


instance  CommutativeRing a =>  Set (Pol a)   where

  card _ =  [[]]

  setTerm  f = 
    (setDomFuncs  (funcNames "set")  
      (setDomCons  (Polynomial (ringTerm (lc f)) []) trivialDomain
    ))

             -----------------------------------------------------
             -- Polynomial  (in anonymous variables)   Writes  and
             -- Reads  in the default variables    "x1", "x2", ...
             -- We presume also that 
             --  None of these strings can be a Coefficient image.
             -----------------------------------------------------

  w  f@(Pol mons) =  w  ( VarP  f (map (('x':).show) [1..n]) )
       where
       n =  maximum  (map  (\(c,p)-> genericLength (ppP p))  mons)


  fromExpr (Pol []) e =  
                 error( "(fromExpr (Pol []) e):  Non-zero sample "
                         ++ "polynomial needed \n\n"
                      )
  fromExpr f        e =  let  un = unity (lc f)
                              cp = ppCp  (lpp f)
                         in         exprToPol [] (zero un) un cp e




------------------------  AddGroup  ------------------------------


instance  CommutativeRing a =>  AddSemigroup (Pol a)   where

  addSmgTerm (Pol ((c,p):_)) =   let  f = Pol [(c,p)]  in

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+",cyclicAdd f),("gr+",groupAdd f),
           ("ord+",ordAdd f)
         ]
         (setDomCons (Polynomial (ringTerm c) []) trivialDomain)
    ) )

  cyclicAdd _ =  No
  groupAdd  _ =  Yes
  ordAdd    _ =  No

  add         =  polAdd
  zero _      =  Pol []
  zero_l  _   =  [ Pol [] ]
  neg         =  polNeg
  neg_l   f   =  [polNeg f]
  sub_l   f g =  [polSub f g]
  times_l f n =  [polTimes f n]



instance  CommutativeRing a =>  AddMonoid (Pol a)
instance  CommutativeRing a =>  AddGroup  (Pol a)





----------------------  MulSemigroup  ----------------------------


instance  CommutativeRing c =>  MulSemigroup (Pol c)
  where

  mulSmgTerm (Pol ((c,p):_)) =   let  f = Pol [(c,p)]  in

    (setDomFuncs  (funcNames "mulSmg")  
      (setDomProps
         [ ("comm", commutative c),  ("cyc*", Unknown),
           ("gr*", No)
         ]
         (setDomCons (Polynomial (ringTerm c) []) trivialDomain)
    ) )

  commutative f =  commutative (lc f)
  groupMul    _ =  No
  cyclicMul   _ =  Unknown

  mul =  polMul

  unity_l  (Pol ((c,p):_)) =  
     case  (unity_l c, zero c)  of 
                            ([]  , _) ->  []
                            ([un], z) ->  [ cToPol z (ppCp p) un ]

  inv_l  (Pol [(c,p)]) =  if  p/=(zero p)  then  []
                          else
                            case  inv_l c  of
                                          []   -> []
                                          [ic] -> [ Pol [(ic,p)] ]

  divide_l f g =  case  polDivRem f g  of  (q,Pol []) -> [q]
                                           _          -> []

  -- power  is defined automatically




instance  (CommutativeRing c, MulMonoid c) =>  MulMonoid (Pol c)






-------------------------  Ring  ---------------------------------


instance  CommutativeRing c =>  Ring (Pol c)
  where

  ringTerm (Pol ((c,p):_)) =   let  f = Pol [(c,p)]  in

    (setDomFuncs      (funcNames "ring")
      (setDomProps    (polRing_props (ringTerm c) [])
         (setDomCons  (Polynomial (ringTerm c) []) trivialDomain)
    ) )
    where
    polRing_props cTerm vars =
                    polPrs  (domProps cTerm) (domCons cTerm) vars
      where
      polPrs  cProps cCons vars =  []
                              --  (polRingAxioms vars) ...




  hasZeroDiv f =  hasZeroDiv (lc f)         -- TO BE PROVED
  hasNilp    f =  hasNilp    (lc f)         -- ?

  field       _ = No
  euclidean   _ = No       -- the variable list is infinite ...
  princIdeals _ = No     

  syzygySolvable f =  syzygySolvable (lc f)
  factorial      f =  factorial      (lc f)

  factorizeIsTotal _ =  No

--  factorizeIsTotal f =  
--         case  (field (lc f), card (lc f))  of  (Yes,[n]) -> Yes
--                                                _         -> No

                       -- it will be good to have factorization
                       -- only for this case so far (June,1995).


  hasGrBas        f =  euclidean (lc f)
  moduloIsCanonic f =  euclidean (lc f)
  minNormRemValid _ =  No


  i_l  (Pol ((c,p):_)) n  =  case  (i_l c n, zero c)  of
                               ([] , _) -> []
                               ([a], z) -> [ cToPol z (ppCp p) a ]
  char  f =  char (lc f)




instance  CommutativeRing c =>  CommutativeRing (Pol c)



instance  CommutativeRing c =>  Num (Pol c)  where
  negate = neg
  (+)    = add
  (-)    = sub  
  (*)    = mul


instance  CommutativeRing c =>  Fractional (Pol c)  where

  (/) f  = fst.(polDivRem f)      -- be  C A R E F U L:  x/y = 0







--------------------  SyzygySolvableRing  ------------------------



instance  (SyzygySolvableRing a, Num a) => 
                                SyzygySolvableRing (Pol a)   where


            -- canInv, gcD, lcM  are total if  (factorial c)==Yes
 
  -- lcM  is the default one

  canInv (Pol [])              =  error "canInv (Pol []) \n\n"  
  canInv (Pol ((c,PP _ cp):f)) =  Pol [(canInv c, PP [] cp)]

  canAssoc (Pol []) =  Pol []
  canAssoc f        =  cPolMul (inv (canInv (lc f))) f

  factorize _  =  error "no polynomial factorization yet \n\n"

  gcD []            = error "(gcD [])"
  gcD [f]           = f
  gcD ((Pol []):fs) = gcD fs
  gcD (f:fs)        = case  (factorial (lc f), field (lc f))  of

     (_  , Yes) -> gcdL (polGCD "field") (f:fs)
     (Yes, _  ) -> gcdL (polGCD ""     ) (f:fs)
     _          -> 
             error( "(gcD fs): coefficient domain should be "
                    ++" factorial.\n" ++ "head fs =  " ++ (w f "")
                  )


  --grBasis :: String -> [Pol c] ->  ( [Pol c], Matrix (Pol c) )

  grBasis _    []            =  ( [], Mt [] )    
  grBasis _    ((Pol []):fs) =  error  "grBasis [ [] ... ] \n\n"
  grBasis mode (f       :fs) =  let  c = lc f  in

    case  (euclidean c, field c)  
    of
      (_  , Yes) ->  grBas  mode "field" (f:fs)
      (Yes, _  ) ->  grBas  mode "euc"   (f:fs)
      _          ->  
       error ( "(grBasis _ polynomials)" ++
               "  coefficients should be from Euclidean ring \n\n"
             )
  ----------------------------------------------------------------

  moduloBasis _     fs (Pol []) = 
                               ( Pol [], map (const (Pol [])) fs )
  moduloBasis modes fs f        =        
    let                                -- modes = ""|"c"|"g"|"cg"
      c             =  lc f  
      (rMode,gMode) =  
        case  modes  of  
          ""   ->  ("" , "" )
          "c"  ->  ("r", "" )
          "g"  ->  ("" , "g")
          "cg" ->  ("r", "g")
          _    ->  error( "moduloBasis:  modes string may be " ++
                          "  \"\",  \"c\",  \"g\",  \"cg\"  \n\n"
                        )
    in
      case  (euclidean c, rMode, gMode)
      of
        (Yes, "" , "g") ->  polNF ""  fs f
                              --polNF does not find Groebner basis
        (Yes, "r", "g") ->  polNF "r" fs f

        (Yes, rM , _  ) -> 
          let 
            (gs, (Mt rows)) = 
                     if  (field c)==Yes  then  grBas rM "field" fs
                     else                      grBas rM "euc"   fs
            (r , q      ) =  polNF rM gs f
          in         
            (r, rowMatrMul q rows)

        _               ->
                       -- case  domCons (ringTerm c)  of

         error( "(moduloBasis _ _ f)" ++ "  for non-Euclidean"++
                "coefficients DoCon will need to see construction"
                ++"...  \n\n"
              )
  ----------------------------------------------------------------

  syzygyBasis  mode fs =  case  filter (not.isZeroPol) fs  of
    
    []    ->  error "(syzygyBasis _ [])  \n\n"
    [f]   ->  []
    (f:fs)->  case  euclidean (lc f)  
              of
                Yes -> polRelBasis_euc mode (f:fs)
                _   -> error( "(syzygyBasis _ _)  " ++ 
                              "coefficients should be from " ++ 
                              "Euclidean ring  \n\n"
                            )








------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





   ---------------------------------------------------------------

   -- Fraction  constructor is so far only for the FACTORIAL rings

   -- Hence it yeilds a FIELD.


   -- *** ATTENTION: ***

   -- (1) In  n:/d   d/=zero,  and  n,d  are cancelled by GCD.

   -- (2) The fraction  n:/m  is *not* necessarily cancelled by 
   --    the *canonical invertible* factor.  
   -- For example, an arithmetical operation *cannot* return
   --                    2:/4  or  (x^2-1):/(x+1)  
   -- but it may return  (-1):/(-2).

   -- The equality of fractions is expressed as  n*d1-n1*d == 0.

   -- This is done because the  *canonical invertible*  function 
   -- canInv  may be not easy to compute for some domains.
   -- But knowing that it is fast for certain domain, the 
   -- programmer may apply 'canFr' for the canonical cancellation
   -- (through canInv).  And for the canonical forms  
   -- n:/d == n1:/d1  =  (n,d)==(n1,d1).

   -- ATTENTION: 
   -- the below functions   num, denom   are the correct functions
   -- *only for the canonical forms* :
   -- Thus it is  *NOT true*  that 
   --                 fr1==fr2  =>  num fr1 == num fr2

   -- (2) distincts  Fraction  from  Ratio.  
   --     (see == definition for  :% ).
   --     Ratio  needs Ord,  and  Fraction does not.
   --     It is not clear how Ratio would work for the ring of
   --     polynomails over Rational, how the fractions like 
   --     (2x+1):%(-3x+2)  would cancel.
   ---------------------------------------------------------------




module  Fraction  where

import  PreludeInteger
import  Categ
import  Categ1
import  Matrix
import  IParse



infixl 7  :/

data  Fraction a =  a :/ a    deriving(Text)

num   (n :/ _)  =  n            -- these are the correct functions
denom (_ :/ d)  =  d            -- only for the canonical forms

zeroFr, unityFr ::  Ring a =>  a -> (Fraction a)      -- x /= zero

zeroFr  x =  (zero  x):/(unity x)
unityFr x =  (unity x):/(unity x)



canFr ::  
       SyzygySolvableRing a =>  String -> Fraction a -> Fraction a
                                --mode  

            -- mode = ""   means "cancel fraction by  gcd  only".
            --        "i"  means  "gcd  is already 1, 
            --                    cancel by canonical invertible".

canFr ""  (n:/d) = let  g = gcD [n,d] in (divide n g ):/(divide d g )
canFr "i" (n:/d) = let  ci= canInv d  in (divide n ci):/(divide d ci)
canFr m   _      = 
    error "(canFr mode fraction):  mode== \"\" | \"i\"  expected\n\n"



instance  (SyzygySolvableRing a, Fractional a) =>  Eq (Fraction a)
  where
  (n:/d)==(n1:/d1) = if  n==(zero d)  then  n1==(zero d)
                     else
                       let  gn = gcD [n,n1]
                            gd = gcD [d,d1]
                       in   (n/gn)*(d1/gd) == (n1/gn)*(d/gd)
                           




---------------------------  Set  --------------------------------


instance  (SyzygySolvableRing a, Fractional a) => Set (Fraction a)  
  where  

  setTerm (_:/d) = 
          (setDomFuncs  (funcNames "set")  
             (setDomCons  (FractionC (ringTerm d))  trivialDomain
          ))

  card (_:/d) =  case  card d  
                 of  
                   []    -> []
                   [[]]  -> [[]]
                   [[n]] -> []      -- *** define it correctly !

  w (n:/d) =  if  d==(unity d)  then  w n
              else           ('(':).(w n).(")/("++).(w d).(')':)

  --------------------------------------------------------------
  fromExpr (n:/d) e =  case  fromExpr d e  of  
                              -- element 
                              -- of  a  converts to fraction too
    ([n1],"") -> ( [n1:/(unity d)], "" )

    _         -> let  fre = fromExpr (n:/d)  in

      (case  e  of
        (E (L ":/") [e1] [e2]) -> 
                                fr (fromExpr d e1) (fromExpr d e2)
        (E (L "-")  []   [e2]) -> f "-u" ([], "") (fre e2)
        (E (L "-")  [e1] [e2]) -> f "-"  (fre e1) (fre e2)
        (E (L "+")  [e1] [e2]) -> f "+"  (fre e1) (fre e2)
        (E (L "*")  [e1] [e2]) -> f "*"  (fre e1) (fre e2)
        (E (L "/")  [e1] [e2]) -> f "/"  (fre e1) (fre e2)
        (E (L "^")  [e1] [e2]) ->
                            pw (fre e1) (fromExpr (1::Integer) e2)
        _                      -> 
          ( [], "(fromExpr "++(w (n:/d) " ")++(showsExpr e ")\n"))
      )
        where  
        fr ([n1],"" ) ([d1],"" ) = ( [canFr "" (n1:/d1)], "" )
        fr ([n1],"" ) (_   ,msg) = ( []                 , msg)
        fr (_   ,msg) _          = ( []                 , msg)

        f "-u"  _         ([x] ,"") = ( [(-x)], "" )
        f "-"   ([x], "") ([y] ,"") = ( [x-y] , "" )
        f "+"   ([x], "") ([y] ,"") = ( [x+y] , "" )
        f "*"   ([x], "") ([y] ,"") = ( [x*y] , "" )
        f "/"   ([x], "") ([y] ,"") = 
                   case  divide_l x y  of
                     [q] -> ( [q], "" )
                     []  -> ( [] , "fromExpr "++ (w (n:/d) " ") ++ 
                                   (showsExpr e ")\n")          ++
                                   "failed to divide with  / "       
                            )

        pw  ([x],"" ) ([n],"" ) = ([x^n], "" ) 
        pw  ([x],"" ) (_  ,msg) = ([]   , msg)
        pw  (_  ,msg) _         = ([]   , msg)






---------------------  AddSemigroup  -----------------------------


instance  (SyzygySolvableRing a, Fractional a) => 
                                 AddSemigroup (Fraction a)   where

  addSmgTerm (_ :/ d) =
    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [("cyc+",Unknown),("gr+",Yes),("ord+",ordAdd d)]
         (setDomCons (FractionC (ringTerm d)) trivialDomain)
    ) )

  groupAdd _      =  Yes
  ordAdd   (_:/d) =  ordAdd d

  -- cyclicAdd  

  zero_l (n:/d) =  [ (zero d):/d ]
  neg_l  (n:/d) =  [ (neg  n):/d ]

  times_l (n:/d) k =  let  k_a  =  i (unity d) k
                           g    =  gcD [k_a,d]
                      in                    [ (n*(k_a/g)):/(d/g) ]

  sub_l  x y =  [ add x (neg y) ]

  add  (n1:/d1) (n2:/d2) =  
    let  
      zr = zero d1  
    in
      (case  (n1==zr, n2==zr)  of

        (True,_   ) ->  n2:/d2
        (_   ,True) ->  n1:/d1
        _           ->  let  g   = gcD [d1,d2]  
                             dd1 = d1/g
                             dd2 = d2/g  
                             n   = n1*dd2+n2*dd1
                             gg  = gcD [n,g]
                        in              (n/gg):/((dd1*dd2)*(g/gg))
      )

  compare  (n1:/d1) y =
                      let  (n:/d) = sub (n1:/d1) y 
                           zr     = zero d1
                      in    
                        case  (compare n zr, compare d zr)  of
                                                    (EQ, _ ) -> EQ
                                                    (GT, GT) -> GT
                                                    (LT, LT) -> GT
                                                    _        -> LT


instance  (SyzygySolvableRing a, Fractional a) =>
                                            AddMonoid (Fraction a)
instance  (SyzygySolvableRing a, Num a, Fractional a) => 
                                            AddGroup  (Fraction a)




------------------------------------------------------------------
instance  (SyzygySolvableRing a, OrdAddMonoid a, Fractional a) =>
                                         OrdAddMonoid (Fraction a)


instance  (SyzygySolvableRing a, OrdAddMonoid a, Fractional a) =>
                                                  Ord (Fraction a)
  where
  x <= y =  case  compare x y  of  GT -> False
                                   _  -> True
  x <  y =  case  compare x y  of  LT -> True
                                   _  -> False


instance  (SyzygySolvableRing a, OrdAddMonoid a, Fractional a) =>
                                          OrdAddGroup (Fraction a)




---------------------  MulSemigroup  -----------------------------



instance  (SyzygySolvableRing a, Fractional a) => 
                                MulSemigroup (Fraction a)    where

  mulSmgTerm (_:/d) =   
          (setDomFuncs  (funcNames "mulSmg")  
            (setDomProps
               [ ("comm",Yes), ("cyc*",No) {-because of 0-},
                 ("gr*",No) 
               ]
               (setDomCons (FractionC (ringTerm d)) trivialDomain)
          ) )

  commutative  _ =  Yes
  groupMul     _ =  No     -- because of zero fraction         
  cyclicMul    _ =  No     -- ...

  unity_l (_:/d) =  [unityFr d]

  inv_l   (n:/d) =  if  n==(zero d)  then  []  else  [ d:/n ]


  power_l (n:/d) k =  
    let  
      { zr = zero d;  un = unity d }
    in    
      (case  (n==zr, k==0, k>0)  of
         (True , True, _   ) ->
                      error( ("power_l "++)$(w (n:/d))$" 0 \n\n" )
         (_    , True, _   ) -> [ unityFr d ]
         (True , _   , _   ) -> [ zeroFr  d ]
         (_    , _   , True) -> [ (power n k   ):/(power d k   ) ]
         _                   -> [ (power d (-k)):/(power n (-k)) ]
      )



  mul  (n1:/d1) (n2:/d2) =  let  zr = zero d1
                            in   
                              if (n1==zr)||(n2==zr) then zeroFr d1
                              else
                                let  g12 = gcD [n1,d2]  
                                     g21 = gcD [n2,d1]
                                     nn1 = n1/g12
                                     dd1 = d1/g21
                                     nn2 = n2/g21
                                     dd2 = d2/g12
                                in            (nn1*nn2):/(dd1*dd2)


  divide_l  x (n2:/d2) =  
             if  n2==(zero d2)  then  []  else  [ mul x (d2:/n2) ]





instance  (SyzygySolvableRing a, Fractional a) =>
                                            MulMonoid (Fraction a)






-------------------------  Ring  ---------------------------------


instance  (SyzygySolvableRing a, Fractional a) => 
                                         Ring (Fraction a)   where


  ringTerm (n:/d) = 
    (setDomFuncs      (funcNames "ring")
      (setDomProps    
        -- (complete 
                 [ ("fld", field(n:/d)) ]  
        -- )  
         (setDomCons  (FractionC (ringTerm d)) trivialDomain)
    ) )


  field  (n:/d) = 
    if  (factorial d)==Yes  then  Yes
    else    
      error (w (n:/d) 
               "\nFraction is valid only if  factorial==Yes\n\n"
            )

  char   (n:/d) =  char d

  i_l  (n:/d) k =  [ (i d k):/(unity d) ]




instance  (SyzygySolvableRing a, Num a, Fractional a) => 
                                      CommutativeRing (Fraction a)  


------------------------------------------------------------------

instance  (SyzygySolvableRing a, Fractional a) => 
                            SyzygySolvableRing (Fraction a)  where

  canAssoc (n:/d) =  let  zr = zero d  in
                          if n==zr then  zeroFr d  else  unityFr d

  canInv   (n:/d) =  let  zr = zero d  in
                              if n==zr then  unityFr d  else  n:/d

  eucNorm (n:/d) = 
     if  n==(zero d)  then  error( "eucNorm "++(w (n:/d) "\n\n") )
     else                   0

  divRem  _ (n:/d) y  =  [ divide (n:/d) y,  zeroFr d ]

  gcD  []          =  error "gcD [] \n\n"
  gcD  ((n:/d):fs) =  if n==(zero d) then  gcD fs  else  unityFr d

  factorize _ =  []

  moduloBasis _ []            y =  ( y, [] )
  moduloBasis _ ((n:/d):fs) y = 
      ( zeroFr d,  (divide y (n:/d)):(map (const (zeroFr d)) fs) )

  grBasis  _ []          =  ( [], Mt [] )
  grBasis  _ ((n:/d):fs) = 
              ( [ unityFr d ], 
                Mt  [ (inv (n:/d)) : (map (const (zeroFr d)) fs) ]
              )

  -- syzygyBasis _ ((n:/d):fs) =





--------------------------  field  -------------------------------


instance  (SyzygySolvableRing a, Fractional a) => 
                                                Field (Fraction a)
  where
  hasAbs (n:/d) =  case  domCons (ringTerm d)  of 
                                            (Basic "Z") -> Yes
                                            _           -> Unknown
  real   (n:/d) =  case  domCons (ringTerm d)  of 
                                            (Basic "Z") -> Yes
                                            _           -> Unknown
------------------------------------------------------------------

instance  (SyzygySolvableRing a, Fractional a) => Num (Fraction a)
  where
  negate  = neg
  (+)     = add
  (-)     = sub
  (*)     = mul
------------------------------------------------------------------

instance  (SyzygySolvableRing a, Fractional a) =>
                                           Fractional (Fraction a)
  where
  (/) = divide
  fromRational (n:%d) =  (fromInteger n)/(fromInteger d)

;





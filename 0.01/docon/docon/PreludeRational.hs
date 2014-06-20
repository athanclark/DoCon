------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




------------------------------------------------------------------
--            Instances for  Integral a => Ratio a              --


-- We presume that the DoCon operations take and return the
-- rationals in their *canonocal form* :   n :% d,
-- where  n, d  are reduced, and  d > 0.
-- This agrees with the Standard Prelude.

-- %   reduces the rational to this canonical form   -  according 
--     to the  Standard Prelude  -  see there the definitions for 
--     :%, %, /.
------------------------------------------------------------------





module  PreludeRational
  (
    Set(..),    AddSemigroup(..),AddMonoid(..),AddGroup(..),
      OrdAddMonoid(..), OrdAddGroup(..),  
    MulSemigroup(..),MulMonoid(..),MulGroup(..),
    Ring(..),CommutativeRing(..),SyzygySolvableRing(..),Field(..)
  )

where

import  PreludeInteger
import  Categ
import  Categ1
import  Matrix
import  IParse







-------------------------  Set  ----------------------------------


instance  (Integral a, SyzygySolvableRing a) =>  Set (Ratio a)
  where  

  card (_:%d) =  case  card d  
                 of  
                   []   -> []
                   [[]] -> [[]]
                   [[n]]-> []      --*** define it as in  Fraction

  setTerm (_:%d) = 
          (setDomFuncs  (funcNames "set")  
             (setDomCons  (RatioC (ringTerm d))  trivialDomain
          ))

  w (n:%d) =  if  d==(unity d)  then  w n
              else              ('(':).(w n).('/':).(w d).(')':)

  ----------------------------------------------------------------
  fromExpr (n:%d) e =  case  fromExpr d e  of  
                              -- element 
                              -- of  a  converts to fraction too
    ([n1],"") -> ( [n1:%(unity d)], "" )

    _         -> let  fre = fromExpr (n:%d)  in

      (case  e  of
        (E (L "%") [e1] [e2]) -> 
                                fr (fromExpr d e1) (fromExpr d e2)
        (E (L "-") []   [e2]) -> f "-u" ([], "") (fre e2)
        (E (L "-") [e1] [e2]) -> f "-"  (fre e1) (fre e2)
        (E (L "+") [e1] [e2]) -> f "+"  (fre e1) (fre e2)
        (E (L "*") [e1] [e2]) -> f "*"  (fre e1) (fre e2)
        (E (L "/") [e1] [e2]) -> f "/"  (fre e1) (fre e2)
        (E (L "^") [e1] [e2]) -> 
                            pw (fre e1) (fromExpr (1::Integer) e2)
        _                     -> 
            (  [],  "(fromExpr <Rational> "++(showsExpr e " )")  )
      )
        where  
        fr  ([n1],"") ([d1],"")  = ( [n1%d1], ""  )
        fr  ([x], "") (_   ,msg) = ( [],      msg )
        fr  (_  ,msg) _          = ( [],      msg )

        f "-u" _         ([x] ,"") = ( [(-x)] , "" )
        f "-"  ([x], "") ([y] ,"") = ( [x-y]  , "" )
        f "+"  ([x], "") ([y] ,"") = ( [x+y]  , "" )
        f "*"  ([x], "") ([y] ,"") = ( [x*y]  , "" )
        f "/"  ([x], "") ([y] ,"") = 
                      case  divide_l x y  of
                        [q] -> ( [q], "" )
                        []  -> ( [] , "fromExpr "++(w (n%d) " ")++
                                      (showsExpr e ")\n") ++
                                      "failed to divide with  / "
                               )
        f _    ([x], "") pair      = pair
        f _    pair       _        = pair

        pw  ([x],"" ) ([n],"" ) = ([x^n], "" ) 
        pw  ([x],"" ) (_  ,msg) = ([]   , msg)
        pw  (_  ,msg) _         = ([]   , msg)
  --------------------------------------------------------------








---------------------  AddSemigroup  -----------------------------


instance  (Integral a, SyzygySolvableRing a) => 
                                            AddSemigroup (Ratio a)   
  where

  addSmgTerm (_:%d) =
    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [("cyc+",Unknown),("gr+",Yes),("ord+",ordAdd d)]
         (setDomCons (RatioC (ringTerm d)) trivialDomain)
    ) )

  groupAdd _      =  Yes
  ordAdd   (_:%d) =  ordAdd d

  -- cyclicAdd  

  zero_l _  =  [ fromInteger 0 ]
  neg_l  x  =  [ (-x) ]

  times_l x n =  [ x*(fromInteger n) ]
  sub_l   x y =  [ x-y ]

  add =  (+)

  compare  x y =  if  x<y  then LT 
                  else          if  x>y  then GT  else EQ



instance  (Integral a, SyzygySolvableRing a)=> AddMonoid (Ratio a)

instance  (Integral a, SyzygySolvableRing a) => AddGroup (Ratio a)




------------------------------------------------------------------
instance  (Integral a, SyzygySolvableRing a, OrdAddMonoid a) 
          =>                    
          OrdAddMonoid (Ratio a)


instance  (Integral a, SyzygySolvableRing a, OrdAddMonoid a) 
          => 
          OrdAddGroup (Ratio a)




---------------------  MulSemigroup  -----------------------------



instance  (Integral a, SyzygySolvableRing a) => 
                                            MulSemigroup (Ratio a)    
  where

  mulSmgTerm (_:%d) =   
          (setDomFuncs  (funcNames "mulSmg")  
            (setDomProps
               [ ("comm",Yes), ("cyc*",No) {-because of 0-},
                 ("gr*",No) 
               ]
               (setDomCons (RatioC (ringTerm d)) trivialDomain)
          ) )

  commutative  _ =  Yes
  groupMul     _ =  No     -- because of zero fraction         
  cyclicMul    _ =  No     -- ...

  unity   _ =  fromInteger 1
  unity_l _ =  [fromInteger 1]

  inv_l  (n:%d) =  case  compare n (zero d)  of 
                                              EQ -> []
                                              GT -> [ d :% n]
                                              LT -> [ (-d):%(-n) ]
        -- this is to avoid extra  gcd
        -- operation (which may take place in  x-> 1/x  script)

  mul          =  (*) 
  power        =  (^)
  power_l  x k =  [ x^k ]

  divide_l  x (n2 :% d2) =  
                 if  n2==(zero d2)  then  []  else  [ x/(n2:%d2) ]





instance (Integral a, SyzygySolvableRing a) => MulMonoid (Ratio a)






-------------------------  Ring  ---------------------------------


instance  (Integral a, SyzygySolvableRing a) =>  Ring (Ratio a)
  where

  ringTerm (n:%d) = 
    (setDomFuncs      (funcNames "ring")
      (setDomProps    
        -- (complete 
                 [ ("fld", field(n:%d)) ]  
        -- )  
         (setDomCons  (RatioC (ringTerm d)) trivialDomain)
    ) )


  field x =  if  (factorizeIsTotal (denominator x))==Yes  then Yes
             else    
                    error (w x  ( "\nfraction is valid only"
                                   ++" if  factorizeIsTotal==Yes" 
                                )
                          )     

  char  x =  char (denominator x)

  i_l  (n:%d) k =  [ fromInteger k ]




instance  (Integral a, SyzygySolvableRing a) => 
                                         CommutativeRing (Ratio a)  


------------------------------------------------------------------

instance  (Integral a, SyzygySolvableRing a) => 
                               SyzygySolvableRing (Ratio a)  where

  canAssoc x =  if  x==(fromInteger 0)  then  fromInteger 0  
                else                          fromInteger 1  
  canInv   x =  if  x==(fromInteger 0)  then  fromInteger 1  
                else                          x  

  eucNorm  x =  if  x==(fromInteger 0)  then  
                                      error ("eucNorm "++(show x))
                else                  fromInteger 0

  divRem  _ x y  =  [ divide x y,  fromInteger 0 ]

  gcD  xs =  gc  xs (fromInteger 0)
    where
    gc []     _  =  error "gcD []"
    gc (x:xs) zr =  if x==zr then  gc xs zr  else  (fromInteger 1)

  factorize _ =  []

  moduloBasis  _ xs y =  mb  xs y  (fromInteger 0)
    where
    mb []     y  _  =  ( y, [] )
    mb (x:xs) y  zr =  ( zr,  (divide y x):(map (const zr) xs) )

  grBasis  _ xs =  gb xs (fromInteger 0) (fromInteger 1)
    where
    gb []     _  _  =  ( [], Mt [] )
    gb (x:xs) zr un =  ( [un],  Mt [(inv x):(map (const zr) xs)] )

  -- syzygyBasis 





--------------------------  field  -------------------------------


instance  (Integral a, SyzygySolvableRing a) =>  Field (Ratio a)
  where
  hasAbs x =  case  domCons (ringTerm (denominator x))  of 
                                            (Basic "Z") -> Yes
                                            _           -> Unknown
  real   x =  case  domCons (ringTerm (denominator x))  of 
                                            (Basic "Z") -> Yes
                                            _           -> Unknown
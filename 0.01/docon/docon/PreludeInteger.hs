------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




module  PreludeInteger 
  (
    Fractional(..),   Set(..), 
    AddSemigroup(..),AddMonoid(..),AddGroup(..),OrdAddMonoid(..),
      OrdAddGroup(..),  
    MulSemigroup(..),MulMonoid(..),
    Ring(..),CommutativeRing(..),SyzygySolvableRing(..),
    ModOverInt
  )
where

import  PreludeChar
import  PreludeList
import  PreludeRational
import  Categ
import  Categ1
import  Generic
import  Matrix
import  IParse






---------------------------  Set  --------------------------------


instance  Set Integer    where   

  card    _ =  [[]]

  setTerm _ =  (setDomFuncs      (funcNames "set") 
                 (setDomCons     (Basic "Z")
                    (setDomName  "Z"   trivialDomain 
               )))

  w =  shows

  ----------------------------------------------------------------
  fromExpr n e =  let  fre = fromExpr n  in 

    (case  e  of
      (L s)                 ->  
           (case  (reads s ::[(Integer,String)])  of 
             [(n,_)]-> ( [n], "" )
             _      -> 
                     ( [] , "(fromExpr <Integer> "++(show (L s)) )
           )
      (E (L "-") []   [e2]) ->  f "-u" ([], "") (fre e2)
      (E (L "-") [e1] [e2]) ->  f "-"  (fre e1) (fre e2)
      (E (L "+") [e1] [e2]) ->  f "+"  (fre e1) (fre e2)
      (E (L "*") [e1] [e2]) ->  f "*"  (fre e1) (fre e2)
      (E (L "^") [e1] [e2]) ->  f "^"  (fre e1) (fre e2)
      (E (L "/") [e1] [e2]) ->  f "/"  (fre e1) (fre e2)
      _                     ->  
               ( [] , "(fromExpr <Integer> "++(showsExpr e " )") )
    )
      where  f "-u" _        ([m],"") = ( [(- m)], "" )
             f "-"  ([k],"") ([l],"") = ( [k-l],   "" )
             f "+"  ([k],"") ([l],"") = ( [k+l],   "" )
             f "*"  ([k],"") ([l],"") = ( [k*l],   "" )
             f "^"  ([k],"") ([l],"") = ( [k^l],   "" )
             f "/"  ([k],"") ([l],"") = 
                       case  divide_l k l  of
                         [q] -> ( [q], "" )
                         []  -> ( [] , "fromExpr "++(w n " ")++ 
                                       (showsExpr e ")\n")   ++
                                       "failed to divide with  / "
                                )
             f _    ([k],"") pair     = pair
             f _    pair     _        = pair
  ----------------------------------------------------------------







----------------------  Semigroup  -------------------------------


instance  AddSemigroup Integer    where 

  addSmgTerm _ =  
     (setDomFuncs        (funcNames "addSmg")
       (setDomProps      [("cyc+",Yes),("gr+",Yes),("ord+",Yes)] 
         (setDomCons     (Basic "Z") 
            (setDomName  "Z"  trivialDomain 
     ))))

  cyclicAdd _ = Yes 
  groupAdd  _ = Yes
  ordAdd    _ = Yes

  add         =  (+)
  zero    _   =  0
  zero_l  _   =  [0]
  neg         =  (-) 0
  neg_l   x   =  [neg x]
  times       =  (*)
  times_l x n =  [times x n]

  compare  n m | n<m       = LT
               | n>m       = GT
               | otherwise = EQ


instance  AddMonoid Integer 
instance  AddGroup  Integer 


------------------------------------------------------------------
instance  MulSemigroup Integer    where 

  mulSmgTerm _ =  
    (setDomFuncs       (funcNames "mulSmg")
      (setDomProps     [("comm",Yes),("cyc*",No),("gr*",No)] 
        (setDomCons    (Basic "Z") 
          (setDomName  "Z"   trivialDomain
    ))))

  commutative  _ =  Yes
  cyclicMul    _ =  No 
  groupMul     _ =  No                   

  mul  =  (*)

  unity   _ =  1 
  unity_l _ =  [1] 

  inv_l  n  | (abs n)==1 =  [n]
            | otherwise  =  []

  divide_l   x y |  (mod x y)==0 =  [div x y]
                 |  otherwise    =  []

  power_l 0 0 =  error "power 0 0"
  power_l _ 0 =  [1]
  power_l 1 _ =  [1]
  power_l x n =  if  n>0  then  [x^n]  else  []



                      -- The below method for  rootN  is too slow 
                      -- - for the small numbers

  rootN  _    n 1  =  [n]
  rootN  mode n d  =  case  ((mode=="")||(mode=="int"), d<1)  of  

    (_    , True) ->  error "rootN for degree < 1 "

    (False, _   ) ->  
                error "rootN:  mode should be  \"\"  or  \"int\" "
    _             ->
      if  (n==0)||(n==1)  then  [n]
      else
        (case (n<0, even d)  of

          (True , True ) -> []
          (True , False) -> 
              if  mode==""  then
                           (case  rootN "" (-n) d  of [] -> []
                                                      [r]-> [(-r)]
                           )
              else
                let  [r] = rootN "int" (-n) d   
                in          if (r^d)==(-n) then [-r] else [(-r)-1]

          _              ->        -- find approximation for root
                                   -- in fractions
            let
              rtUn =  (fromInteger 1)::Rational
              rtN  =  (fromInteger n)::Rational
              f x  =  ((power x d)-rtN) :: Rational
              rr   =  contigFnRootAppr  f rtUn rtN (1:%2)
              r0   =  floor rr
              n0   =  r0^d
            in 
              (case  (compare n0 n, mode, (fromInteger r0)==rr)  of 

                                      -- TRY to write this shorter
                                      -- *****************
                (EQ, _    , _   ) -> [r0] 
                (GT, "int", _   ) -> [r0-1]
                (GT, _    , _   ) -> []
                (_ , "int", True) -> [r0]
                (_ , ""   , True) -> []
                _                 -> 
                  (case  (compare ((r0+1)^d) n, mode)  
                   of                            (EQ, _ )-> [r0+1]
                                                 (_ , "")-> []
                                                 (LT, _ )-> [r0+1]
                                                 _       -> [r0]
                  )
              )
        )
------------------------------------------------------------------


instance  OrdAddMonoid Integer   
instance  OrdAddGroup  Integer      
instance  MulMonoid    Integer      




--------------------------  Ring  --------------------------------


instance  Ring Integer   where

  ringTerm _ =  
    (setDomFuncs  (funcNames "ring")
      (setDomProps 
         --(completeRingProps  "commutative"
              [("euc",Yes),("fld",No),("factT",Yes),("minD",Yes)]
         --) 
        (setDomCons  (Basic "Z")  (setDomName "Z" trivialDomain)
    )))

  euclidean        _ =  Yes 
  factorizeIsTotal _ =  Yes 
  minNormRemValid  _ =  Yes
  field            _ =  No

  char    _   =  [0]
  i       _ n =  n
  i_l     _ n =  [n]  



instance  CommutativeRing Integer  


------------------------------------------------------------------
instance  SyzygySolvableRing Integer   where

  canAssoc x  | x<0       = (-x)
              | otherwise = x

  canInv   x  |  x<0      = (-1)
              | otherwise = 1

  gcD []     =  error "gcD []"
  gcD [x]    =  x
  gcD (x:xs) =  gcd x (gcD xs)

  eucNorm 0 = error "eucNorm 0"
  eucNorm n = abs n

              -- for  mode == ""  (divRem Integer)  is the canonic
              -- division with the  Non-negative remainder  r.
              -- "m"  requires the minimal-norm  r.

  divRem  _    _ 0 =  error "divRem _ _ 0"
  divRem  _    0 y =  [0,0]
  divRem  mode x y =  
    let  
       q = div x y
       r = mod x y              -- sign r == sign y
    in
      if   r==0  then  [q,r] 
      else
        case  (mode, r>0)  of              
          ("" , True ) ->  [q,r]
          ("" , False) ->  [q+1,r-y]
          ("m", True ) ->  if (y-r)<r then  [q+1,r-y]  else  [q,r]
          ("m", False) ->  
                     if  (r-y)>=(-r)  then  [q+1,r-y]  else  [q,r]
          _            ->  
            error( 
             ((w "divRem ").(w mode).(' ':).(w x).(' ':).(w y)) ""
                 )



  factorize 0 =  error "factorize 0"
  factorize 1 =  [] 
  factorize n = 
    if  n<0  then  factorize (-n)
    else           fact  n primes []   
      where
      fact  1 _      facts =  facts
      fact  n (p:ps) facts =  case  (multiplicity p n)  
                              of
                                  (0,q) -> fact q ps facts
                                  (m,q) -> fact q ps ((p,m):facts)
      


  syzygyBasis  modeString xs = 
           error  "No  syzygyBasis  for long Integer bases so far"


  --moduloBasis :: String -> [a] -> a -> (a, [a])

  moduloBasis _ []      y =  ( y, [] )
  moduloBasis _ [x]     y =  let  [q,r]= divRem "" y x  in (r,[q])
  moduloBasis _ [x1,x2] y =  let 
                               (g,u1,u2) = eucGCDE x1 x2
                               [q,r]     = divRem "" y g
                             in                 ( r, [q*u1,q*u2] )     
  moduloBasis _ [xs]    y =  
           error  "No  moduloBasis  for long Integer bases so far"


  --grBasis :: String -> [a] -> ([a], Matrix a)

  grBasis _ []    =  ( [] , Mt []    )
  grBasis _ [x]   =  ( [x], Mt [[1]] )
  grBasis _ [x,y] =  let  (g,u1,u2) = eucGCDE x y
                     in                      ( [g], Mt [[u1,u2]] )
  grBasis _ xs    =    
               error  "No  grBasis  for long Integer bases so far"

------------------------------------------------------------------


instance  Fractional Integer   where

  (/)                 =  divide         -- they yeild (error..) if
  fromRational (n:%d) =  n/d            -- d  does not divide  n








------------------------------------------------------------------


-- ModOverInt   sets canonically a module over Integer in 
--              correspondence to each additive group.


data   ModOverInt a =  MOI a Integer   deriving(Eq,Text)



instance  Set a =>  Set (ModOverInt a)
  where
  card  (MOI x _) =  card x

  setTerm  (MOI x _) = 
    (setDomFuncs 
      (funcNames "set") 
      (setDomCons   (ModOverIntC (setTerm x))  trivialDomain
    ) )
  w (MOI x _) =  w x


instance  AddGroup a =>  AddSemigroup (ModOverInt a)
  where
                                  -- direct sum:  a + Integer
  addSmgTerm (MOI x _) =  

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+", cyclicAdd x),  ("gr+", Yes), 
           ("ord+", Unknown)
         ]
         (setDomCons  (ModOverIntC (addSmgTerm x))  trivialDomain
    ) )  )

  groupAdd  _         =  Yes
  cyclicAdd (MOI x _) =  cyclicAdd x
  ordAdd    (MOI x _) =  Unknown       

  add     (MOI x n) (MOI y m) =  MOI (add x y) (n+m)
  zero_l  (MOI x n)           =  [ MOI (zero x)    0     ]
  neg_l   (MOI x n)           =  [ MOI (neg x)     (-n)  ]
  sub_l   (MOI x n) (MOI y m) =  [ MOI (sub x y)   (n-m) ]
  times_l (MOI x n) m         =  [ MOI (times x m) (n*m) ]


instance  AddGroup a =>  AddMonoid (ModOverInt a)  
instance  AddGroup a =>  AddGroup  (ModOverInt a)  


instance  AddGroup a =>  MulSemigroup (ModOverInt a)   where

                -- direct sum:  a' + Integer   
                -- where  a' is supplied with zero multiplication

  mulSmgTerm (MOI x n) =  

    (setDomFuncs  (funcNames "mulSmg")  
      (setDomProps
         [ ("cyc*", No), ("comm", Yes), ("gr*", No),
           ("ord*", Unknown)
         ]
         (setDomCons  (ModOverIntC (addSmgTerm x))  trivialDomain)
    ) )

  mul (MOI x n) (MOI _ m) =  MOI (zero x) (n*m)

  unity_l _ =  []
  inv_l   _ =  []

  divide_l  (MOI x n) (MOI _ m) =  
    let  zr = zero x  
    in        
      case  (x==zr, divide_l n m)  of  (False, _  ) -> []
                                       (_    , [] ) -> []
                                       (_    , [k]) -> [MOI zr k]

  power_l  (MOI x n) m =  [ MOI (zero x) (n^m) ]





instance  AddGroup a =>  Ring (ModOverInt a)    where
                  
                                 -- Direct Sum   a' + Integer,
                                 -- very similar to  0 + Integer
  ringTerm (MOI x n) = 

    (setDomFuncs      (funcNames "ring")
      (setDomProps    []
         (setDomCons (ModOverIntC (addSmgTerm x)) trivialDomain)
    ) )



instance  AddGroup a => CommutativeRing (ModOverInt a)

instance  AddGroup a => Num (ModOverInt a)   where  (+)    = add
                                                    (-)    = sub
                                                    negate = neg
                                                    (*)    = mul
------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




module  PreludePair   
  (
    Set(..),Num(..),AddSemigroup(..),AddMonoid(..),AddGroup(..),
    MulSemigroup(..),MulMonoid(..),MulGroup(..),
    Ring(..),CommutativeRing(..)
  )
where

import  PreludeInteger
import  PreludeList
import  Categ
import  Categ1
import  Matrix
import  IParse





lsCartP  [x] [y] =  [ (x,y) ]     
lsCartP  _   _   =  []





--------------------------  Set  ---------------------------------


instance  (Set a, Set b) =>  Set (a,b)    where  

  setTerm (x,y) = 
      (setDomFuncs    (funcNames "set")  
         (setDomCons  (Pair (setTerm x) (setTerm y)) trivialDomain
      )) 

  card (x,y) =  case (card x,card y) of  ([[n]], [[m]]) -> [[n*m]]
                                         ([[]] , _    ) -> [[]]
                                         (_    , [[]] ) -> [[]]
                                         _              -> []

  w (x,y)   =  ('(':).(w x).(',':).(w y).(')':)


  fromExpr (x,y) (E (L ",") [e1] [e2]) =  
         case  
           (fromExpr x e1, fromExpr y e2)  
         of
           ( ([x'],"" ), ([y'],"" ) ) -> ( [(x',y')], "" )
           ( ([x'],"" ), (_   ,msg) ) -> 
                        ( [], "fromExpr:  second of pair: "++msg )
           ( (_   ,msg), _          ) -> 
                        ( [], "fromExpr:  first of pair: " ++msg )

  fromExpr _     _                     =  
              ( [], "fromExpr:  (expr1,expr2) expected on input" )





instance  (Num a, Num b) => Num (a,b)   where

  fromInteger n   = (fromInteger n, fromInteger n)
  (x1,x2)+(y1,y2) = (x1+y1, x2+y2)
  (x1,x2)-(y1,y2) = (x1-y1, x2-y2)
  negate (x1,x2)  = (negate x1, negate x2)
  (x1,x2)*(y1,y2) = (x1*y1, x2*y2)

  --(x1,x2)/(y1,y2) = (x1/y1, x2/y2)






-------------------------  Semigroup  ----------------------------
                     

                   
instance  (AddSemigroup a, AddSemigroup b) =>  
                                        AddSemigroup (a,b)   where


  addSmgTerm (x,y) =  

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+", cyclicAdd (x,y)),
           ("gr+",  and3 (groupAdd x) (groupAdd y)),
           ("ord+", Unknown)
         ]
         (setDomCons  (Pair (addSmgTerm x) (addSmgTerm y)) 
                      trivialDomain
    ) )  )



  cyclicAdd (x,y) =  case (cyclicAdd x, cyclicAdd y) of
      (No     , _      ) -> No
      (_      , No     ) -> No
      (Unknown, _      ) -> Unknown
      (_      , Unknown) -> Unknown
      (Yes    , Yes    ) -> 
                    Unknown    --  (case  (card x, card y)  of ...  

  groupAdd (x,y) =  and3 (groupAdd x) (groupAdd y) 

  ordAdd   _     =  Unknown


  add (x,y) (x1,y1) =  (add x x1, add y y1)

  zero_l  (x,y)           = lsCartP  (zero_l x)    (zero_l y) 
  neg_l   (x,y)           = lsCartP  (neg_l  x)    (neg_l  y)  
  sub_l   (x1,y1) (x2,y2) = lsCartP  (sub_l x1 x2) (sub_l y1 y2)  
  times_l (x,y)   n       = lsCartP  (times_l x n) (times_l y n)




instance  (AddMonoid a, AddMonoid b) =>  AddMonoid (a,b)

instance  (AddGroup a,  AddGroup  b) =>  AddGroup (a,b)

------------------------------------------------------------------



instance  (MulSemigroup a, MulSemigroup b) =>  
                                        MulSemigroup (a,b)   where

  mulSmgTerm (x,y) =  

    (setDomFuncs  (funcNames "mulSmg")  
      (setDomProps
         [ ("cyc*", cyclicMul (x,y)),
           ("comm", and3 (commutative x) (commutative y) ),
           ("gr*",  and3 (groupMul x) (groupMul y)),
           ("ord+", Unknown)
         ]
         (setDomCons  (Pair (mulSmgTerm x) (mulSmgTerm y)) 
                      trivialDomain
    ) )  )


  commutative (x,y) =  and3 (commutative x) (commutative y)

  cyclicMul (x,y) =  case  (cyclicMul x, cyclicMul y)  of
                                     (No     , _      ) -> No
                                     (_      , No     ) -> No
                                     (Unknown, _      ) -> Unknown
                                     (_      , Unknown) -> Unknown
                                     (Yes    , Yes    ) -> Unknown 
                                 -- case (card x, card y) of ...  

  groupMul (x,y) =  and3 (groupMul x) (groupMul y) 


  mul (x,y) (x1,y1) = (mul x x1, mul y y1)

  unity   (x,y) =  (unity x, unity y)
  unity_l (x,y) =  lsCartP (unity_l x) (unity_l y)

  inv_l  (x,y) =  lsCartP (inv_l x) (inv_l y)  

  divide_l (x1,y1) (x2,y2) =  
                       lsCartP  (divide_l x1 x2)  (divide_l y1 y2) 

  power_l (x,y) n =  lsCartP  (power_l x n) (power_l y n) 




instance  (MulMonoid a, MulMonoid b) =>  MulMonoid (a,b)

instance  (MulGroup a,  MulGroup  b) =>  MulGroup (a,b)  







--------------------------  Ring  --------------------------------



instance  (Ring a, Ring b) =>  Ring (a,b)       where


  ringTerm (x,y) =  

    (setDomFuncs     (funcNames "ring")
      (setDomProps  (cartP_ring_props (ringTerm x) (ringTerm y))
        (setDomCons  (Pair (ringTerm x) (ringTerm y))
                     trivialDomain
    ) ) )
      where
      cartP_ring_props xT yT = ctpP  (domProps xT) (domCons yT)
        where
        ctpP  aProps bProps =  []
                                   --  cartP_ring_axioms ...


  hasZeroDiv      _     =  Yes
  hasNilp         (x,y) =  and3 (hasNilp x)     (hasNilp y)
  princIdeals     (x,y) =  and3 (princIdeals x) (princIdeals y) 
  syzygySolvable  (x,y) = 
                      and3 (syzygySolvable x)  (syzygySolvable y)
  moduloIsCanonic (x,y) = 
                      and3 (moduloIsCanonic x) (moduloIsCanonic y)
  field            _ = No
  euclidean        _ = No
                      -- in  "categ"  field => euclidean   is set,
                      -- but  (not euclidean)=> not field  is not
  factorial        _ = No 
  factorizeIsTotal _ = No
  minNormRemValid  _ = No
  hasGrBas         _ = No


  i_l     (x,y) n =  lsCartP  (i_l  x n ) (i_l   y n) 

  char (x,y) =  case (char x, char y) of  ([] , _  ) -> []
                                          (_  , [] ) -> []
                                          ([n], [m]) -> [m*n] -- ?



instance  (CommutativeRing a, CommutativeRing b) =>
                                             CommutativeRing (a,b)

------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





-- Residues Modulo 2.
--
-- This field is done specially - just for a change.





module  Res_z2   where


import  Categ
import  Categ1
import  Matrix
import  IParse



data  ResZ2 =  Z20 | Z21     deriving(Eq,Text)



instance  Set ResZ2    where

  setTerm _ =  (setDomFuncs      [ "w", "card" ] 
                 (setDomCons     (Basic "ResZ2")
                    (setDomName  "ResZ2"   trivialDomain 
               )))
  card _ = [[2]]

  w Z20 =  ('0':)
  w Z21 =  ('1':)

  fromExpr _ (L "0") =  ( [Z20], "" )
  fromExpr _ (L "1") =  ( [Z21], "" )
  fromExpr _ e       =  ( [], "ResZ2 input is \"0\" or \"1\" " )

                          



instance  AddSemigroup ResZ2     where 

  addSmgTerm x = 
         (setDomFuncs  
             ["+","0","0L","neg","negL","-","-l", "tim","timL"]
             (setDomProps  [("cyc+",Yes),("gr+",Yes),("ord+",No)] 
                           (setTerm x) 
         )   )

  cyclicAdd _ = Yes 
  groupAdd  _ = Yes
  ordAdd    _ = No

  add  Z20 x   = x
  add  x   Z20 = x
  add  _   _   = Z20

  zero    _   =  Z20
  zero_l  _   =  [Z20]
  neg         =  id
  neg_l   x   =  [neg x]

  times Z20 _ =  Z20
  times _   n =  if  even n  then Z20  else Z21

  times_l x n =  [times x n]



instance  AddMonoid ResZ2 
instance  AddGroup  ResZ2  



instance  MulSemigroup ResZ2     where 

  mulSmgTerm x = 
          (setDomFuncs   [ "*", "1L", "invL", "dvL", "^L" ]
            (setDomProps  [("comm",Yes),("cyc*",No),("gr*",No)] 
                          (setTerm x)
          ) )
  commutative  _ =  Yes
  cyclicMul    _ =  No 
  groupMul     _ =  No                   

  mul  Z20 _   = Z20
  mul  _   Z20 = Z20
  mul  _   _   = Z21

  unity   _ =  Z21 
  unity_l _ =  [Z21] 

  inv_l  Z21 =  [Z21]
  inv_l  _   =  []

  divide  x Z20 =  error "divide _ Z20"
  divide  x Z21 =  x

  divide_l  _ Z20 =  []
  divide_l  x Z21 =  [x]

  power_l Z20 0 =  error "power Z20 0"
  power_l x   _ =  [x]




instance  Ring ResZ2   where

  ringTerm x =  
    (setDomFuncs  [  {- "*", "1L", "invL", "dvL", "^L" -}  ]
      (setDomProps 
           -- (completeRingProps "commutative"  [("fld",Yes)] )

        [("euc",Yes),("fld",Yes),("factT",Yes),("fact",Yes),
         ("minD",Yes)
        ]
        
        (setTerm x)
    ) )

  field _ =  Yes

  char    _   =  [2]
  i       _ n =  if even n then Z20 else Z21
  i_l     x n =  [i x n]  



instance  CommutativeRing ResZ2  



instance  SyzygySolvableRing ResZ2   where

  canAssoc = id 

  canInv _ = Z21

  gcD [] =  error "gcD []  in ResZ2"
  gcD _  =  Z21

  factorize x = [(x,1)]      


  eucNorm Z20 =  error "eucNorm Z20"
  eucNorm _   =  0

  divRem  _  _   Z20 =  error "divRem _ _ Z20"
  divRem  _  Z20 _   =  [Z20,Z20]
  divRem  _  _   _   =  [Z21,Z20]

  syzygyBasis  modeString xs = 
                       error  "No  syzygyBasis for  ResZ2  so far"


  --moduloBasis :: String -> [a] -> a -> (a, [a])

  moduloBasis _ []       y =  ( y, [] )
  moduloBasis _ (Z20:xs) y = 
                  let  (r,q) = moduloBasis "" xs y  in  (r, Z20:q)
  moduloBasis _ (x  :xs) y =
                      ( Z20,  (divide y x):(map (const Z20) xs)  )


  --grBasis :: String -> [a] -> ([a], Matrix a)

  grBasis  _ []  =  ( [] , Mt []        )
  grBasis  _ [x] =  ( [x], Mt [[inv x]] )
  grBasis  _ _   =    
                 error  "No  grBasis  for long ResZ2 bases so far"


instance  Num ResZ2  where   (+)         = add
                             (-)         = sub
                             negate      = neg
                             (*)         = mul
                             fromInteger = i Z21
 
instance  Fractional ResZ2  where   

  (/)                 =  divide
  fromRational (n:%d) =  (fromInteger n)/(fromInteger d)




------------------------------------------------------------------
-- instance  ModuleOver ResZ2 Integer  where  

--  cMul n Z20 = Z20
--  cMul n _   = i Z21 n

;
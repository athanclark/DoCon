------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Operations on the Power Products




module  PP  where

import  PreludeInteger
import  PreludeList
import  Categ
import  Categ1
import  Matrix
import  IParse





        -- Power Product  is a list of non-negative integers --
        -- terminating with non-zero (if not empty)          --


type  PPComp =  PowPr -> PowPr -> Comp    
                          -- and  PowPr=[Integer], Comp=LT|GT|EQ

data  PP     =  PP PowPr PPComp

      -- Thus  PP is PowPr supplied with the Comparison function.


ppP ::  PP        ->  PowPr
ppP     (PP p _ ) =   p

ppCp :: PP        ->  PPComp 
ppCp    (PP _ cp) =   cp


------------------------------------------------------------------





addL :: AddMonoid a =>  [a] -> [a] -> [a]
                               -- add lists cancelling last zeroes
addL []     ys     =  ys      
addL xs     []     =  xs
addL (x:xs) (y:ys) =  
            let  z  = add x y  
                 zs = addL xs ys
            in  if  (z==(zero z))&&(null zs)  then  []  else  z:zs



ppLcm :: Ord a => [a] -> [a] -> [a]
                       -- Least Common Multiple  of power products
ppLcm []     ys     = ys
ppLcm xs     []     = xs
ppLcm (x:xs) (y:ys) = (max x y):(ppLcm xs ys)


ppCompl :: (AddGroup a, Num a, Ord a) =>  [a] -> [a] -> [a]
                                             -- p q -> (lcm p q)-p
ppCompl []     ys =  ys
ppCompl (x:xs) ys =  cpl (zero x) (x:xs) ys   
  where
  cpl _  []     ys     =  ys
  cpl _  xs     []     =  []
  cpl zr (x:xs) (y:ys) =  let  m = (max x y)-x
                          in  case  (m==zr, cpl zr xs ys) 
                              of                  (True,[])-> []
                                                  (_   ,zs)-> m:zs


ppMutPrime :: AddMonoid a =>  [a] -> [a] -> Bool
                            -- "Power Products are Mutually Prime" 
ppMutPrime []     _  =  True
ppMutPrime (x:xs) ys =  mp  (zero x) (x:xs) ys   
  where
  mp _  []     _      =  True
  mp _  _      []     =  True
  mp zr (x:xs) (y:ys) =  
                   if  x==zr||y==zr  then  mp zr xs ys  else False



ppDivides :: PowPr -> PowPr -> Bool 
ppDivides    p        q     =  all (>=0) (sub q p)






------  SOME USABLE COMPARISONS for the power products  ----------


lexComp, revLex, degLex, degRevLex ::  PowPr -> PowPr -> Comp

lexComp  (n:p) (m:q) =  if  n<m  then LT  else 
                                 if n>m then GT  else  lexComp p q
lexComp  []    []    =  EQ
lexComp  []    _     =  LT
lexComp  _     _     =  GT


degLex    ns ms =  case  compare (sum ns) (sum ms)  of
                                              EQ  -> lexComp ns ms
                                              res -> res

degRevLex ns ms =  case  compare (sum ns) (sum ms)  of
                                               EQ  -> revLex ns ms
                                               res -> res

revLex  ns ms =  rl ns ms EQ
  where
  rl []     []     res  =  res
  rl []     _      _    =  LT 
  rl _      []     _    =  GT
  rl (n:ns) (m:ms) res  =  rl ns ms r  
                             where  r =  case  compare n m  
                                         of            EQ  -> res
                                                       res1-> res1






--------------------  PP  Ordered Group  -------------------------


    ------------------------------------------------------------
    -- For the  Ordering  on  PP,   we presume  essentially  the 

    -- operand PP-s  (PP p comp)  have the SAME  comp  function.

    -- This is needed to agree  `compare'  with the natural set-
    -- ting for  (==)  - see below.
    ------------------------------------------------------------



instance  Eq  PP      where    (PP p _)==(PP q _) =  p==q

instance  Set PP      where    w    (PP p _) =  w p

                               --fromExpr p    =  ?

                               card _        =  [[]]

instance  AddSemigroup PP   where   
  groupAdd  _ = Yes
  cyclicAdd _ = No
  ordAdd    _ = Yes
  add     (PP p cp) (PP q _) =  PP (addL p q) cp
  zero_l  (PP _ cp)          =  [ PP [] cp ]
  neg_l   (PP p cp)          =  [ PP (neg p) cp ]
  sub_l   (PP p cp) (PP q _) =  [ PP (addL p (neg q)) cp ]
  times_l (PP p cp) n        =  [ PP (map (\x-> times x n) p) cp ]

  compare (PP p cp) (PP q _) =  cp p q       -- <---


instance  AddMonoid    PP
instance  AddGroup     PP 
instance  OrdAddMonoid PP 
instance  OrdAddGroup  PP      

instance  Ord PP       where    p <= q = (compare p q)/=LT
                                p <  q = (compare p q)==LT

instance  Text PP  
instance  Num  PP     where     (+)    = add
                                (-)    = sub
                                negate = neg
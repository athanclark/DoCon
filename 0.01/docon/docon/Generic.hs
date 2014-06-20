------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Some general purpose functions




module  Generic  where 

import  PreludeList
import  Categ
import  Categ1
import  Matrix  --?
import  IParse 
import  ParOpTab 



copy :: Integer -> a -> [a]     -- *** try to find the replacement
                                -- *** for this in Prelude

copy    n x =  take n xs  where  xs = x:xs


-- remove the element No n  from a list  -------------------------

del_n_th :: Integer -> [a] -> [a]     -- **** to be optimized ****

del_n_th  _ []     = []
del_n_th  0 xs     = xs
del_n_th  1 (x:xs) = xs
del_n_th  n (x:xs) = x : (del_n_th (n-1) xs)


-- merge lists ordered by the predicate  p  ----------------------

mergeP  _ []     ys     =  ys
mergeP  _ xs     []     =  xs
mergeP  p (x:xs) (y:ys) =  if (p x y) then  x:(mergeP p xs (y:ys))
                           else             y:(mergeP p (x:xs) ys)

-- sort list w.r.to predicate  p  --------------------------------

sortP  p xs =  s (map (\x->[x]) xs)
  where
  s []        =  []
  s [segment] =  segment
  s segments  =  s  (mrPairs segments)
    where 
    mrPairs (sg1:sg2:sgs) =  (mergeP p sg1 sg2):(mrPairs sgs)
    mrPairs sgs           =  sgs
------------------------------------------------------------------

genSum, genProduct ::  Num a =>  [a] -> a

genSum (x:xs) = foldl (+) x xs
genSum []     = error "genSum []"

genProduct (x:xs) = foldl (*) x xs
genProduct []     = error "genProduct []"


------------------  general reading function  --------------------

r ::  Set a =>  a -> String -> a
                           -- Makes use  of  infixParse, fromExpr.
                           -- See  infixParse  in      IParse.hs,
                           --      fromExpr    in the  Set class.

r  sample s =  case  infixParse parenTable opTable (lexLots s)  of 

    ([e], "" ) -> 
      (case  fromExpr sample e  of
        ([x],"" ) -> x
        (_  ,msg) -> 
          error( (w "fromExpr: bad string for the given sample.")
                 $(w " sample =  ")$(w sample)$('\n':)$(w msg)$ ""
               )
      )
    (es , msg) -> error ("infixParse:  " ++ msg)
------------------------------------------------------------------





{-
RESERVE

           --  Finding  minimum-s   using the comparison predicate
           --  (p x y)==True  iff  x < y

minP ::  (a -> a -> Bool) -> a -> a -> a        -- minimum of two
minP  p x y =  if  p x y  then x  else y

minimumP p =  foldl1 (minP p)                 -- minimum of list



minPAhead ::  (a -> a -> Bool) -> [a] -> [a]
           -- p                   xs     ys

                  -- Move the minimal of  xs  to the head.
                  -- ys differs from xs only in one transposition.
minPAhead _ []       =  []
minPAhead _ [x]      =  [x]
minPAhead p (x:y:xs) = 
            if  not (p x y)  then   
                        let  (y1:xs') = minPAhead p (y:xs)
                        in                                y1:x:xs'
            else        let  (x1:xs') = minPAhead p (x:xs)
                        in                                x1:y:xs'

-}




----------------- TAKEN FROM  Gofer  examples.gs -----------------

primes = map head (iterate sieve [2..])  :: [Integer]

sieve (p:xs) = [ x | x<-xs, x `rem` p /= 0 ]
------------------------------------------------------------------


------------------------------------------------------------------
firstIntDivisor n =  
  if  (abs n) < 2  then  error ("firstIntDivisor "++(show n))
  else
    d  n 2 (mod n 2)  where   d  _ m 0 =  m
                              d  n m _ =  d  n (m+1) (mod n (m+1))


isPrimeInt n = if  n<2  then  error ("isPrimeInt "++(show n))
               else           n==(firstIntDivisor n)
------------------------------------------------------------------

gcdL :: SyzygySolvableRing a =>  (a -> a -> a) -> [a] -> a

                                  -- gcd  for list via gcd for two
gcdL _ []     = error "gcdL []"
gcdL g (x:xs) = gc x xs    where  gc  res []     = res
                                  gc  res (x:xs) = gc (g res x) xs



eucGCDE :: (SyzygySolvableRing a, Num a) =>  a -> a -> (a, a, a)
                                          -- x    y     g  u  v  
                      
eucGCDE  x y =                             --  g = GCD = u*x+v*y
  let  zr = zero  x
       un = unity x
  in
    gc  zr  (un,zr,x)  (zr,un,y)      
           -- u1 u2 u3   v1 v2 v3                    
             -- Euclidean GCD is applied to  u3,v3,  operations on
             -- u1,u2, v1,v2  are parallel to ones of  u3,v3              
      where
      gc  zr (u1,u2,u3) (v1,v2,v3) = 
        if  v3==zr  then  (u3,u1,u2)
        else
          let  [q,r] = divRem "" u3 v3
          in               gc  zr (v1,v2,v3) (u1-q*v1, u2-q*v2, r)
------------------------------------------------------------------

multiplicity :: 
           (SyzygySolvableRing r, Num r) =>  r -> r -> (Integer,r)
                                          -- x    y     m       q

          --  Multiplicity of  x  in  y  for Euclidean ring 
          --  q = y/(x^m),    x,y  non-zero,  x  is Not invertible

multiplicity  x y =  case  divide_l y x  of
  [] -> (0,y)
  [q]-> if  (eucNorm q)>=(eucNorm y)  then  
         error( 
               ((shows "multiplicity ").(' ':).
                 (shows x).(' ':).(shows y))  " Invertible Divisor"
              )
        else     mt  x y 0   
          where
          mt  x y m =  case  divide_l y x  of  []  -> (m,y)
                                               [q] -> mt x q (m+1)
------------------------------------------------------------------

contigFnRootAppr :: (Field k, OrdAddGroup k, Fractional k) =>
                    (k -> k) -> k -> k -> k  ->  k
                 -- f           l    r    prec


        --  Approximation for the  Root of Continuous Function  f 
        --  on the segment  [l,r],   (f l) <= zero <= (f r),   in
        --  the  Ordered Real field  (compare,<,<=)  with the Ab-
        --  solute value  absV.
        --  absV(result,root) <= prec
        --  `real' means -1 is not a sum of squares.

        --  Bisection method. 

        --  absV   should satisfy  ? 

        --  Root itself belongs to the  ?  (completion of k ?)


contigFnRootAppr  f l r prec =

  if  (field prec/=Yes)||(hasAbs prec/=Yes)||(real prec/=Yes)
      then 
        error "contigFnRootAppr: Required: field,hasAsb,real==Yes"
  else
    let
      zr = zero prec
      fl = f l
      fr = f r
    in
      case  (compare l r, compare fl zr, compare fr zr)   
      of
        (EQ,EQ,_ ) ->  l
        (_ ,EQ,_ ) ->  l
        (_ ,_ ,EQ) ->  r
        (EQ,_ ,_ ) ->  error "contigFnRootAppr:  l==r,(f l)/=zero"
        (GT,_ ,_ ) ->  error "contigFnRootAppr:  l > r "
        (_ ,GT,_ ) -> 
            error "contigFnRootAppr: (f l)<=zero<=(f r)  required"
        (_ ,_ ,LT) ->  
            error "contigFnRootAppr: (f l)<=zero<=(f r)  required"
        _          ->
                     (bisect l r)   where

          bisect  l r =  
            let
              mid  = (l+r)/(i prec 2)
              fmid = f mid
            in
              case (compare fmid zr, compare (absV (r-l)) prec) of
                (EQ,_ ) -> mid
                (GT,GT) -> bisect l   mid
                (LT,GT) -> bisect mid r  
                _       -> mid



-----------------------  GCD test  -------------------------------


gcd_test :: 
           (Num a, SyzygySolvableRing a) =>  a -> a -> a -> String
                                           --d    x1   y1
gcd_test d x1 y1 = 
  let
    zr = zero  d
    un = unity d
  in
    if  x1==zr || y1==zr || (canAssoc (gcD [x1,y1]))/=un   then  
       error 
        "(gcd_test d x1 y1):  x1,y1  should be mutually prime\n\n"
    else
      let     
        x   = d*x1 
        y   = d*y1
        d'  = gcD [x,y]
        ok  = if  (canAssoc d')==(canAssoc d)  then  
                              " (canAssoc d')==(canAssoc d) O.K. "
              else         "ERROR: (canAssoc d') /= (canAssoc d) "
      in

        "\n(gcd_test d x1 y1): "    ++
        "\n\n" ++
        "d  = "                     ++  (w d  "")  ++ 
        "\n\n" ++
        "x1 = "                     ++  (w x1 "")  ++ 
        "\n\n" ++
        "y1 = "                     ++  (w y1 "")  ++ 
        "\n\n" ++
        "d' = gcd [d*x1,d*y1] =  "  ++  (w d' "")  ++ 
        "\n\n" ++
        ok


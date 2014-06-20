--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module Common_  

  -- Part of DoCon Prelude.
  -- 
  -- All needed from here is  reexported by  DPrelude.


  (partitionN, eqListsAsSets, del_n_th, halve,  mulSign, invSign, 
   evenL, factorial, binomCoefs,  isOrderedBy,  mergeBy, mergeE, 
   sort, sortBy, sortE,  sum1, product1, alteredSum, 
   minPartial, maxPartial,  lexListComp
  )
where 

import List     (partition               )
import Prelude_ (Z, Comparison, CompValue)






--------------------------------------------------------------------
partitionN :: (a -> a -> Bool) -> [a] -> [[a]]
                -- break list into groups by Equivalence relation  p
partitionN _ []     = []
partitionN p (x:xs) = (x:ys):(partitionN p zs) where
                                        (ys,zs) = partition (p x) xs  

          -- but for the case of equivalent items being *neighbours* 
          --                                            use  groupBy
eqListsAsSets :: (Eq a) => [a] -> [a] -> Bool
eqListsAsSets              xs     ys  =
                          all (`elem` xs) ys  &&  all (`elem` ys) xs

{-# specialize eqListsAsSets :: [Z] -> [Z] -> Bool #-}


del_n_th :: Z -> [a] -> [a]    -- remove element No n  from list
del_n_th    _  []     = []
del_n_th    0  xs     = xs
del_n_th    1  (_:xs) = xs
del_n_th    n  (x:xs) = x:(del_n_th (n-1) xs)

halve :: [a] -> ([a],[a])
halve    xs  = h [] xs xs  where   
                           h ls (x:rs) (_:_:ys) = h (x:ls) rs ys
                           h ls rs     _        = (reverse ls, rs)

mulSign :: Char -> Char -> Char 
mulSign    x       y    =  if  x==y  then '+'  else '-'

invSign :: Char -> Char 
invSign    '+'  =  '-'
invSign    '-'  =  '+'

evenL :: [a] -> Char       
                   -- '+' ('-') means the list has even (odd) length
evenL []     = '+'
evenL (_:xs) = invSign $ evenL xs

factorial :: Z -> Z
factorial    0 = 1
factorial    n = 
  if 
     n < 0  then 
        error $ ("factorial "++) $ shows n ":   negative argument\n"
  else  product [1..n]  


binomCoefs :: Z -> [Z]
               -- binomial coefficients [C(n,k)..C(n,0)], k <= n/2+1
binomCoefs 0 = [1] 
binomCoefs 1 = [1]
binomCoefs n = 
  if  
    n < 0  then  
         error$ ("binomCoefs "++)$ shows n $ ": negative argument\n"
  else   bc n 2 [n,1]
  where
  bc n k (c:cs) = let  c' = quot (c*(n-k+1)) k
                  in
                  if  (2*k) <= n  then  bc n (k+1) (c':c:cs)
                  else
                    if  even n  then  c:cs  else  c':c:cs


isOrderedBy :: Comparison a -> [a] -> Bool

  -- "list is ordered".
  -- Examples:  isOrderedBy compare        [1,2,2] -> True,
  --            isOrderedBy (flip compare) [1,2,2] -> False

isOrderedBy cp xs = isO xs  
                    where  isO (x:y:xs) = (cp x y)/=GT && isO (y:xs)
                           isO _        = True

mergeBy :: Comparison a -> [a] -> [a] -> [a]
                                        -- merge lists ordered by cp 
mergeBy _  []     ys     = ys
mergeBy _  xs     []     = xs
mergeBy cp (x:xs) (y:ys) = case  cp x y  of 
                                      GT -> y:(mergeBy cp (x:xs) ys)
                                      _  -> x:(mergeBy cp xs (y:ys))

sortBy :: Comparison a -> [a] -> [a]

  -- Sort list by comparison cp.  
  -- Example:  sort compare        [2,1,3,1] = [1,1,2,3]
  --           sort (flip compare) [2,1,3,1] = [3,2,1,1]
  --
  -- This is the  merge  sorting:  O( n*log(n) )  cost.

sortBy cp xs = s $ mergePairs [[x] | x <- xs]
  where
  s []   = []
  s [xs] = xs
  s xss  = s $ mergePairs xss

  mergePairs (xs:ys:zss) = (mergeBy cp xs ys):(mergePairs zss)
  mergePairs xss         = xss


sort :: (Ord a) => [a] -> [a]
sort = sortBy compare


mergeE :: Comparison a -> [a] -> [a] -> ([a],Char)

  -- Extended merge: 
  -- the transposition sign '+' | '-' is also accumulated. 

mergeE cp xs ys = m xs ys $ evenL xs
  where
  m []     ys     _  = (ys,'+')
  m xs     []     _  = (xs,'+')
  m (x:xs) (y:ys) ev = case  cp x y  of

    GT -> (y:zs, mulSign s ev)  where  (zs,s) = m (x:xs) ys ev 
    _  -> (x:zs, s)         where  (zs,s) = m xs (y:ys) (invSign ev)
      

sortE :: Comparison a -> [a] -> ([a],Char)
                -- Extended sort:
                -- the permutation sign '+' | '-'  also accumulates.
                -- The cost is still  O( n*log(n) ).
sortE _  []  = ([] , '+')
sortE _  [x] = ([x], '+')
sortE cp xs  = let  (ys ,zs) = halve xs
                    (ys',s1) = sortE cp ys
                    (zs',s2) = sortE cp zs
                    (us ,s3) = mergeE cp ys' zs'
               in   (us, mulSign s3 $ mulSign s1 s2)
--------------------------------------------------------------------
sum1, product1, alteredSum :: (Num a) => [a] -> a

sum1 []     = error "sum1 []\n"
sum1 (x:xs) = sm xs x  where  sm []     s = s
                              sm (x:xs) s = sm xs (x+s)

product1 []     = error "product1 []\n"
product1 (x:xs) = pr xs x  where  pr []     p = p
                                  pr (x:xs) p = pr xs (x*p)

alteredSum [] = error "alteredSum []\n"   -- [x1..xn]-> x1-x2+x3-...
alteredSum xs = sum1 $ altNeg '+' xs
                            where
                            altNeg _   []     = []
                            altNeg '+' (x:xs) = x   :(altNeg '-' xs)
                            altNeg '-' (x:xs) = (-x):(altNeg '+' xs)

{-# specialize sum1       :: [Z] -> Z #-}
{-# specialize product1   :: [Z] -> Z #-}
{-# specialize alteredSum :: [Z] -> Z #-}
--------------------------------------------------------------------
lexListComp :: (a -> b -> CompValue) -> [a] -> [b] -> CompValue

  -- Compare the lists lexicographically according to the given 
  -- element comparison  cp.
  -- The lists may differ in type and length.

lexListComp cp = lcp
  where  
  lcp []     []     = EQ
  lcp []     _      = LT
  lcp _      []     = GT
  lcp (x:xs) (y:ys) = case  cp x y  of  EQ -> lcp xs ys
                                        v  -> v
                      
minPartial, maxPartial ::  
                 (Eq a) => (a->a->Maybe CompValue) -> [a] -> Maybe a

  -- Minimum by the Partial ordering.
  -- The result maybe 
  --            Just m   - for  m<-xs & m <= x  for all  x  from xs,
  --            Nothing  - if there is no such  x  in  xs.  

minPartial _  []       = Nothing
minPartial _  [x]      = Just x
minPartial cp (x:y:xs) = case  cp x y  of
  
  Just LT -> minPartial cp (x:xs)
  Just EQ -> minPartial cp (x:xs)
  Just GT -> minPartial cp (y:xs)
  _       -> case   minPartial cp xs  
             of
               Nothing -> Nothing
               Just m  -> case  (cp m x, cp m y)  of
                                       (Nothing, _      ) -> Nothing
                                       (_      , Nothing) -> Nothing
                                       (Just GT, _      ) -> Nothing
                                       (_      , Just GT) -> Nothing
                                       _                  -> Just m

maxPartial cp = minPartial (flip cp)

 ;







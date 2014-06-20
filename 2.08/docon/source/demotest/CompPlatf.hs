-- This is to measure the  relative performance  for various Haskell
-- platforms and implementations.
--
-- Choose  n,  run  test n  and compare the timings.
--
-- It consists mainly of merge sorting of a list of small integers.


module CompPlatf (test)
where 
-- main = putStr $ shows (test 55000) "\n"

test :: Int -> Int
test n = max' $ sort' $ zipWith (-) (reverse xs) xs
                                                  where  xs = [1..n]

max' :: Ord a => [a] -> a
max' [x]      = x
max' (x:y:xs) = case  compare x y  of  LT -> max' (y:xs)
                                       _  -> max' (x:xs)
sort' :: Ord a => [a] -> [a]
sort'             xs  =  s $ mergePairs [[x] | x <- xs]
  where
  s []   = []
  s [xs] = xs
  s xss  = s $ mergePairs xss

  mergePairs (xs:ys:zss) = (merge xs ys):(mergePairs zss)
  mergePairs xss         = xss

merge :: Ord a => [a] -> [a] -> [a]
merge             []     ys     = ys
merge             xs     []     = xs
merge             (x:xs) (y:ys) = case  compare x y  of
                                           GT -> y:(merge (x:xs) ys)
                                           _  -> x:(merge xs (y:ys))


{- statistics for  test 55000 

scico September 2001 ghc-5.02 -interpreted 
                                 time (under large heap) = 15.8 sec,
                                    minimal-needed(Heap) <= 200 Kb !
   (ghc-5.02 saves memory greatly
    and is a bit slower than 5.00.1
   )
 compiled with  -O 
  loaded and run from  -interactive  time = 4.0,  min(Heap) <= 200 Kb
                -Onot                       5.2 

 5.00.1: linked and run in batch mode   2.2,  5 Mb
         -Onot, run from  -interactive  3.8, 10 Mb


scico  August 1999  ghc-4.04 -Onot -M9m -H8m   3.5 sec
math   ...                                     1.9

scico  Hugs-98-February-2000      time      = 18.0 
                                  min(heap) = 400K cells  (3.2 Mb ?)

time(scico)/time(revolt) = 13.3 / 9.8 =~= 1.4
-}






























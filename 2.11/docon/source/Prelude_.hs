------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
------------------------------------------------------------------------
------------------------------------------------------------------------





module Prelude_   

  -- Initial part of the DoCon prelude.
  --
  -- All needed from here is  reexported by  DPrelude.

  (Cast(..), ct, ctr, 
   PropValue(..), InfUnn(..), MMaybe, CompValue, Comparison, 
   Z, Natural, toZ, fromZ, 
   tuple31, tuple32, tuple33,  tuple41, tuple42, tuple43, tuple44,
   tuple51, tuple52, tuple53, tuple54, tuple55,
   zipRem, allMaybes,  mapmap, fmapmap, mapfmap, fmapfmap,
   boolToPropV, propVToBool, not3, and3, or3,  compBy,  delBy, 
   separate, pairNeighbours, removeFromAssocList, 
   addToAssocList_C, addListToAssocList_C, propVOverList, 
   addListToMap, addListToMapWith,  updateProps, mbPropV, 
   lookupProp, addUnknowns,  takeAsMuch, dropAsMuch,
   antiComp,  minBy, maxBy, minimum, maximum, minAhead, maxAhead
  ) 
where   
import qualified Data.Map as Map 
                               (Map(..), fromList, union, unionWith)

import Prelude hiding (maximum, minimum)



--------------------------------------------------------------------
type Z       = Integer    -- IGNORE Int !
type Natural = Integer    -- presumed:  >= 0

toZ :: (Integral a) => a -> Z
toZ =  toInteger
{-# specialize toZ :: Int -> Z,  Integer -> Z #-}

fromZ :: (Num a) => Z -> a
fromZ =  fromInteger
{-# specialize fromZ :: Z -> Int,  Z -> Integer #-}
--------------------------------------------------------------------
data InfUnn a = Fin a | Infinity | UnknownV  
                                   deriving(Eq, Show, Read)
  -- Example:
  -- setCardinality(sS) = osetCard sS  :: InfUnn Z  may yield 
  --   Fin n,    n Natural, or
  --   Infinity,            or
  --   UnknownV

instance Functor InfUnn  where  fmap f (Fin a)  = Fin (f a)
                                fmap _ Infinity = Infinity
                                fmap _ UnknownV = UnknownV

--------------------------------------------------------------------
class Cast a b where  cast :: Char -> a -> b -> a
                              --mode

  -- cast mode a b  means  cast  b  to domain of sample  `a'.
  --
  -- mode = 'r'        means the additional correction to perform,
  --        any other  means to project "as it is".
  --
  -- Examples.
  -- * Map coefficient c <- R to polynomial domain R[x1..xn]:
  --   cast mode pol c,
  --   mode = 'r'  means here the  check  c == zero  is needed,
  --   other mode  is usually set when  c  is known as non-zero.
  --
  -- * Projection  R -> R/I  to residue ring, 
  --   say, R = Z,  I = Ideal(g),  g > 1,  res <- R/I,  n <- R,  and
  --   cast mode res n   projects  n  to  R/I.
  --   mode = 'r'  
  --       takes first the remainder by g (g contained in res data),
  --   other mode  has sense when it is known that  0 <= n < g.

ct, ctr :: (Cast a b) => a -> b -> a
ct  = cast '_'
ctr = cast 'r'

tuple31 (x,_,_) = x       -- there comes the language extension
tuple32 (_,x,_) = x       -- where these tuple things will be done
tuple33 (_,_,x) = x       -- nicer
                          --
tuple41 (x,_,_,_) = x     --
tuple42 (_,x,_,_) = x
tuple43 (_,_,x,_) = x
tuple44 (_,_,_,x) = x

tuple51 (x,_,_,_,_) = x
tuple52 (_,x,_,_,_) = x
tuple53 (_,_,x,_,_) = x
tuple54 (_,_,_,x,_) = x
tuple55 (_,_,_,_,x) = x

type CompValue = Ordering           -- `Ordering' is from Haskell-98
                                    -- and it does not sound well
type Comparison a = a -> a -> CompValue

type MMaybe a = Maybe (Maybe a)

  -- Example of usage:
  -- subsmgUnity sS -> 
  --     Just (Just u)   means here the unity  u  is found in sS,
  --     Just Nothing    - sS does not contain unity,
  --     Nothing         - cannot determine whether such  u  exists.

data PropValue = Yes | No| Unknown  
                           deriving (Eq, Ord, Enum, Show, Read)
--------------------------------------------------------------------
not3 :: PropValue -> PropValue
not3    Yes       =  No
not3    No        =  Yes
not3    _         =  Unknown

and3, or3 :: PropValue -> PropValue -> PropValue

and3    Yes  Yes = Yes
and3    No   _   = No
and3    _    No  = No
and3    _    _   = Unknown

or3    Yes  _   = Yes
or3    _    Yes = Yes
or3    No   No  = No
or3    _    _   = Unknown

boolToPropV :: Bool -> PropValue
boolToPropV    b    =  if  b  then Yes  else No

propVToBool :: PropValue -> Bool 
propVToBool    Yes       =  True
propVToBool    _         =  False
--------------------------------------------------------------------
compBy :: Ord b => (a -> b) -> Comparison a
compBy f x y = compare (f x) (f y)          
  -- 
  -- Usable tool to define comparison. Examples:
  -- compBy snd         compares pairs by second component,
  -- compBy (abs .snd)  -      by absolute value of second component


-- BEGIN  **********************************************************
-- suggestion for Haskell library? 

mapmap :: (a -> b) -> [[a]] -> [[b]]
mapmap    f        =  map (map f)

fmapmap :: Functor c => (a -> b) -> c [a] -> c [b]
fmapmap                 f        =  fmap (map f)

mapfmap :: Functor c => (a -> b) -> [c a] -> [c b]
mapfmap                 f        =  map (fmap f)

fmapfmap :: (Functor c, Functor d) => (a -> b) -> c (d a) -> c (d b)
fmapfmap                              f        =  fmap (fmap f)

allMaybes :: [Maybe a] -> Maybe [a] 
                                 -- taken from (non-standard) Maybes
                                 -- of `misc' and somewhat optimized
allMaybes ms = a [] ms  where
                        a xs []           = Just $ reverse xs
                        a xs (Just x :ms) = a (x:xs) ms
                        a _  _            = Nothing


takeAsMuch, dropAsMuch  :: [a] -> [b] -> [b]

takeAsMuch (_: xs) (y: ys) =  y: (takeAsMuch xs ys)
takeAsMuch _       _       =  []

dropAsMuch xs ys =  case (xs, ys) of 
                                  ([],     _     ) -> ys
                                  (_,      []    ) -> []
                                  (_: xs', _: ys') -> dropAsMuch xs' ys'


zipRem :: [a] -> [b] -> ([(a,b)], [a], [b])

  -- zip preserving remainders. Example:
  -- for  xs = [1,2]  zipRem xs (xs++[3]) = ([(1,1),(2,2)], [], [3])

zipRem []     ys     = ([], [], ys)
zipRem xs     []     = ([], xs, [])
zipRem (x:xs) (y:ys) = ((x,y):ps, xs', ys')  
                                  where  (ps,xs',ys') = zipRem xs ys

delBy :: (a -> Bool) -> [a] -> [a]  
delBy _ []     = []        
delBy p (x:xs) = if  p x  then  xs  else  x:(delBy p xs)

separate :: (Eq a) => a -> [a] -> [[a]]
  --
  -- break list to lists separated by given separator
  -- Example:  ';' -> "ab;cd;;e f " -> ["ab", "cd", "", "e f "]
  --
separate _ [] = []
separate a xs = case  span (/= a) xs  of
                                    (ys, []  ) -> [ys]
                                    (ys, _:zs) -> ys:(separate a zs)

pairNeighbours :: [a] -> [(a,a)]
pairNeighbours (x:y:xs) = (x,y):(pairNeighbours xs)
pairNeighbours _        = []

removeFromAssocList :: Eq a => [(a, b)] -> a -> [(a, b)]

removeFromAssocList []              _  = []
removeFromAssocList ((x',y):pairs)  x  =  
              if 
                 x==x'  then  pairs
              else            (x', y): (removeFromAssocList pairs x)

addToAssocList_C :: 
             Eq a => (b -> b -> b) -> [(a, b)] -> a -> b -> [(a, b)]
                      -- c
              -- combines with the previous binding: when a key is
              -- in the list, it binds with  (c oldValue newValue)

addToAssocList_C c pairs key value = add pairs 
  where
  add []         = [(key, value)] 
  add ((k,v):ps) = if  k /= key then  (k,v)         : (add ps)
                   else               (k, c v value): ps  

addListToAssocList_C :: 
           Eq a => (b -> b -> b) -> [(a, b)] -> [(a, b)] -> [(a, b)]

addListToAssocList_C c ps binds = foldl addOne ps binds
                         where
                         addOne ps (k,v) = addToAssocList_C c ps k v

addListToMap :: Ord k => Map.Map k a -> [(k, a)] -> Map.Map k a
addListToMap             mp             pairs    =
                                   Map.union (Map.fromList pairs) mp

addListToMapWith :: 
    Ord k => (a -> a -> a) -> Map.Map k a -> [(k, a)] -> Map.Map k a
           -- old  new
addListToMapWith f mp pairs =
                             Map.unionWith f mp (Map.fromList pairs)

-- END *************************************************************



propVOverList :: 
      Eq a => [(a, PropValue)] -> a -> PropValue -> [(a, PropValue)]
                                            -- update property value
propVOverList ps _  Unknown = ps
propVOverList ps nm v       = pov ps
  where
  pov []            = [(nm, v)]
  pov ((nm1,v1):ps) = if  nm1 /= nm  then  (nm1, v1): (pov ps)
                      else                 (nm , v ): ps

updateProps :: 
    Eq a => [(a, PropValue)] -> [(a, PropValue)] -> [(a, PropValue)]

updateProps ps ps' = foldl update ps ps'
                           where
                           update ps (nm, v) = propVOverList ps nm v

mbPropV :: Maybe PropValue -> PropValue
mbPropV    (Just v)        =  v
mbPropV    _               =  Unknown

lookupProp :: Eq a => a -> [(a, PropValue)] -> PropValue
lookupProp            a =  mbPropV . lookup a

addUnknowns :: Eq a => [(a, PropValue)] -> [a] -> [(a, PropValue)]
addUnknowns props = foldl addOne props
  where
  addOne  []               nm = [(nm, Unknown)]
  addOne  ps@((nm',v):ps') nm = if  nm==nm'  then  ps
                                else       (nm', v): (addOne ps' nm)

antiComp :: CompValue -> CompValue
antiComp    LT        =  GT
antiComp    GT        =  LT
antiComp    _         =  EQ

minBy, maxBy :: Comparison a -> [a] -> a

  -- Minimum, maximum by the given comparison
  -- Example:   minBy compare        [2,1,3,1] = 1
  --            minBy (flip compare) [2,1,3,1] = 3

minBy _  [] = error "minBy <comparison> []\n"
minBy cp xs = m xs
                where  m [x]      = x
                       m (x:y:xs) = case  cp x y  of  GT -> m (y:xs)
                                                      _  -> m (x:xs)
maxBy cp = minBy (flip cp)

minimum, maximum :: Ord a => [a] -> a
minimum = minBy compare
maximum = minBy (flip compare)

minAhead, maxAhead :: Comparison a -> [a] -> [a]
  --
  -- put ahead the minimum (maximum)  by maybe transposing a single 
  -- pair of list elements
  --
minAhead cp xs = m: (ys++zs)  where 
                              (ys, m:zs) = span ((== LT) . cp m') xs  
                              m'         = minBy cp xs

maxAhead cp = minAhead (flip cp)


  



{- reserve **************************************************
Maybe, to join Cast, maybe, flip a b ... 
class Convertible a b  
  where  
  cvm :: a -> b -> Maybe b
  cv  :: a -> b -> b
  cv a b = fromMaybe (error "(cv a b) fail\n") (cvm a b)
-- cvm a b  tries to convert  a  to domain of  b.
--
-- b  is a *sample* for its domain.
-- DIFFERENCE from  Cast: 
--   cvm may return Nothing, it is more complex, may be expensive,
--   it is usually applied at the upper, "interface" level of the 
--   program, out of the nested cycles. 
-- Example:
-- for  f <- Z[x,y],  g <- Rational[x,y,z][u] = R,   cvm f g
-- has a chance to "extend and lift" f to R by adding denominators 1
-- and zero powers for z, u.

-- instance Convertible a a   where  cv a _ = a
instance Convertible Bool    Bool     where  cvm a _ = Just a
                                             cv  a _ = a
instance Convertible Char    Char     where  cvm a _ = Just a
                                             cv  a _ = a
instance Convertible Integer Integer  where  cvm a _ = Just a
                                             cv  a _ = a
*****************************
-}









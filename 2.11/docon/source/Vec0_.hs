------------------------------------------------------------------------
------------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
------------------------------------------------------------------------
------------------------------------------------------------------------





module Vec0_    

  -- Some operations for  Vector.
  --
  -- All needed from here is  reexported by  VecMatr.
  
  (allMaybesVec, vecSize, vecHead, vecTail, constVec, scalProduct
   -- , instances for Vector:  Dom, Functor
  )

where
import List     (genericLength)
import Categs   (Dom(..), Vector(..), vecRepr)
import DPrelude (Z, allMaybes, sum1)
import SetGroup (zeroS)
import Ring0_   (CommutativeRing())





--------------------------------------------------------------------
-- Initial items for  Vector,Matrix  are imported from Categs,Ring0_


instance Functor Vector  where  fmap f = Vec .map f .vecRepr


allMaybesVec :: [Maybe a] -> Maybe (Vector a)
allMaybesVec              =  fmap Vec . allMaybes
--------------------------------------------------------------------
instance Dom Vector
  where 
  sample = vecHead
  dom _  = error "dom (Vec..):  dom  not defined for Vector\n"


vecSize :: Vector a -> Z
vecSize =  genericLength . vecRepr

vecHead :: Vector a -> a 
vecHead    v        =  case vecRepr v of
                                  x:_ -> x  
                                  _   -> error "vecHead (Vec []) \n"
vecTail :: Vector a -> [a] 
vecTail    v        =  case vecRepr v of
                                 _:xs -> xs
                                 _    -> error "vecTail (Vec []) \n"

scalProduct :: CommutativeRing a => [a] -> [a] -> a
scalProduct                         xs     ys  =  

  case (xs ++ ys) 
  of
  x: _ -> sum1 ((zeroS x) : (zipWith (*) xs ys))
  _    -> error ("\nscalProduct [] []:   " ++ 
                 "at least one of the lists must be non-empty.\n"
                )


constVec :: Vector a -> b -> Vector b
constVec    v           b =  fmap (const b) v





{- reserve  ***************************
instance (Convertible a b) => Convertible a (Vector b)
  where
  cvm a = fmap Vec .cvm a .vecRepr     -- as Convertible a [b]
instance (Convertible a b) => Convertible (Vector a) (Vector b)
  where
  cvm  u@(Vec as) v@(Vec bs) = 
                         case  ((vecSize u)==(vecSize v), cvm as bs)
                         of  (False, _      ) -> Nothing
                             (_    , Just xs) -> Just (Vec xs)
**************************
-}













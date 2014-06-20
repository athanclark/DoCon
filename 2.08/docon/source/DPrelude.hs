--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------






module DPrelude   -- DoCon Prelude
  (
   sublists, listsOverList, smParse,

   -- from Prelude_:
   Cast(..), ct, ctr,
   PropValue(..), InfUnn(..), MMaybe, CompValue, Comparison,
   Z, toZ, fromZ,
   tuple31, tuple32, tuple33,  tuple41, tuple42, tuple43, tuple44,
   tuple51, tuple52, tuple53, tuple54, tuple55,
   eFM, lkp, zipRem, allMaybes, mapmap, fmapmap, mapfmap, fmapfmap,
   boolToPropV, propVToBool, not3, and3, or3,  compBy,  delBy, 
   separate, pairNeighbours, removeFromAssocList, addToAssocList_C,
   addListToAssocList_C, propVOverList, mbPropV, lookupProp, 
   updateProps, addUnknowns, 
   foldlStrict, foldl1Strict, 
   antiComp, minBy, maxBy, minimum, maximum, minAhead, maxAhead,

   -- from Iparse_:
   Expression(..), OpDescr, OpTable, ParenTable, lexLots, showsExpr,
   infixParse,                   

   parenTable, opTable,   -- from OpTab_ 

   module Char_,
   module List_,

   -- from Common_:
   partitionN, eqListsAsSets, del_n_th, halve, mulSign, invSign, 
   evenL, factorial, binomCoefs, isOrderedBy, mergeBy, mergeE, sort,
   sortBy, sortE,  sum1, product1, alteredSum, lexListComp,  
   minPartial, maxPartial,

   -- from Set_:
   less_m, lessEq_m, greater_m, greaterEq_m, incomparable, 
   showsWithDom
  ) 

where   
import Prelude hiding (maximum, minimum)
import Prelude_
import Iparse_
import OpTab_
import Common_
import Set_     (Set(..),  less_m, lessEq_m, greater_m,
                 greaterEq_m, incomparable, showsWithDom
                )
import Char_
import List_





--------------------------------------------------------------------
sublists :: [a] -> [[a]]
sublists []     =  [[]]
sublists (x:xs) =  (map (x:) ls)++ls  where  ls = sublists xs


listsOverList :: Z -> [a] -> [[a]]

  -- list of all lists of length  n  with the elements from  xs.
  -- It does Not take notice of the repetitions in  xs.

listsOverList 0 _  = [[]]
listsOverList n [] = error $ ("listsOverList "++) $ shows n " [] \n"
listsOverList n xs =
  if
    n < 0  then  error $ ("listsOverList "++) $ shows n
                                          " xs:     n > 0  needed\n"
  else
    ll n xs  where  ll 0 _  = [[]]
                    ll n xs = concat [map (:l) xs| l <- ll (n-1) xs]
                             -- probably,
                             -- this concat needs optimization *****

--------------------------------------------------------------------
smParse :: (Set a) => a -> String -> a

  -- Generic parsing by sample.
  -- Makes use  of  infixParse, fromExpr.
  -- See  infixParse  in Iparse.hs,  fromExpr  of Set class.

smParse sample s = case infixParse parenTable opTable$ lexLots s  of

  ([e], "" ) -> case  fromExpr sample e  of

          ([x],"" ) -> x
          (_  ,msg) -> error $ 
                         ("fromExpr sample str:  bad string.\n"++) $
                         showsWithDom sample "sample" "" 
                         ('\n':(msg++"\n"))

  (_  , msg) -> error ("infixParse:  "++msg++"\n")

 ;












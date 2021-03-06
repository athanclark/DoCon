------------------------------------------------------------------
------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
------------------------------------------------------------------
------------------------------------------------------------------





module Char_  

-- instances  Set, OrderedSet   for the Char  domain.
--
-- All needed from here is  reexported by  DPrelude.

where
import qualified Data.Map as Map (lookup, insert)

import Iparse_  (Expression(..), showsExpr     )
import Prelude_ (PropValue(..), InfUnn(..), toZ)

import Categs (CategoryName(..), Domain1(..), OSet(..), 
               Property_OSet(..), Construction_OSet(..)
              )
import Set_   (Set(..), OrderedSet())





------------------------------------------------------------------
instance Set Char  
  where   
  compare_m  x = Just . compare x 
  showsDomOf _ = ("Char"++)

  fromExpr _ (E (L "'") [] [L [c]]) = ([c], "")
  fromExpr _ e                      =  
    ( [], "(fromExpr <Char> e):  wrong e = " ++ (showsExpr e "") )

  baseSet _ dm = case  Map.lookup Set dm  of

    Just (D1Set o) -> (dm, o)
    _              -> (Map.insert Set (D1Set o) dm, o)
     where
     o = OSet {osetSample  = 'a',
               membership  = (\ _ _-> True),
               osetCard    = Fin (n2-n1+1),
               osetPointed = Just $ Just 'a',
               osetList    = Just list,
               osetBounds  = (Just $ Just minC, Just $ Just maxC,
                              Just $ Just minC, Just $ Just maxC  
                             ),       
               osetProps   = props,
               osetConstrs = 
                     [(Interval (Just minC) True (Just maxC) True)],
               osetOpers   = []
              }             
     (minC, maxC) = (minBound, maxBound) :: (Char, Char)
     [n1  , n2  ] = map (toZ . fromEnum) [minC, maxC]
     list         = [minC .. maxC]

     props        = [(Finite,      Yes), (FullType,      Yes), 
                     (IsBaseSet,   Yes), (OrderIsTrivial,No ),
                     (OrderIsTotal,Yes), (OrderIsNoether,Yes), 
                     (OrderIsArtin,Yes)
                    ]


instance OrderedSet Char

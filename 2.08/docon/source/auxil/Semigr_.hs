--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------




module Semigr_

  -- Category hierarchy. Continuation:
  -- items related to the  binary relation, semigroup.
  --
  -- All needed from here is  reexported by  Semigroup, Z.

  (-- categories
      AddSemigroup(..), OrderedAddSemigroup(), AddMonoid(),
      OrderedAddMonoid(), 

   upAddSemigroup, isGroup, isCommutativeSmg, trivialSubsemigroup,
   isoSemigroup, isoConstruction_Subsemigroup, zeroS, isZero, neg, 
   sub, times
   -- ,instances for  Integer:
   -- Set, OrderedSet, AddSemigroup, OrderedAddSemigroup, AddMonoid,
   -- OrderedAddMonoid
  )

where   
import Data.FiniteMap (addToFM)

import Maybe     (fromMaybe)

import Prelude_  (PropValue(..), InfUnn(..), Z, eFM, lkp, 
                  lookupProp, fmapmap, fmapfmap
                 )
import Categs   
       (CategoryName(..), Domain1(..), Domains1, OSet(..), 
        Property_OSet(..), Construction_OSet(..), Subsemigroup(..), 
        AddOrMul(..), Property_Subsemigroup(..), 
        Construction_Subsemigroup(..)
       )
import Iparse_  (Expression(..), showsExpr          )
import Set_     (Set(..), OrderedSet(), showsWithDom)





--------------------------------------------------------------------
timesbin :: (AddSemigroup a) => a -> Z -> Maybe a
                            -- generic binary method to multiply
timesbin x n                -- additive semigroup element by integer 
  | n==1      = Just x
  | n==0      = zero_m x
  | n<0       = maybe Nothing (\y->timesbin y (-n)) $ neg_m x

  | otherwise = let  Just h = timesbin x $ quot n 2
                in
                if  even n  then  Just (h `add` h)
                else              Just ((h `add` h) `add` x)


--------------------------------------------------------------------
isGroup, isCommutativeSmg :: Subsemigroup a -> PropValue

isGroup          = lookupProp IsGroup     . subsmgProps
isCommutativeSmg = lookupProp Commutative . subsmgProps



--------------------------------------------------------------------
isoSemigroup :: (a->b) -> (b->a) -> Subsemigroup a -> Subsemigroup b

  -- given a   Subsemigroup H with the base set X on a type `a',
  --           a map  f: a -> b  injective on X,
  --           f_inv  the inverse to  f  on X,
  -- produce  Subsemigroup H' on the base set f(X),  such that  
  -- f_restrictedTo_X  is an isomorphism between H and H'

isoSemigroup f f_inv hH = 
  let
    (opType,un,gens,props,conss,_) = 
                                  (subsmgType hH   , subsmgUnity hH,
                                   subsmgGens hH   , subsmgProps hH,  
                                   subsmgConstrs hH, subsmgOpers hH
                                  )
  in
  Subsemigroup 
    {subsmgType    = opType, 
     subsmgUnity   = fmapfmap f un,
     subsmgGens    = fmapmap  f gens,
     subsmgProps   = props,
     subsmgConstrs =
                   map (isoConstruction_Subsemigroup f f_inv) conss,
     subsmgOpers   = []
    }



--------------------------------------------------------------------
isoConstruction_Subsemigroup ::  
            (a -> b) -> (b -> a) -> Construction_Subsemigroup a ->
                                       Construction_Subsemigroup b

isoConstruction_Subsemigroup _f _fInv _ = ConsSemigDUMMY
  -- case constr 
  -- of Intersection_Subsemigroup smgs ->
  --   Intersection_Subsemigroup $ map (isoSemigroup f fInv) smgs
  -- GenBySet_Subsemigroup xX       -> 
  --                      GenBySet_Subsemigroup $ isoOSet f fInv xX

--------------------------------------------------------------------
trivialSubsemigroup :: Subsemigroup a -> Subsemigroup a

  -- make a  trivial subsemigroup  inside a Non-trivial base monoid 

trivialSubsemigroup bM =
  let
    (opType,unityM,propsBase) = 
                       (subsmgType bM,subsmgUnity bM,subsmgProps bM)
    un = case  unityM  
         of
           Just (Just u) -> u
           _             -> error ("trivialSubsemigroup baseMonoid:"
                                   ++"   zero (unity) not found\n"
                                  )
    props' =  
          [(Commutative          ,Yes    ), (IsGroup          ,Yes),
           (IsCyclicSemigroup    ,Yes    ), (IsMaxSubsemigroup,No ),
           (IsOrderedSubsemigroup,ordered)
          ]
    ordered = lookupProp IsOrderedSubsemigroup propsBase
  in
  Subsemigroup {subsmgType    = opType, 
                subsmgUnity   = Just $ Just un,
                subsmgGens    = Just [un],
                subsmgProps   = props',
                subsmgConstrs = [],
                subsmgOpers   = []
               }



--------------------------------------------------------------------
class (Set a) => AddSemigroup a  where  

  -- REQUIRED:  `add' associative, commutative, 
  --            agreed with (==), zero_m

  baseAddSemigroup :: a -> Domains1 a -> (Domains1 a,Subsemigroup a)

  add     :: a -> a -> a
  zero_m  :: a -> Maybe a
  neg_m   :: a -> Maybe a
  sub_m   :: a -> a -> Maybe a
  times_m :: a -> Z -> Maybe a

  zero_m x = let  sH = snd $ baseAddSemigroup x eFM 
             in 
             case  subsmgUnity sH  of  Just (Just z) -> Just z
                                       _             -> Nothing
  sub_m x = maybe Nothing (Just .add x) . neg_m
  times_m = timesbin   -- default definition via `add'


--------------------------------------------------------------------
-- up<category> :: <category> a => a -> Domains1 a -> Domains1 a 
--
-- <category> === AddSemigroup,MulSemigroup...Ring...,
--
-- differs from   base<category> x dom   in that it also forms all 
-- the *implied domains* for  x  and puts them into  doms'.
-- Examples:  
-- upAddSemigroup x dom 
--      will first add  osetTerm(x)  to  dom  - making dom', 
--      then add  addSemigroupTerm(x)  to  dom',  and return  dom''.
--
-- upRing  implies baseSet,AddSemigroup,MulSemigroup,AddGroup.
-- ...

upAddSemigroup :: (AddSemigroup a) => a -> Domains1 a -> Domains1 a
upAddSemigroup                      a =
                            fst .baseAddSemigroup a .fst .baseSet a

--------------------------------------------------------------------
class (OrderedSet a, AddSemigroup a) => OrderedAddSemigroup a  

         -- Presumed:   
         -- base AddSemigroup  contains  (IsOrderedSubsemigroup,Yes)
         --
         -- - see the Subsemigroup constructor.

--------------------------------------------------------------------
zeroS :: (AddSemigroup a) => a -> a
                        -- `zero' is the thing from Haskell Prelude,
                        -- so we call a semigroup zero differently
                        --
zeroS x = fromMaybe (error msg) $ zero_m x
           where
           msg = ("(zero x)  failed,"++) $ showsWithDom x "x" "" ""

isZero :: (AddSemigroup a) => a -> Bool
isZero                        a =  case zero_m a of  Just z -> a==z
                                                     _      -> False

neg :: (AddSemigroup a) => a -> a
neg                        x =  fromMaybe (error msg) $ neg_m x
             where
             msg = ("(neg x)  failed,"++) $ showsWithDom x "x" "" ""


sub :: (AddSemigroup a) => a -> a -> a
sub                        x    y = fromMaybe (error msg)$ sub_m x y
  where
  msg = ("(sub x y)  failed,"++) $ showsWithDom x "x" "" $
        ("y = "++) $ shows y "\n"

times :: (AddSemigroup a) => a -> Z -> a
times                        x    n = 
                                 fromMaybe (error msg) $ times_m x n
  where
  msg = ("times x "++) $ shows n $ ("  failed,"++) $
        showsWithDom x "x" "" "n"
   

{-# specialize zeroS  :: Z -> Z      #-}
{-# specialize isZero :: Z -> Bool   #-}
{-# specialize neg    :: Z -> Z      #-}
{-# specialize sub    :: Z -> Z -> Z #-}
{-# specialize times  :: Z -> Z -> Z #-}

--------------------------------------------------------------------
class (AddSemigroup a) => AddMonoid a 

               -- Setting   instance AddMonoid (..)   means that the
               -- programmer is sure that a semigroup (..)  has zero.
               -- Here  (zeroS x)  should give the true zero element 
               -- (hence, there is no need in  zero_m). 

class (OrderedAddSemigroup a,AddMonoid a) => OrderedAddMonoid a 


--------------------------------------------------------------------
--------------------------------------------------------------------
instance Set Z
  where   
  compare_m  x = Just .compare x
  showsDomOf _ = ("Z"++)

  fromExpr _ (L s) = case  reads s ::[(Z,String)]  of 

              [(n,_)] -> ([n], "")
              _       -> ([] , "(fromExpr <Integer> "++(show (L s)))

  fromExpr _ e     = ([], "fromExpr <Integer> "++(showsExpr e ""))

  baseSet _ dm = case  lkp dm Set  of

    Just (D1Set o) -> (dm, o)
    _              -> (addToFM dm Set $ D1Set o, o)
      where
      o = OSet
            {osetSample  = 1,           membership  = (\_ _-> True),
             osetCard    = Infinity,    osetPointed = Just $ Just 1,
             osetList    = Nothing,
             osetBounds  = (Just Nothing, Just Nothing,
                            Just Nothing, Just Nothing
                           ),
             osetProps   = props,
             osetConstrs = [(Interval Nothing False Nothing False)],
             osetOpers   = []
            }
      props = [(Finite      , No ), (FullType      , Yes),
               (IsBaseSet   , Yes), (OrderIsTrivial, No ),
               (OrderIsTotal, Yes), (OrderIsNoether, No ),
               (OrderIsArtin, No )
              ]

--------------------------------------------------------------------
instance OrderedSet Integer

instance AddSemigroup Integer  
  where 
  add       = (+)
  zero_m    = const $ Just 0
  neg_m     = Just .negate
  sub_m   x = Just .(x -)
  times_m x = Just .(x *)

  baseAddSemigroup _ dm = case  lkp dm AddSemigroup  of

    Just (D1Smg s) -> (dm, s)
    _              -> (addToFM dm AddSemigroup $ D1Smg s, s)  
      where
      s = Subsemigroup 
           {subsmgType    = Add,         subsmgUnity = Just$ Just 0,
            subsmgGens    = Just [1,-1], subsmgProps = props,
            subsmgConstrs = [],          subsmgOpers = []
           }
      props = [(Commutative          ,Yes), (IsGroup          ,Yes),
               (IsCyclicSemigroup    ,Yes), (IsMaxSubsemigroup,No ),
               (IsOrderedSubsemigroup,Yes)
              ]


instance OrderedAddSemigroup Integer
instance AddMonoid           Integer   
instance OrderedAddMonoid    Integer   





{- reserve  ********************************************************

-- Computable Binary relation between the base set of  a  and the
-- base set of  b.
data BinRel a b =   
     BinRel 
         {binRelSamples   :: (a,b),         -- sample data for Types
          binRelPredicate :: a -> b -> Bool,
          binRelMap       :: Maybe (a -> b),
          binRelLists     ::
                         Maybe (ListedBinRel a b, ListedBinRel b a),
          binRelCoimage   :: Maybe (OSet a),
          binRelImage     :: Maybe (OSet b),
          binRelProps     :: [(Property_binRel,PropValue)],
          binRelConstrs   :: [Construction_binRel a b],
          binRelOpers     :: Operations_binRel a b
        }
      deriving(Show)

type ListedBinRel a b = [(a,[b])]
       -- Here the formal domain and range mean that the predicate
       -- is considered only as Restricted to these subsets.
       -- IsMap==Yes  implies  co-image = base set.
       --
       -- binRelMap
       -- is only for the case of a map, it is  Nothing  when the
       -- relation is not known to be a map.
       --
       -- binRelLists 
       -- is either  Nothing  - the relation is not listed,
       -- or 
       -- Just (l1,l2)
       --       - the pair of the list representations (see below).
       --         In  l1  each  x <- coImage  is paired with all 
       --         the  y-s  related to  x,  x-s do not repeat.
       --         l2  represents the inverse relation.

data Property_binRel = 
             Reflexive          -- for BinRel a a
           | Symmetric          -- for BinRel a a
           | Transitive         -- for BinRel a a
           | IsFullBinRel       -- == (formalDomain x formalRange)
           | Injective
           | Surjective
           | IsConstantBinRel     -- image = {y} or {}
           | IsMap
           | IsIdentityBinRel     -- for BinRel a a,  means the
                                  -- identity map  - when 
                                  -- restricted to  domain

           deriving(Eq,Ord,Enum,Show,Read)

data Construction_binRel a b = 
                    ComposeBinRel      (BinRel a b) (BinRel b a)
                  | ReflClose          (BinRel a a)
                  | SymmClose          (BinRel a a)
                  | TransClose         (BinRel a a)
                  | ReflSymmTransClose (BinRel a a)
                  deriving(Show)

type Operations_binRel a b = [(OpName_binRel, Operation_binRel a b)]
data OpName_binRel         = Op_binRel_DUMMY   
                                     deriving(Eq,Ord,Enum,Show,Read)
data Operation_binRel a b  = Op_binRel_DUMMY' Char
                                                 deriving(Show,Read)
******************************************************
-}









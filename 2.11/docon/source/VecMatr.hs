--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.11
--
--  Copyright  Serge Mechveliani,    2007
--------------------------------------------------------------------
--------------------------------------------------------------------




module VecMatr

  -- Vector, Matrix  operations and their  category instances.
  --
  -- This head module implements the  matrix instances  and 
  -- reexports other needed items from other modules.

  (
   -- Vector(..),                   from Categs
   vecRepr,  {- Eq Vector, -}    -- from Categs
   Matrix(..), matrRows,         -- from Ring0_

   -- from Vec0_
   allMaybesVec, vecSize, vecHead, vecTail, constVec, scalProduct,
   -- instance Functor

   -- from Vec1_  
   vecBaseSet, vecBaseAddSemigroup, vecBaseAddGroup, 
   vecBaseMulSemigroup, vecBaseMulGroup, vecBaseRing,

   module Vec_,    
   -- instances for Vector:
   -- Show,Set,OrderedSet,AddSemigroup,AddMonoid,OrderedAddSemigroup,
   -- OrderedAddMonoid,AddGroup,OrderedAddGroup,MulSemigroup,
   -- OrderedMulSemigroup,MulMonoid,MulGroup,Ring,CommutativeRing,
   -- OrderedRing,Num,Fractional,
 
   -- from Matr0_:
   SquareMatrix(..),  toSqMt, fromSqMt, matrHeight, matrWidth,
   mtHeight, mtWidth, mtHead, isZeroMt, sqMatrSize, matrHead, 
   matrTail, mapMt, mapSqMt, transp, constMatr, constSqMatr,
   rowMatrMul, scalarMt, mainMtDiag, isDiagMt, isStaircaseMt,
   isLowTriangMt, vandermondeMt, resultantMt,

   -- from Matr1_:
   matrBaseSet, matrBaseAddSemigroup, matrBaseAddGroup, 
   sqMatrBaseSet, sqMatrBaseAddSemigroup, sqMatrBaseAddGroup, 
   sqMatrBaseMulSemigroup, sqMatrBaseRing
  )
where
import Maybe    (fromJust                    )
import DPrelude (showsWithDom                )
import Categs   (Dom(..), Vector(..), vecRepr)
import SetGroup  
import Ring0_    
import Vec0_
import Vec1_
import Vec_
import Matr0_
import Matr1_



--------------------------------------------------------------------
instance Show a => Show (Matrix a) 
  where   
  showsPrec _ m = ("(Mt  [ \n"++) . w1 (matrRows m) . ("\n ] )"++)
                           where
                           w1 []     = id
                           w1 [r]    = shows r
                           w1 (r:rs) = shows r . (",\n\n"++) . w1 rs

instance Show a => Show (SquareMatrix a)  
                                     where   
                                     showsPrec _ =  shows . fromSqMt



instance Set a => Set (Matrix a) 
  where   
  baseSet   = matrBaseSet
  compare_m = compareTrivially

  showsDomOf mM = case (matrHeight mM, matrWidth mM) of
     
    (0, _) -> error "showsDomOf (Mt []) \n"
    (n, 0) -> 
       error $ ("showsDomOf mM:   "++) $ shows n "  x  0   matrix\n"

    (n, m) -> ("(L "++) . shows n . (' ':) . shows m . (' ':) .
              showsDomOf (matrHead mM) . (')':)

  fromExpr mM e = case (matrRows mM, dom mM)
                  of
                  ([],   _) -> ([], "empty sample matrix")
                  (rows, d) -> case fromExpr rows e  
                               of
                               ([rs], "" ) -> ([Mt rs d], "" )
                               (_   , msg) -> ([]       , msg)


instance OrderedSet a => Ord (Matrix a)
  where
  compare x = fromJust . compare_m x

instance OrderedSet a => OrderedSet (Matrix a)


instance Set a => Set (SquareMatrix a)  
  where   
  baseSet   = sqMatrBaseSet
  compare_m = compareTrivially

  showsDomOf mM = case sqMatrSize mM of

     0 -> error "showsDomOf (SqMt []) \n"
     n -> ("L "++) . shows n . (' ':) . showsDomOf (sqMatrHead mM) .
          (')':)
          
  fromExpr (SqMt rows d) e = case fromExpr rows e  
                             of
                             ([rs], "" ) -> ([SqMt rs d], "" )
                             (_   , msg) -> ([]         , msg)


instance OrderedSet a => Ord (SquareMatrix a)
  where
  compare x = fromJust . compare_m x 

instance OrderedSet a => OrderedSet (SquareMatrix a)




--------------------------------------------------------------------
-- The additive (semi)group  for matrices is isomorphic to the  
-- additive (semi)group of the vectors of size n*m.

instance AddGroup a => AddSemigroup (Matrix a)  
  where 
  baseAddSemigroup = matrBaseAddSemigroup

  add (Mt rs dm) (Mt rs' _) = Mt (zipWith (zipWith add) rs rs') dm

  zero_m  m@(Mt rs _) = case rs of

                     (e:_):_ -> Just $ mapMt (const z) m
                                                  where  z = zeroS e
                     _       -> 
                       error "zero_m (Mt rows dom):  empty matrix\n"

  neg_m       = Just . mapMt neg
  times_m m n = Just $ mapMt (\ x -> times x n) m


--------------------------------------------------------------------
instance AddGroup a => AddSemigroup (SquareMatrix a)  
  where 
  baseAddSemigroup = sqMatrBaseAddSemigroup 

  add (SqMt rs d) (SqMt rs' _) = toSqMt $ add (Mt rs d) (Mt rs' d)

  zero_m  m@(SqMt rs _) = case rs of

                   (e:_):_ -> Just $ mapSqMt (const z) m
                                                  where  z = zeroS e
                   _       -> 
                     error "zero_m (SqMt rows dom):  empty matrix\n"

  neg_m       = Just . mapSqMt neg
  times_m m n = Just $ mapSqMt (\ x -> times x n) m

--------------------------------------------------------------------
instance OrderedAddGroup a => OrderedAddSemigroup (Matrix a)  
instance AddGroup        a => AddMonoid           (Matrix a)  
instance OrderedAddGroup a => OrderedAddMonoid    (Matrix a)  
instance OrderedAddGroup a => OrderedAddSemigroup (SquareMatrix a)  
instance AddGroup        a => AddMonoid           (SquareMatrix a)  
instance OrderedAddGroup a => OrderedAddMonoid    (SquareMatrix a)  

instance AddGroup a => AddGroup (Matrix a)  where
                                     baseAddGroup = matrBaseAddGroup

instance AddGroup a => AddGroup (SquareMatrix a)  
  where
  baseAddGroup = sqMatrBaseAddGroup 

instance OrderedAddGroup a => OrderedAddGroup (Matrix a)
instance OrderedAddGroup a => OrderedAddGroup (SquareMatrix a)

--------------------------------------------------------------------
instance CommutativeRing a => MulSemigroup (SquareMatrix a)  
  where
  baseMulSemigroup = sqMatrBaseMulSemigroup

  mul (SqMt rs d) (SqMt rs' _) = 
                               toSqMt $ matrMul (Mt rs d) (Mt rs' d)

  unity_m (SqMt rs d) = case rs of

         (e:_):_ -> Just $ SqMt (scalarMt rs u z) d
                                         where  
                                         (z, u) = (zeroS e, unity e)  

         _       -> error "unity_m (SqMt rows dom):  empty matrix\n"

  divide_m _ _ = 
       error $ concat ["divide_m (SqMt _ _) (SqMt _ _):   ",
                       "not defined for square matrices, so far.\n",
                       "For Euclidean domain  e,  use  ",
                       "inverseMatr_euc (m :: Matrix e) ...\n"
                      ]

  -- ?             
  -- inv_m m =  case inverseMatr(_euc?) m  of [] -> Nothing
  --                                          im -> Just im
  -- divide_m  t u =   ... toDiagMatr_ ...

  divide_m2 _ _ = 
       error $ concat ["divide_m2 (SqMt _ _) (SqMt _ _):   ",
                       "not defined for square matrices, so far.\n",
                       "For Euclidean domain  e,  use  ",
                       "inverseMatr_euc (m :: Matrix e) ...\n"
                      ]
  root _ _ = 
       error $ concat ["root n (SqMt _ _):   ",
                       "not defined for square matrices, so far,\n",
                       "sorry.\n"
                      ]
   
--------------------------------------------------------------------
instance (CommutativeRing a, MulMonoid a) =>
                                          MulMonoid (SquareMatrix a)

instance CommutativeRing a => Num (Matrix a)  
  where
  negate = mapMt neg
  (+)    = add
  (*)    = matrMul 
  m-m'   = add m (neg m')
  signum _ = error "signum (Mt _):  not defined for (Matrix a)\n" 
  abs    _ = error "abs (Mt _):  not defined for (Matrix a)\n" 
  fromInteger _ = error "fromInteger:  use  fromi, fromi_m\n" 

instance CommutativeRing a => Num (SquareMatrix a)  
  where
  negate = mapSqMt neg
  (+)    = add 
  (-)    = sub 
  (*)    = mul 
  signum _ = 
        error "signum (SqMt _):  not defined for (SquareMatrix a)\n"
  abs    _ = 
           error "abs (SqMt _):  not defined for (SquareMatrix a)\n" 
  fromInteger _ = error "fromInteger:  use  fromi, fromi_m\n" 


instance CommutativeRing a => Fractional (Matrix a)      
  where
  fromRational _ = 
     error $ concat 
       ["fromRational (Mt _):  \n",
        "Fractional  instance is dummy for (Matrix a).\n",
        "For Euclidean domain  e,  use  ",
        "inverseMatr_euc (m :: Matrix e) ...\n"
       ]

instance CommutativeRing a => Fractional (SquareMatrix a) 
  where
  fromRational _ = 
     error $ concat 
       ["fromRational (SqMt _):  \n",
        "Fractional  instance is dummy for (Matrix a).\n",
        "For Euclidean domain  e,  use  ",
        "inverseMatr_euc (m :: Matrix e) ...\n"
       ]

--------------------------------------------------------------------
instance CommutativeRing a => Ring (SquareMatrix a) 
  where
  baseRing = sqMatrBaseRing

  fromi_m mt n =  
    (case  
         (sqMatrRows mt, unity_m mt)
     of
       ((e:_):_, Just uM) -> case fromi_m e n
                             of
                             Just c -> Just $ mapSqMt (mul c) uM
       ((e:_):_, _      ) -> 
                  error $ msg $ showsWithDom e "sqMatrHead mM" "R" $
                                "\nunity not found in  R \n"
       (_      , Just uM) ->
            error $ msg $ ("R =  "++) $ showsDomOf (sqMatrHead uM) $
                                        "\n\nEmpty  mM\n"
    )
    where  
    msg = ("fromi_m mM "++) . shows n . 
          ("mM = sampleSquareMatrix  over  R  has size  "++) . 
          shows (sqMatrSize mt) . ("\n"++) 

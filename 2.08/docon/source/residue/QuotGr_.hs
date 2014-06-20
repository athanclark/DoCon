--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module QuotGr_ 

  -- Operations in the  Quotient group  of  a commutative group.
  -- Constructor  ResidueG.
  -- See Manual.

  -- All needed from here is reexported by  Residue.


  (ResidueG(..), isCorrectRsg, 
   -- instances  
   -- Cast, Residue, Dom, Set, AddSemigroup, AddMonoid, AddGroup
  )

where
import Data.FiniteMap (addToFM)
   
import Random   (Random(..)        )
import List     (nub, genericLength)
import DPrelude  
       (Cast(..), ct, ctr, InfUnn(..), PropValue(..), lkp,
        lookupProp, showsWithDom
       )
import Categs 
       (CategoryName(..), Dom(..), Domain1(..), Domains1, 
        AddOrMul(..), OSet(..), Subsemigroup(..), Subgroup(..), 
        Property_OSet(..), Property_Subsemigroup(..), 
        Property_Subgroup(..)
       )
import SetGroup  
       (Set(..), AddSemigroup(..), AddMonoid(), AddGroup(..), 
        compareTrivially, zeroS, neg, sub, isFiniteSet, 
        upAddSemigroup, upAddGroup
       )
import RingModule (FactorizationRing(..))
import Z          ()
import ResEuc0_   (Residue(..), resSubgroup) 






--------------------------------------------------------------------
data ResidueG a =  Rsg a (Subgroup a, Domains1 a) (Domains1 a)

instance Residue ResidueG
  where
  resRepr   (Rsg x _ _) = x
  resGDom   (Rsg _ d _) = d
  resIDom   _           = 
             error "resIDom (Rsg..)  - it is not defined for  Rsg\n"
  resPIdeal _           = 
           error "resPIdeal (Rsg..)  - it is not defined for  Rsg\n"

instance Dom ResidueG  where  dom (Rsg _ _ d) = d
                              sample          = resRepr


instance (AddGroup a) => Cast (ResidueG a) a
  where
  cast  mode  r@(Rsg _ gdom d)  a =  
    case
        (mode=='r', subgrCanonic $ fst gdom)
    of
      (False, _      ) -> Rsg a      gdom d
      (_    , Just cn) -> Rsg (cn a) gdom d
      _                -> error$ ("cast "++)$ (mode:)$ (" r a,"++) $
                                 showsWithDom a "a" "" $
                                 showsWithDom r "r" "" messgCanMap

messgCanMap = "\nCanonical map modulo subgroup not found\n" 


isCorrectRsg :: (AddGroup a) => ResidueG a -> Bool
isCorrectRsg                    r@(Rsg x d _) =
  case  subgrCanonic $ fst d
  of
    Just can -> x==(can x)
    Nothing  -> error $ ("isCorrectRsg r,"++) $
                            showsWithDom r "r" "" ('\n':messgCanMap)



{- reserve **************
instance (Convertible a b) => Convertible a (ResidueG b)
  where cvm a r = case cvm a (resRepr r) of Just c-> Just (ctr r c)
                                            _      -> Nothing
********************** 
-}



--------------------------------------------------------------------
-- Random, Set, semigroup ... instances for the Quotient group  A/H,   
--
-- A = baseAddGroup x,   H  a NON-trivial  subgroup in  A.


instance (AddGroup a, Random a) => Random (ResidueG a)  
  where
  randomR (l,h) g = (ctr l a, g')  where
                            (a,g') = randomR (resRepr l,resRepr h) g

  random _ = error "random  for (ResidueG _):  use  randomR\n"  


instance (AddGroup a) => Set (ResidueG a)  
  where
  compare_m   = compareTrivially   -- so far
  baseSet     = rsgBaseSet

  fromExpr r e = case  fromExpr (resRepr r) e  of

            ([x], "" ) -> ([ctr r x], "")
            (_  , msg) -> ([], "fromExpr (Rsg sample _ _) e:  could"
                               ++" not read  e  as sample.\n" ++ msg
                          )
  showsDomOf r =
           ('{':) .showsDomOf a .("/Subgroup<"++) .showsGs .(">}"++)
            where
            (a,gH)  = (resRepr r, resSubgroup r)
            showsGs = case  subgrGens gH 
                      of
                        Nothing     -> ("?"++)
                        Just []     -> id
                        Just [g]    -> shows g
                        Just (g:gs) -> shows g .("... a_"++) 
                                       .shows (genericLength (g:gs))

--------------------------------------------------------------------
instance (AddGroup a) => AddSemigroup (ResidueG a)  
  where
  baseAddSemigroup = rsgBaseAddSemigroup           
  zero_m r         = Just $ ct  r $ zeroS $ resRepr r
  neg_m  r         = Just $ ctr r $ neg $   resRepr r
  add    r         = ctr r .add (resRepr r) .resRepr
  sub_m  r         = Just .ctr r .sub (resRepr r) .resRepr


instance (AddGroup a) => AddMonoid (ResidueG a)

instance (AddGroup a) => AddGroup (ResidueG a)  
  where 
  baseAddGroup = rsgBaseAddGroup



--------------------------------------------------------------------
-- see  instance ... => Set (ResidueG a) ...


rsgBaseSet  r@(Rsg x dG aD) dm =  case  lkp dm Set  of

  Just (D1Set o) -> (dm, o)
  _              ->
    (case  (subgrCanonic $ fst dG, lkp aD Set)
     of
       (Nothing  , _                ) -> 
                                       (dm, error $ msg messgCanMap)
       (_        , Nothing          ) -> (dm, error $ msg msgSetA)
       (Just canr, Just (D1Set setA)) -> rbs canr setA
    )
    where
    msg    = ("baseSet r dom', \n"++) 
             .("r = "++). shows r .("\n <- D/H =  "++) .showsDomOf r

    msgSetA = "\n\nSet not found in  D\n"
    msgSetH = "\n\nSet not found in  H\n"
    (gH,hD) = dG

    rbs canr setA = case  lkp hD Set  of

      Nothing           -> (dm, error $ msg msgSetH)
      Just (D1Set setH) -> (addToFM dm Set $ D1Set o, o)
        where
        o = 
          let
            bel        = membership setA  
            gensH      = subgrGens gH
            redRes x   = Rsg (canr x) dG aD
            (_,gA)     = baseAddGroup x aD
            (gensA,ps) = (subgrGens gA, subgrProps gA)

            bel' 'r' r = isCorrectRsg r  &&  (bel 'r' $ resRepr r)
            bel' _   r = isCorrectRsg r 

            (cardA,cardH) = (osetCard    setA, osetCard    setH)
            (finA,finH)   = (isFiniteSet setA, isFiniteSet setH)
            cycAl         = lookupProp IsCyclicGroup ps
            --------------------------------------------------------
            props' = [(Finite        , fin'), (IsBaseSet, Yes),   
                      (FullType      , No  ),       -- for gH/={0}
                      (OrderIsTrivial, Yes ),       -- so far
                      (OrderIsTotal  , No  ), 
                      (OrderIsNoether, Yes ), (OrderIsArtin, Yes)
                     ]
            fin' = case  (cycAl,finA,finH)  of 
                                          (Yes, _  , _  ) -> Yes
                                          (_  , Yes, _  ) -> Yes
                                          (_  , No , Yes) -> No
                                          _               -> Unknown
            --------------------------------------------------------
            card' = case  (cardA,cardH,gensA,gensH)  of

              (_       , Infinity, Just [g], Just [h]) -> 
                                              Fin $ multiplicity g h
              (_       , Infinity, _       , _       ) -> UnknownV
              (_       , UnknownV, Just [g], Just [h]) -> 
                                              Fin $ multiplicity g h
              (_       , UnknownV, _       , _       ) -> UnknownV
              (Infinity, _       , _       , _       ) -> Infinity 
              (UnknownV, _       , Just [g], Just [h]) -> 
                                              Fin $ multiplicity g h
              (UnknownV, _       , _       , _       ) -> UnknownV
              (Fin n   , Fin m   , _       , _       ) -> 
                  if
                     (mod n m)==0  then  Fin $ quot n m
                  else    
                    error $ msg ("\n\nfinding card(D/H):  card(H)"++
                                 " does not divide card(D) - why?\n"
                                )
            --------------------------------------------------------
            multiplicity x y =  
                      if  x==y  then  1 
                      else            1 + (multiplicity x $ sub y x)
            --------------------------------------------------------
            list' = case  (gensA,gensH)  of

              (Just [g],Just [h]) ->  
                   Just $ map redRes $ multiplesUpTo g h g [zeroS g]
              _                   ->
                    fmap (map (ct r) .nub .map canr) $ osetList setA

            multiplesUpTo x y sum zs =
              if  
                y==sum  then  zs 
              else            multiplesUpTo x y (add sum x) (sum:zs)      
            --------------------------------------------------------
         in
         OSet {osetSample  = r,         membership  = bel', 
               osetCard    = card',     osetPointed = Just $ Just r,
               osetList    = list',
               osetBounds  = (Nothing,Nothing,Nothing,Nothing),
               osetProps   = props',
               osetConstrs = [],        osetOpers   = []
              }                                



--------------------------------------------------------------------
rsgBaseAddSemigroup  r@(Rsg x dG aD) dm =  
                                       case  lkp dm AddSemigroup  of
  Just (D1Smg s) -> (dm, s)
  _              ->
    (case  (subgrCanonic $ fst dG, lkp aD Set)
     of
       (Nothing  , _                ) -> 
                                       (dm, error $ msg messgCanMap)
       (_        , Nothing          ) -> (dm, error $ msg msgSetA)
       (Just canr, Just (D1Set setA)) -> rbs (zeroS x) canr setA
    )
    where
    msg = ("baseAddSemigroup r dom', \n"++)
          .("r = "++). shows r .("\n <- D/H =  "++) .showsDomOf r

    msgSetA       = "\n\nSet not found in  D\n"
    (dm',setRes)  = baseSet r dm
    rbs zr canr _ = (addToFM dm' AddSemigroup $ D1Smg s, s)
      where
      s = 
       let
         (aD,smgA)         = baseAddSemigroup x aD
         (_ ,gA  )         = baseAddGroup x aD
         (gensA,smgAProps) = (subgrGens gA, subsmgProps smgA)

         props'= [(Commutative          , Yes    ), (IsGroup,Yes),
                  (IsMaxSubsemigroup    , No     ),
                  (IsOrderedSubsemigroup, Unknown), -- so far
                  (IsCyclicSemigroup    , cyc'   )   
                 ]
         cyc' = 
           case (lookup IsCyclicSemigroup smgAProps,osetCard setRes)
           of                                   
             (Just Yes, _    ) -> Yes
             (_       , Fin n) -> if  isPrime n  then Yes  
                                  else                Unknown
             _                 -> Unknown
                                  -- further possible solutions?

         gens' = case  (gensA, osetList setRes)  of
                              -- many optimizations are possible ***

           (Just xs, _        ) -> 
               Just $ map (ct r) $ nub $ filter (/=zr) $ map canr xs

           (_      , Just ress) -> Just $ gensModulo ress
                                       where 
                                       gensModulo xs = xs  -- so far
           _                    -> Nothing
       in
       Subsemigroup 
             {subsmgType    = Add,    subsmgUnity = Just $ zero_m r,
              subsmgGens    = gens',  subsmgProps = props',
              subsmgConstrs = [],     subsmgOpers = []  
            }                                       



--------------------------------------------------------------------
rsgBaseAddGroup  r@(Rsg x dG aD) dm =  case lkp dm AddGroup of

  Just (D1Group g) -> (dm, g)
  _                ->
    (case  subgrCanonic $ fst dG  of
                          Just canr -> rg (zeroS x) canr
                          _         -> (dm, error $ msg messgCanMap)
    )
    where
    msg = ("baseAddGroup r dom', \n"++)
          .("r = "++). shows r .("\n <- D/H =  "++) .showsDomOf r

    dm'                 = upAddSemigroup r dm
    Just (D1Set setRes) = lkp dm' Set

    rg zr canr = (addToFM dm' AddGroup $ D1Group g, g)
      where
      g = 
        let
          canForRes = const $ zeroS r
                                    -- base subgroup is the full one
          dA                 = upAddGroup x aD
          Just (D1Group gA)  = lkp dA AddGroup
          (gens_gA,props_gA) = (subgrGens gA, subgrProps gA)

          props' = [(IsNormalSubgroup , Yes   ),
                    (IsMaxSubgroup    , No    ), 
                    (IsOrderedSubgroup, No    ),   -- so far            
                    (IsCyclicGroup    , cyc'  ),
                    (IsPrimeGroup     , prime')
                   ]
          prime' = case  (lookup IsPrimeGroup props_gA, primeCard)
                   of
                     (Just Yes, _   ) -> Yes
                     (_       , True) -> Yes
                     _                -> Unknown

          primeCard = case osetCard setRes  of  Fin n -> isPrime n
                                                _     -> False

          cyc' =  case (lookup IsCyclicGroup props_gA, primeCard)
                  of
                    (Just Yes, _   ) -> Yes
                    (_       , True) -> Yes
                    _                -> Unknown

          gens' = case  (gens_gA, osetList setRes)  of
                              -- many optimizations are possible ***

            (Just xs, _        ) -> 
                Just $ map (ct r) $ nub$ filter (/=zr) $ map canr xs

            (_      , Just ress) -> Just $ gensModulo ress
                                       where 
                                       gensModulo xs = xs  -- so far
            _                    -> Nothing
        in
        Subgroup 
               {subgrType    = Add,             subgrGens  = gens', 
                subgrCanonic = Just canForRes,  subgrProps = props',
                subgrConstrs = [],              subgrOpers = []
               }                           

  ;





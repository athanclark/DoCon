--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------






module RsePol0_ 

  -- All needed from here is  reexported by  Residue.

  (msgField
   -- ,Specialization of R/(g), R Euclidean, to R = k[x], k a Field:
   -- Field k => ResidueE (UPol k).
   -- Instances up to  AddGroup, MulSemigroup
  )

where
import Data.FiniteMap (addToFM) 

import List       (delete )
import DPrelude   (PropValue(..), InfUnn(..), Z, Comparison, lkp, 
                   lookupProp, ct, ctr, showsWithDom
                  )
import Categs 
import SetGroup
import RingModule (Field(), PIRChinIdeal(..), isField)
import UPol_      (PolLike(..), UPol(..), upolMons, varP, cPMul, 
                   pmul, monicUPols_overFin
                  )
import Pol2_      ()
import ResEuc0_   (Residue(..)        )
import ResEuc1_   (rseBaseMulSemigroup)
import qualified ResEuc_ (rseShowsd_, rseFromExpr_, rseDivm_)






--------------------------------------------------------------------
msgField str = str++"  should a Field\n"     --LOCAL



--------------------------------------------------------------------
instance (Field a) => Set (ResidueE (UPol a))
  where
  compare_m  = compareTrivially 
  showsDomOf = ResEuc_.rseShowsd_
  fromExpr   = ResEuc_.rseFromExpr_

  baseSet  r@(Rse f iI fD) dm =  
               case  (lkp dm Set, pirCIBase iI, sample f, dom f)  of

    (Just (D1Set o), _, _, _ ) -> (dm, o)  
    (_             , g, a, aD) ->
      (case
           (lkp aD Set, lkp aD Ring)
       of
         (Just (D1Set setA), Just (D1Ring rA)) ->
                                           rbs g a setA $ isField rA
         _                                         ->
                 (dm, error $ msg "\nSet or Ring not found in  R\n")
      )
    where
    msg = ("baseSet r rdom,"++) .showsWithDom r "r" "R[_]/I" .('\n':)

    rbs _ _ _    No      = (dm, error $ msg $ msgField "R")

    rbs g a setA isfield = (addToFM dm Set $ D1Set o, o)
      where
      o =
        let
          (z,u,degG) = (zeroS a, unity a, deg g)
          x          = varP u f
          belP       = membership $ snd $ baseSet f fD

          card' = case  (isfield, osetCard setA)  
                  of 
                    (_  , UnknownV) -> UnknownV
                    (_  , Infinity) -> Infinity
                    (Yes, Fin n   ) -> Fin (n^degG)
                    _               -> UnknownV

          bel' md (Rse f _ _) = ldeg f < degG  &&  bl md f
                                                 where
                                                 bl 'r' = belP 'r'
                                                 bl _   = const True

          list' = case  (isfield, osetList setA)  of
     
            (Yes, Just as) ->
              let
                but0         = delete z as
                assocClass f = [cPMul a f| a <- but0]
                constPols    = map (ctr f) as
                assocGroups  = takeWhile ((< degG) .deg .head) $
                                                monicUPols_overFin x
                nonConstPols =
                        concat $ map assocClass $ concat assocGroups
              in
              Just $ map (ct r) $ (constPols++nonConstPols)

            _              -> Nothing

          props' = [(Finite        , isFiniteSet setA), 
                    (IsBaseSet     , Yes),   
                    (FullType      , No ), 
                    (OrderIsTrivial, Yes),  -- so far
                    (OrderIsTotal  , No ), 
                    (OrderIsNoether, Yes),  (OrderIsArtin, Yes)
                   ]               
        in
        OSet {osetSample  = r,         membership  = bel', 
              osetCard    = card',     osetPointed = Just $ Just r,
              osetList    = list',
              osetBounds  = (Nothing,Nothing,Nothing,Nothing),
              osetProps   = props',
              osetConstrs = [],      
              osetOpers   = []
             }


--------------------------------------------------------------------
instance (Field a) => AddSemigroup (ResidueE (UPol a))  
  where
  -- in this case, the additive operations in  k[x]/(g) 
  -- skip the reduction by g:

  zero_m  r = Just $ ct r $ zeroS $ resRepr r

       -- add, neg_m .. imes_m  skip the reduction by base, because
       --                       these operations are linear over  k

  neg_m   r = Just $ ct r $   neg$ resRepr r
  add     r = ct r .add (resRepr r) .resRepr
  sub_m   r = Just .ct r .sub (resRepr r) .resRepr
  times_m r = Just .ct r .times (resRepr r)

  baseAddSemigroup  r@(Rse f iI _)  dm =  
    (case  
         (lkp dm AddSemigroup, pirCIBase iI, dom f)
     of
       (Just (D1Smg s), _, _ ) -> (dm, s)
       (_             , g, aD) ->
         case  
              (lkp aD AddSemigroup, lkp aD AddGroup)
         of
           (Just (D1Smg sA), Just (D1Group gA)) -> 
                                         semig g sA gA $ lkp aD Ring
           _                                    ->
                                              (dm, error $ msg msg1)
    )
    where
    msg = ("baseAddSemigroup r rdom,"++).showsWithDom r "r" "R[_]/I"
          .('\n':)
    msg1 =  
         "\nAddSemigroup or AddGroup or Ring term not found in  R\n"

    semig _ _  _  Nothing            = (dm, error $ msg msg1)
    semig g sA gA (Just (D1Ring rA)) = case  isField rA  of

      No      -> (dm, error $ msg $ msgField "R")
      isfield -> (addToFM dm AddSemigroup $ D1Smg s, s)
        where
        s =
          let
            (degG , zeroRes) = (deg g       , zeroS r       )
            (gensA, sAProps) = (subgrGens gA, subsmgProps sA)

            props'= [(Commutative          , Yes    ),
                     (IsGroup              , Yes    ),
                     (IsMaxSubsemigroup    , No     ),
                     (IsOrderedSubsemigroup, Unknown),  -- so far
                     (IsCyclicSemigroup    , cyc'   )   
                    ]
            cyc'  = case  (isfield,degG)
                    of
                      (Yes,1)-> lookupProp IsCyclicSemigroup sAProps
                      (Yes,_)-> No
                      _      -> Unknown

            gens' = case  (isfield, gensA)  of
                      -- if gA is generated by  as, then  a[x]/g  is
                      -- generated by [a*x^i| a<-as, i<-[0..degG-1]]

              (Yes, Just as) -> Just [ct r $ ct f (b,i) |
                                         b <- as, i <- [0..(degG-1)]
                                     ]
              _              -> Nothing
          in
          Subsemigroup 
           {subsmgType    = Add,   subsmgUnity = Just$ Just zeroRes,
            subsmgGens    = gens', subsmgProps = props',
            subsmgConstrs = [],    subsmgOpers = []  
           }    

        
--------------------------------------------------------------------
instance (Field a) => AddGroup (ResidueE (UPol a))
  where 
  baseAddGroup  r@(Rse f iI _) dm =  
    (case  
         (lkp dm AddGroup, pirCIBase iI, dom f)  
     of
       (Just (D1Group g), _, _ ) -> (dm, g)
       (_               , g, aD) ->
         case 
             (lkp aD Set, lkp aD AddGroup, pirCIFactz iI)
         of
           (_,               Nothing          , _ ) ->
                                              (dm, error $ msg msg1)

           (Just (D1Set sA), Just (D1Group gA), ft) -> 
                                         gr g sA gA ft $ lkp aD Ring
    )
    where
    msg = ("baseAddGroup r rdom,"++).showsWithDom r "r" "R[_]/I"
          .('\n':)
    msg1 = "\nAddGroup or Ring not found in  R\n"

    gr _ _  _  _  Nothing            = (dm, error $ msg msg1)

    gr g sA gA ft (Just (D1Ring rA)) = case  isField rA  of

      No      -> (dm, error $ msg $ msgField "R")
      isfield -> (addToFM dm AddGroup $ D1Group gG, gG)
        where
        gG = 
          let
            (zrRes,   degG    ) = (zeroS r     , deg g        )
            (gens_gA, props_gA) = (subgrGens gA, subgrProps gA)

            props' = [(IsNormalSubgroup , Yes    ),
                      (IsMaxSubgroup    , No     ), 
                      (IsOrderedSubgroup, Unknown),   -- so far            
                      (IsCyclicGroup    , cyc'   ),
                      (IsPrimeGroup     , prime' )
                     ]
            cyc'   = case  (isfield, degG)  
                     of
                       (Yes,1) -> lookupProp IsCyclicGroup props_gA
                       (Yes,_) -> No
                       _       -> Unknown

            -- a[x]/(g) is a prime group <==>
            --                          a  is finite and g is prime.
            -- For primality of  g  inspect the factorization in iI
            --
            prime' = case  (isFiniteSet sA, ft)  
                     of
                       (No , _       ) -> No
                       (_  , []      ) -> Unknown 
                                             -- factorization skipped
                       (Yes, [(_,1)] ) -> Yes
                       (_  , [(_,1)] ) -> Unknown
                       _               -> No 

            gens' = case  (isfield, gens_gA)  of
                      -- if gA is generated by  as, then  a[x]/g  is
                      -- generated by [a*x^i| a<-as, i<-[0..degG-1]]

              (Yes, Just as) -> Just [ct r $ ct f (b,i) |
                                         b <- as, i <- [0..(degG-1)]
                                     ]
              _              -> Nothing
          in
          Subgroup 
           {subgrType    = Add,                 subgrGens  = gens', 
            subgrCanonic = Just $ const zrRes,  subgrProps = props',
            subgrConstrs = [],                  subgrOpers = []
           }                           


--------------------------------------------------------------------
instance (Field a) => MulSemigroup (ResidueE (UPol a))
  where
  baseMulSemigroup = rseBaseMulSemigroup
  unity_m r        = Just $ ct r $ unity $ resRepr r
  divide_m         = ResEuc_.rseDivm_

  -- inv_m, power    are the default ones.

  mul r =      -- applies optimization for the case  Ideal = (a*x^n)
    (case 
         upolMons $ pirCIBase $ resPIdeal r
     of
       [(_,n)] -> 
                ct r .ct f .pmul z cp (rd n) mons .upolMons .resRepr
       _       -> ctr r . mul f . resRepr
    ) where
      (f,    cp) = (resRepr r, compare :: Comparison Z)
      (mons, z ) = (upolMons f, zeroS $ sample f)
      rd n (a,m) = if  m < n  then  (a,m)  else  (z,0) 

  divide_m2 _ _ = 
         error "divide_m2  for ResidueE (UPol _):   use  divide_m\n"
  root _ _ = error ("root _  for ResidueE (UPol _): \n"++
                    "not defined so far, sorry\n"
                   )

 ;




module ResEuc1_  where

-- Auxiliary for  ResEuc_.hs   - see the comments there.
--
-- All needed from here is  reexported by  Residue.
 

import Data.FiniteMap (addToFM)

import Maybe     (fromJust )
import List      (nub, find) 

import DPrelude  (PropValue(..), InfUnn(..), Z, lkp, ct, ctr, not3, 
                  boolToPropV
                 )
import Categs
import SetGroup  
import Ring0_    (isCEucRing                )
import Ring1_    (remEuc                    )
import ResEuc0_  (Residue(..),  isCorrectRse)







--------------------------------------------------------------------
ifCEuc_rse_ :: Domains1 a -> b -> (String->String) -> (b,c) -> (b,c)
ifCEuc_rse_    aDom          dom  msg                 v     =  
  case  
      lkp aDom EuclideanRing  
  of
    Nothing         ->
            (dom, error $ msg "\n\nEuclideanRing not found in  D\n")

    Just (D1EucR t) -> case  isCEucRing t  of

        No -> (dom, error $ msg "\n\nc-Euclidean ring  D  needed\n")
        _  -> v


--------------------------------------------------------------------
rseBaseSet r dm = case  (lkp dm Set, resPIdeal r, dom r)  of

  (Just (D1Set o), _ , _ ) -> (dm, o)
  (_             , iI, aD) ->
    (case  (pirCIBase iI, lkp aD Set)
     of
       (_, Nothing          ) -> (dm, error $ msg1 msg)
       (b, Just (D1Set setA)) ->
               ifCEuc_rse_ aD dm msg1 $ rbs b setA $ membership setA
    )
  where
  msg1 =  ("baseSet r dom', \n"++)
         .("r = "++) .shows r .("\n <- D/I =  "++) .showsDomOf r 

  msg  = "\n\nSet or EuclideanRing  not found in  D\n"

  rbs b setA bel = (addToFM dm Set $ D1Set o, o)
    where
    o = 
       let
         canr x                 = remEuc 'c' x b
         bel' md r@(Rse x iJ _) =
                     isCorrectRse r  &&  (pirCIBase iJ)==b  &&  bl x
                   where
                   bl = if  md=='r'  then  bel 'r'  else  const True

         card' = UnknownV   -- to be developed  ***

         ll'   = fmap (map (ct r) .nub .map canr) $ osetList setA

         props' = [(Finite        , fin'), (IsBaseSet, Yes),   
                   (FullType      , No  ), 
                   (OrderIsTrivial, Yes ),  -- so far
                   (OrderIsTotal  , No  ), 
                   (OrderIsNoether, Yes ), (OrderIsArtin, Yes)
                  ]               
         fin' = case  card'  of  UnknownV -> Unknown
                                 Infinity -> No
                                 _        -> Yes
       in
       OSet {osetSample  = r,           membership  = bel', 
             osetCard    = card',       osetPointed = Just $ Just r,
             osetList    = ll',
             osetBounds  = (Nothing,Nothing,Nothing,Nothing),
             osetProps   = props',
             osetConstrs = [],        
             osetOpers   = []
            }                                





--------------------------------------------------------------------
rseBaseAddSemigroup r dm = 
                 case  (lkp dm AddSemigroup, resPIdeal r, dom r)  of

 (Just (D1Smg s), _ , _ ) -> (dm, s)
 (_             , iI, aD) ->
  let 
     b = pirCIBase iI
  in
  (case  (lkp aD AddSemigroup, lkp aD AddGroup)
   of
     (Just (D1Smg sA), Just (D1Group gA)) -> 
                              ifCEuc_rse_ aD dm msg1 $ semig b sA gA
     _                                    -> (dm, error $ msg1 msg)
  )   
  where
  msg1 =  ("baseAddSemigroup r dom', \n"++)
         .("\nr = "++) .shows r .("\n <- D/I =  "++) .showsDomOf r

  msg  = "\n\nAddSemigroup or AddGroup not found in  D\n"

  semig b sA gA = (addToFM dm' AddSemigroup $ D1Smg s, s)
    where
    (dm',rSet) = baseSet r dm
    s          =
      let
        zr              = zeroS b
        zeroRes         = ct r zr
        canr x          = remEuc 'c' x b
        (gensA,sAProps) = (subgrGens gA, subsmgProps sA)

        props' = [(Commutative          , Yes    ), (IsGroup,Yes),
                  (IsMaxSubsemigroup    , No     ),
                  (IsOrderedSubsemigroup, Unknown),  -- so far
                  (IsCyclicSemigroup    , cyc'   )   
                 ]
        cyc'   = case  lookup IsCyclicSemigroup sAProps
                 of
                   Just Yes -> Yes    -- residue of cyclic is cyclic
                   _        -> Unknown
                     --
                     -- we could use further isPrime (card(residue))
                     -- but isPrime is not compiled yet for Z
                     -- at *this* point of program modules !

        gens' = case  (gensA, osetList rSet)  of
                                  -- many optimizations possible ***
          (Just xs, _        ) ->  
               Just $ map (ct r) $ nub $ filter (/=zr) $ map canr xs
                               
          (_      , Just ress) -> 
                   Just $ map (ct r) $ gensModulo $ map resRepr ress
                                      where 
                                      gensModulo xs = xs   -- so far
          _                    -> Nothing
      in
      Subsemigroup 
         {subsmgType    = Add,    subsmgUnity = Just (Just zeroRes),
          subsmgGens    = gens',  subsmgProps = props',
          subsmgConstrs = [],     subsmgOpers = []  
         }                                       


      



rseBaseMulSemigroup r dm = 
                   case  (lkp dm MulSemigroup, resRepr r, dom r)  of

  (Just (D1Smg s), _, _ ) -> (dm, s)
  (_             , x, aD) -> ifCEuc_rse_ aD dm msg (dm',s)
    where
    msg = ("baseMulSemigroup r dom', \n"++)
          .("\nr = "++) .shows r .("\n <- D/I =  "++) .showsDomOf r

    dm' = addToFM dm MulSemigroup $ D1Smg s
    s   =
        let  unR   = ctr r $ unity x
             props = [(Commutative          ,Yes    ), (IsGroup,No),
                      (IsMaxSubsemigroup    ,No     ),
                      (IsOrderedSubsemigroup,Unknown),  
                      (IsCyclicSemigroup    ,No     )   
                                      -- because 0,1 <- subsemigroup
                     ]
        in   Subsemigroup {subsmgType    = Mul,   
                           subsmgUnity   = Just (Just unR),
                           subsmgGens    = Nothing,  -- so far
                           subsmgProps   = props,
                           subsmgConstrs = [],
                           subsmgOpers = []
                          }



--------------------------------------------------------------------
rseBaseAddGroup r dm =
                     case  (lkp dm AddGroup, dom r, resPIdeal r)  of

  (Just (D1Group g), _ , _ ) -> (dm, g)
  (_               , aD, iI) ->
    (case  (lkp aD AddGroup, pirCIBase iI, pirCIFactz iI)
     of
       (Nothing          , _, _ ) -> (dm, error $ msg1 msg)
       (Just (D1Group gA), b, ft) -> 
                                 ifCEuc_rse_ aD dm msg1 $ gr gA b ft
    )
  where
  msg1 = ("baseAddGroup r dom', \n"++)
         .("\nr = "++) .shows r .("\n <- D/I =  "++) .showsDomOf r
 
  msg  = "\n\nAddGroup  not found in  D\n"

  gr gA b ft = (addToFM dm' AddGroup $ D1Group g, g)
    where
    (dm',rSet) = baseSet r dm
    g          = 
      let
        zr     = zeroS b
        zeroR  = ct r zr
        canr x = remEuc 'c' x b

        (gens_gA,props_gA) = (subgrGens gA, subgrProps gA)

        props' = [(IsNormalSubgroup , Yes   ),
                  (IsMaxSubgroup    , No    ), 
                  (IsOrderedSubgroup, No    ),   -- so far            
                  (IsCyclicGroup    , cyc'  ),
                  (IsPrimeGroup     , prime')
                  ]
        cyc'   = case  lookup IsCyclicGroup props_gA  of
                                                 Just Yes -> Yes
                                                 _        -> Unknown
                                                           -- so far

        -- R/(b) is a prime group <==>
        --                            R/(b) is finite and b is prime
        -- For primality of  b  inspect the factorization from iI
        --
        prime' = case  (isFiniteSet rSet, ft)  
                 of
                   (No , _       ) -> No
                   (_  , []      ) -> Unknown 
                                            -- factorization skipped
                   (Yes, [(_,1)] ) -> Yes
                   (_  , [(_,1)] ) -> Unknown
                   _               -> No 

        gens' = case  (gens_gA, osetList rSet)  of
                                       -- optimizations possible ***
          (Just xs, _        ) -> 
               Just $ map (ct r) $ nub $ filter (/=zr) $ map canr xs

          (_      , Just ress) -> 
                 Just $ map (ct r) $ gensModulo $ map resRepr $ ress
                                        where 
                                        gensModulo xs = xs  --so far
          _                    -> Nothing
      in
      Subgroup {subgrType    = Add,              subgrGens  = gens', 
                subgrCanonic = Just (const zeroR),
                                    -- for base subgroup is full one
                subgrProps   = props',
                subgrConstrs = [],               subgrOpers = []
               }                           



--------------------------------------------------------------------
rseBaseRing r@(Rse a iI aD) dm = 
  case
      (lkp dm Ring, pirCIBase iI, pirCIFactz iI)
  of
    (Just (D1Ring rg), _, _ ) -> (dm, rg)
    (_               , b, ft) ->
      (case
           (lkp aD AddGroup, lkp aD Ring)
       of
        (Just (D1Group aG), Just (D1Ring aR)) ->
                              ifCEuc_rse_ aD dm msg1 $ br b ft aG aR
        _                                     ->
                                               (dm, error$ msg1 msg)
      )
      where
      msg1 = ("baseRing r dom', \n"++)
             .("\nr = "++) .shows r .("\n <- D/I =  "++) 
             .showsDomOf r
      msg  = "\n\nAddGroup or Ring not found in  D\n"

      br b ft aG aR = (addToFM dm' Ring $ D1Ring rg, rg)
        where
        (dm',rSet) = baseSet r dm 
        rg         =
         let
           (zr, un, un') = (zeroS a, unity a, unity r)
           canr x        = remEuc 'c' x b
           xG_gens       = subgrGens aG
           ---------------------------------------------------------
           char' = case  (xG_gens, subringChar aR)  of

             (Just [_], _      ) -> Just n     -- aR isomorphic to Z
                                         where Fin n = osetCard rSet
             (_       , Nothing) -> Nothing
             (_       , Just 0 ) -> Nothing                -- so far
             (_       , Just _ ) -> Just $ c (1::Z) $ canr un
               where
               c k sum = if  sum==zr  then  k    -- may be expensive
                         else               c (k+1) $ canr (sum+un)
                         -- better solution ? ***
           ---------------------------------------------------------
           props' = [(IsField      , bPrime     ), 
                     (HasZeroDiv   , not3 bPrime), 
                     (HasNilp      , hasNl      ),
                     (IsPrimaryRing, bPrimary   ),    
                     (Factorial    , bPrime     ), 
                     (PIR          , Yes        ),                     
                     (IsOrderedRing, Unknown    ),  -- so far
                     (IsRealField  , Unknown    ),  --
                     (IsGradedRing , Unknown    )    
                    ]
           bPrime   = case  ft  of  []      -> Unknown
                                    [(_,1)] -> Yes
                                    _       -> No    
           bPrimary = case  ft  of  []  -> Unknown
                                    [_] -> Yes
                                    _   -> No    
           hasNl = if  null ft  then  Unknown
                   else          boolToPropV $ any (/=1)$ map snd ft
           ---------------------------------------------------------
           -- In  opers',  DoCon is so far interested only in 
           -- finding when  R/(b)  contains a prime field, in 
           -- WithPrimeField  construct.
           -- If  R  is isomorphic to  Z  then, Lemma:
           --           if  b  is prime then R/(b) is a prime field,
           --           otherwise  R/(b)  does not contain a field.
           --
           -- Suppose now  R  is not isomorphic to  Z.
           -- If  dimOverPrime  yields a definite value for R, then 
           -- R  contains a prime field  k  inside.  And it should 
           -- hold  intersection(k,(b)) = {0}.  Hence R/(b) contains
           -- a copy of  k.
           -- But how do we find  dim( R/(b), k' )  ?
           -- Is it true that  R  is isomorphic to  k[x]  in this  
           -- case? 
           -- So far, we skip this case, minding that at least,
           -- ResidueE k[x]  will handle it.

           opers' = (case  (xG_gens, bPrime)
                     of
                       (Just [_], Yes) -> [(WithPrimeField,wp)]
                       _               -> []
                    )
                where                  -- R isomorphic to Z, b prime
                wp = WithPrimeField' 
                         {frobenius            = (id, Just .Just),
                          dimOverPrime         = Fin 1,
                          primeFieldToZ        = toz,
                          primeFieldToRational = undefined,
                          primitiveOverPrime   = 
                            ([un'], [(un',1),(-un',0)], \r->[(r,0)])
                         }
                toz r = fromJust $ find ((==r).times un') [0..]
                     --
                     -- This may be slow. There exist faster special
                     -- overlapping instances for ResidueE.
         in
         Subring {subringChar    = char', 
                  subringGens    = Nothing,   -- so far
                  subringProps   = props',
                  subringConstrs = [],   
                  subringOpers   = opers'
                 }                              

  ;













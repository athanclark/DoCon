------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Extended Polynomial  

-- is sometimes used as the representation of the 
-- Vector over Polynomials.




module  ExtPol  where

import  PreludeChar
import  PreludeList
import  PreludeInteger
import  Categ
import  Categ1
import  Generic
import  PP
import  Pol
import  UnvPol
import  Matrix  --?
import  IParse





type  EComp =  (Integer,PP) -> (Integer,PP) -> Comp

data  EPP   =  EPP Integer PP EComp

      -- Extended Power Product   (EPP n p cp)   consists of  the
      -- * Coordinate No        n = 0,1,2,...,
      -- * Usual power product  p = PP p0 cp0,
      -- * The comparison function  cp  to compare   (n,p)   with
      --   any other  (m,q).
      -- Thus  cp  has  the  coordinate No-s, 
      --                     integer vectors p0,q0 :: PowPr,
      --                     comparison  cp0  for  PowPr
      -- to compare EPP-s.

      -- Again, epp operations are valid only for the epp-s having
      -- the SAME comparison cp.



type  EMon a =  (a,EPP)

data  EPol a =  EPol [EMon a]    deriving (Eq,Text)    


    -- Example.
    -- Let         PV =  EPol Integer,   cp0 = degLex,
    -- and the extended comparison is  cp = eAntyLex_,
    -- eAntiLex_  (n,p) (m,q) =  
    --              case  compare p q  of
    --                      EQ -> (case  compare n m  of  EQ-> EQ
    --                                                    LT-> GT
    --                                                    GT-> LT
    --                            )
    --                      r  -> r

    -- This means that first are compared the proper parts,
    -- then, if equal, compared are the coordinate numbers:
    -- 0 > 1 > 2 ...  
    
    -- Then the vector  V = (5*x+4, 5*x^2*y+4*x, 4*y) 
    --        coordinate No  0      1            2
    -- can be converted to the type  PV:
    -- V ->
    -- (1, 5*x^2*y)+(0,5*x)+(1,4*x)+(2,4*y)+(0,4)  ->

    -- EPol [ (5, EPP 1 (PP [2,1]  degLex)  cp )
    --        (5, EPP 0 (PP [1]  ) degLex)  cp )
    --        (4, EPP 1 (PP [1]  ) degLex)  cp )
    --        (4, EPP 2 (PP [0,1]) degLex)  cp )
    --        (4, EPP 0 (PP []   ) degLex)  cp )
    --      ]
  


data  EVarPol c =  EVarP (EPol c) [String] 
                                  --vars

    -- Example:
    -- w  (EPol  [ (5, EPP 1 (PP [2,1] degLex) cp )
    --               (4, EPP 2 (PP [0,1] degLex) cp )
    --               (4, EPP 0 (PP []    degLex) cp )
    --             ],
    --        ["x","y"]
    --     )  ""                          ->    (4, 5*x^2*y, 4*y)



lmE  (EPol (m:ms)) =  m 
lmE  _             =  error "lmE (EPol [])" 

lcE  =  fst.lmE  
lppE =  snd.lmE  

                                 -- coordinate of Leading monomial
ePolCoord f =  i    where  (EPP i _ _ ) = lppE f 

ePolPP    f =  p    where  (EPP _ p _ ) = lppE f  
ePolCp    f =  cp   where  (EPP _ _ cp) = lppE f 

ePolDeg   f =  sum (ppP (ePolPP f))




------------------------------------------------------------------
instance  Eq EPP   where  (EPP n p cp)==(EPP m q _) = n==m && p==q
------------------------------------------------------------------

instance  Text EPP   -- ?




ePolNeg :: AddGroup a =>  EPol a -> EPol a

ePolNeg (EPol eMons) =  EPol  (map (\(a,p)-> (neg a, p)) eMons)



ePolAdd,ePolSub :: CommutativeRing a => EPol a -> EPol a -> EPol a

ePolAdd  (EPol [])          g          =  g
ePolAdd  (EPol ((a,p):fms)) (EPol gms) =  
                              EPol  (epa (zero a) ((a,p):fms) gms)
  where
  epa  _  []      gms     =  gms
  epa  _  fms     []      =  fms
  epa  zr (m:fms) (n:gms) =
    let (a,p) = m 
        (b,q) = n
        (EPP i p1 cp) = p
        (EPP j q1 _ ) = q
    in  
      case  cp (i,p1) (j,q1)   
      of
        GT ->  m:(epa zr fms (n:gms))  
        LT ->  n:(epa zr (m:fms) gms)
        _  ->  let  c = add a b  
               in          
                 if  c==zr  then  epa zr fms gms
                 else             (c,p):(epa zr fms gms)


ePolSub f g =  ePolAdd f (ePolNeg g)



eMonMul :: Ring c =>  c -> Mon c -> EMon c -> [EMon c]

eMonMul  zero (a,p) (b, EPP n q cp) =  let  c = mul a b  in  

  if  c==zero  then  []   else   [ ( c, EPP n (add p q) cp) ]



mEPolMul :: Ring c =>  Mon c -> EPol c -> EPol c

mEPolMul  (a,p) (EPol mons) =  EPol (mpm (zero a) mons)  
  where
  mpm _ []     = []
  mpm z (n:ms) = (eMonMul z (a,p) n)++(mpm z ms)

polEPolMul  f g =  pem  f (EPol [])
  where 
  pem  (Pol []) sum =  sum
  pem  f        sum =  
                 pem (polTail f) (ePolAdd sum (mEPolMul (lm f) g))


cEPolMul ::  Ring c =>  c -> EPol c -> EPol c 

cEPolMul  c (EPol ms)  =  EPol (cpm (zero c) ms)  
  where
  cpm _ []         =  []
  cpm z ((a,p):ms) =  let  b= mul c a  
                      in 
                        if  b==z  then  cpm z ms
                        else            (b,p):(cpm z ms)

------------------------------------------------------------------
ePolCoefDiv :: Ring c =>  EPol c -> c -> [EPol c]

ePolCoefDiv  (EPol mons) c  =  
  let
    cQuotsPar =  map (\a-> divide_l a c) (map fst mons)
  in
    if  any null cQuotsPar  then  []  
    else     
      [ EPol  (zip (map head cQuotsPar) (map snd mons)) ]
------------------------------------------------------------------

ePolTimes:: Ring c => EPol c -> Integer -> EPol c

ePolTimes  (EPol []) _ =  EPol []
ePolTimes  (EPol ms) n =  EPol (tm  (zero (lcE (EPol ms)))  ms)
  where
  tm  _ []        =  []
  tm  z ((a,p):f) =  let  b = times a n  in  if b==z then  tm z f
                                             else   (b,p):(tm z f)
------------------------------------------------------------------

ePolToPol1 :: CommutativeRing a =>  EPol a -> Pol1 (Pol a)
 
                            -- Convert e-polynomial over  a  to 
                            -- univariate polynomial over  Pol a.  

ePolToPol1  (EPol ms) =  es  (Pol1 []) ms 
  where
  es  f1 []                   =  f1 
  es  f1 ((a, EPP n p cp):ms) =  
    let 
      monOverPol= (Pol [(a,p)], n)
                             -- the coordinate No n = 0,.. becomes
                             -- a degree of unvariate monomial
    in
      es  (pol1Add (Pol1 [monOverPol]) f1) ms
------------------------------------------------------------------

pol1ToEPol :: EComp -> Pol1 (Pol a) -> EPol a

        -- Inverse to  ePolToPol1.
        -- i-th  coordinate   fi   belongs  to   Pol a.      Make 
        -- e-monomials  (cij, EPP i pi cp)  from each monomial of
        -- f   and concatenate these lists,  sorting  e-monomials
        -- under the comparison  cp.

pol1ToEPol  cp (Pol1 mons1) = 
  let
    less  (_, EPP i p cp) (_, EPP j q _) =  (cp (j,q) (i,p))==LT
    merge = mergeP less   
    sort  = sortP  less   

    extMons i mons =  map (\(c,p)-> (c, EPP i p cp)) mons

    ep  []               =  []
    ep  ((Pol ms,i):ms1) =  merge (sort (extMons i ms)) (ep ms1)
  in 
    EPol (ep mons1)
------------------------------------------------------------------

ePolToVector :: CommutativeRing a =>  Integer -> EPol a -> [Pol a]
                                      -- n
              -- convert E-polynomial over to Polynomial Vector.
              -- n  is the length of vector. Zero polynomials are
              --    prepended to vector to  make  its  length  n.
              --    n=0  means nothing to prepend.

ePolToVector  n f =  pol1ToVector  (Pol []) n (ePolToPol1 f)
------------------------------------------------------------------

vectorToEPol :: CommutativeRing a =>  EComp -> [Pol a] -> EPol a

vectorToEPol  cp v =  pol1ToEPol cp (vectorToPol1 v)
------------------------------------------------------------------

  -- S-polynomial for Non-zero e-Polynomials over a Euclidean Ring

sEPol :: SyzygySolvableRing a => 
                    EPol a -> EPol a -> [ (EPol a, Mon a, Mon a) ]

                     -- returns [],     if the coordinates differ,
                     --         [(s-ePol,m1,m2)]  otherwise
sEPol f g =  
    if  (ePolCoord f)/=(ePolCoord g)  then  []
    else
      let 
        a         = lcE f                        
        b         = lcE g 
        (_,m1,m2) = sPol (Pol [(a,ePolPP f)]) (Pol [(b,ePolPP g)])
      in          
        [ (ePolSub (mEPolMul m1 f) (mEPolMul m2 g), m1, m2) ]






---------------------------  Set  --------------------------------

instance  Ring a =>  Set (EPol a)   where

  card _ =  [[]]

  setTerm f = 
     (setDomFuncs  (funcNames "set")  
       (setDomCons  (EPolynomial (ringTerm (lcE f)) [])  
                    trivialDomain
     ))

  w (EPol mons) = (w "(EPol ").(shows (map cutPP mons)).(w " )")
                      where 
                      cutPP (c, EPP n p _) =  (c, "EPP", n, ppP p)

  --fromExpr =
  




------------------------  AddGroup  ------------------------------


instance  CommutativeRing a =>  AddSemigroup (EPol a)   where

  addSmgTerm f = 

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+",cyclicAdd f),("gr+",groupAdd f),
           ("ord+",ordAdd f)
         ]
         (setDomCons  (EPolynomial (ringTerm (lcE f)) []) 
                      trivialDomain
    ) )  )

  cyclicAdd _ =  No
  groupAdd  _ =  Yes
  ordAdd    _ =  No

  add         =  ePolAdd
  zero _      =  EPol []
  zero_l  _   =  [EPol []]
  neg         =  ePolNeg
  neg_l   f   =  [ePolNeg f]
  sub_l   f g =  [ePolSub f g]
  times_l f n =  [ePolTimes f n]

instance  CommutativeRing a =>  AddMonoid (EPol a)
instance  CommutativeRing a =>  AddGroup  (EPol a)
------------------------------------------------------------------

instance  CommutativeRing a =>  Num (EPol a)   where
  negate = neg
  (+)    = add
  (-)    = sub  





------------------  Module over  Pol c  --------------------------
        
{-

instance  Ring c =>  ModuleOver (EPol c) (Pol c)
  where  

               -- this is the first non-trivial module instance

  moduleTerm ef g =  let  c = lcE ef   in

    (setDomFuncs  (funcNames "module")            -- ? ?  
      (setDomProps
         [ 

         ]
         (setDomCons (EPolynomial (ringTerm c) []) trivialDomain)
    ) )
  ---------------------------------------------------------------
  syzygySolvable_m  _ f =  syzygySolvable  f
  hasGrBas_m        _ f =  hasGrBas        f
  moduloIsCanonic_m _ f =  moduloIsCanonic f 

  cMul = polEPolMul 





{-
************


instance  SyzygySolvableRing c =>  
                             SyzygySolvableModule (EPol c) (Pol c)
  where  

  canInv_m  EPol [] _  =  error "canInv_m (EPol []) _"  
  canInv_m  f       _  =  let  cp = ppCp (ePolPP f)
                          in    
                            Pol [(canInv (lcE f), PP [] cp)]

  canAssoc_m  EPol [] _  =  EPol []
  canAssoc_m  f       _  =  cEPolMul  (inv (canInv (lcE f)))  f


  --grBasis_m :: String -> [EPol c] -> ([EPol c], Matrix (Pol c))
{-
  grBasis_m _    []      =  ( [], Mt [] )
  grBasis_m _    ([]:fs) =  error  "grBasis_m [ [] ... ] "
  grBasis_m mode (f:fs)  =  let  c = lc f  in

    case  (euclidean c, field c)  
    of
      (_  , Yes) ->  grBas_e_field mode (f:fs)
                       where  
                       grBas_e_field _ _ = 
                                      error "define grBas_e_field"

      (Yes, _  ) ->  grBas_e_euc mode (f:fs)
                       where  
                       grBas_e_euc _ _= error "define grBas_e_euc"
      _          ->  
            error ( "grBasis_m_q _ [ " ++ (w f) ++ " ... ]" ++
                    "  coefficients should be from Euclidean ring"
                  )               
-}




  --moduloBasis_m :: 
  --             String -> [EPol c] -> EPol c -> (EPol c, [Pol c])
  --             modes     fs          f
  --                                       modes = ""|"c"|"g"|"cg"

{-
  moduloBasis_m _ _     _  [] =  []
  moduloBasis_m _ modes fs f  =  let  c = lc f  in
               
    case  (field c, euclidean c, modes)
    of
      (_  , Yes, "g" ) ->  polNF_e ""  fs f 
      (_  , Yes, "cg") ->  polNF_e "r" fs f
      (Yes, _  , ""  ) ->  polNF_e ""  (grBas_e_field ""  fs) f
      (Yes, _  , "c" ) ->  polNF_e "r" (grBas_e_field "r" fs) f
      (_  , Yes, ""  ) ->  polNF_e ""  (grBas_e_euc   ""  fs) f
      (_  , Yes, "c" ) ->  polNF_e "r" (grBas_e_euc   "r" fs) f
      _                ->
                       -- case  domCons (ringTerm c)  of

         error ("moduloBasis_m _ _ _ "++(w f)++
            "  for non-Euclidean"++
            "coefficients DoCon will need to see construction ..."
               )


  moduloBasis_q _     fs [] =  ( [], map (const []) [] )
  moduloBasis_q modes fs f  =  
    let  c = lc f  
    in
      case  (euclidean c, modes)
      of
        (Yes, "g"   ) -> polNF_q ""  fs f
        (Yes, "cg"  ) -> polNF_q "r" fs f
        (Yes, c_mode) -> 
          let 
            rM = (case  c_mode  of  
                   ""  ->  ""
                   "c" ->  "r"
                   _   ->  error( "moduloBasis_q:  modes should "
                                 ++ "be \"\" or \"c\", or \"cg\" "
                                )
                 )
            (gs,m) = if (field c)==Yes then  grBas_field_q rM fs
                     else                    grBas_euc_q   rM fs
            (r ,q) = polNF_q rM gs f
          in         
            (r, rowMatrMul q m)
                            --     where  rowMatrMul _ _ =
                              --        error "no rowMatrMul so far"

        _          ->
                       -- case  domCons (ringTerm c)  of

         error ("moduloBasis_q _ _ "++(w f)++"  for non-Euclidean"++
            "coefficients DoCon will need to see construction ..."
               )

-}


  -- syzygyBasis 


-}



------------------------------------------------------------------


polNF_e ::  SyzygySolvableRing c =>
                            String -> [EPol c] -> EPol c -> EPol c


    -- As  polNF,  only the power products are Extended;  hence
    -- the coordinate No-s have to be compared in certain moment.


polNF_e "r" gs f =  reverse  (nr [] (polNF_e "" gs f))   where
                      nr r []    =  r
                      nr r (m:f) =  nr (m:r) (polNF_e "" gs f)

polNF_e ""  gs f =  nf  gs f gs  where

  nf  gs      [] _      =  [] 
  nf  []      f  _      =  f 
  nf  ([]:gs) f  _      =  error "(polNF_e _ gs)  zero among gs"
  nf  (g :gs) f  gsCopy =
    let
      a = lc  f
      p = lpp f
      (EPP i p0 cp) = p
    in
      if  i /= (ePolCoord g)  then  nf gs f gsCopy
      else 
        let  dp = sub p0 (ePolPP g)
        in
          if  any (<0) (ppP dp)  then  nf gs f gsCopy
          else                         
            let  [qt,a1] = divRem "m" a (lc g)  
                 norm    = (eucNorm a )
                 norm1   = (eucNorm a1)  
            in
              if a1==(zero a1) then   --monomial divided presizely
                 nf gsCopy
                    (ePolSub (tail f) (mEPolMul (qt,dp) (tail g)))
                    gsCopy
              else                      
                (case  compare norm1 norm  of

                  GT -> error ( ((w "TEST  divRem m ").
                                 (w a).(' ':).(w (lc g)) )  ""
                              )
                  EQ -> nf gs f gsCopy   --pp divided, but 
                                         --coefficient not reduced
                  _  -> nf  gs 
                            ( (a1,p) : 
                              (ePolSub  (tail f) 
                                    (mEPolMul (qt,dp) (tail g))
                              )
                            )
                            gsCopy    
                               -- lc became smaller, apply next g
                )




------------------------------------------------------------------

grBas_e_field :: SyzygySolvableRing a =>
                                    String -> [EPol a] -> [EPol a]



   -- Groebner basis  for Non-zero E-polynomials over a Field  a.

   -- This actually provides Groebner basis for the module of po-
   -- lynomial vectors over the polynomial ring  Pol a.

   -- The method is as in   grBas_field  with the two exceptions:

   -- 1. If  (EPP i p cp) = lpp f    (EPP j q cp) = lpp g  
   --    and   i /= j,  
   --    then No critical pair for  f,g  has to be formed;
   -- 2. Mutually-prime-power-products  criterion is skipped 
   --    (because it is incorrect for e-polynomials).
   -- In the critical pairs  (gij,pp)   pp  is as in  polynomial
   -- case.


grBas_e_field  mode fs  =  
  let
    --------------------------------------------------------------
    cnAs [] = []
    cnAs f  = let  a = lc f  in  if a==(unity a) then  f
                                 else           cEPolMul (inv a) f

    insertEPol  fs g =  ins  fs (ePolDeg g)
      where 
      ins []     d =  [g]
      ins (f:fs) d =  if  (ePolDeg f) < d  then  f:(ins fs d)
                      else                       g:f:fs
    insertEPols  fs []     =  fs 
    insertEPols  fs (g:gs) =  insertEPols (insertEPol fs g) gs

                                   -- insert critical pair (g,pp)
    insertPair  prs (f,p) =  ins  prs (sum p)
      where 
      ins []          d =  [(f,p)]
      ins ((g,q):prs) d =  if  (sum q)<d  then  (g,q):(ins prs d)
                           else                 (f,p):(g,q):prs

    insertRow  rows (f,cs) =  ins  rows (ePolDeg f)
      where 
      ins []           d =  [(f,cs)]
      ins ((g,cs1):rs) d = 
                     if  (ePolDeg g) < d  then  (g,cs1):(ins rs d)
                     else                       (f,cs):(g,cs1):rs
    mergeEPolLists fs gs =  
                 mergeP  (\ f g -> (ePolDeg f)<(ePolDeg g))  fs gs


                        -- reduce fs with h and insert h in result
    reduceIns  fs [] =  fs  
    reduceIns  fs h  =  insertEPol fs h      -- SO FAR 
      {-
        reduceIns  fs h =  rdi  fs []
          where
          rdi  []     gs =  insertEPol gs h
          rdi  (f:fs) gs =  case  cnAs (polNF_e "" [h] f)
                            of       []-> rdi fs gs
                                     r -> rdi fs (insertEPol gs r)
      -}
    reduceInsRepeat  fs []     =  fs 
    reduceInsRepeat  fs (g:gs) =  
                               reduceInsRepeat (reduceIns fs g) gs
    --------------------------------------------------------------

         -- b_criterion  rows singles gs p k  -> 
         --                            (newRows,newSingles,gew_gs)

         -- Is as in polynomial case, only it has additional argu-
         -- ment  k  and it does not touch  pairs  of  coordinates 
         -- different from k.

         -- Deletes from  rows  all the critical pairs (f,t_g_f) 
         -- such that   the power product  p  divides t_g_f  
         --             and  t_p_f /= t_g_f /= t_p_g.
         -- If a row turns to singleton  (f,[]),  then it is remo-
         -- ved, and f joins `singles', gs

    b_criterion  rows sgs gs p0 k0 = 
      let
        singleton (_,crits) =  null crits

        remains t_f_h (g,t) = 
          if  (ePolCoord g) /= k0  then  True
          else
            let  d = sub t p0 
            in       
              (any (<0) d)  ||  (all (==0) d)  ||  t_f_h==t  ||
              ((ppLcm p0 (ppP (ePolPP g))) == t)
         
        makeRow (f,crits) = let  t_f_h = ppLcm p0 (ppP (ePolPP f))
                            in 
                                 (f, filter (remains t_f_h) crits)
        newRows =  map makeRow rows

        moreSingles =  map  fst  (filter singleton newRows)
        moreSgs     =  map  (cnAs.(polNF_e "" gs))  moreSingles

      in
        ( filter (not.singleton) newRows, 
          insertEPols sgs moreSingles,
          reduceInsRepeat gs moreSgs
        )
    --------------------------------------------------------------

                     -- critical pair list for new ePolynomial  h.
                     -- Any  g  of different (to h)  leading coor-
                     -- dinate does Not make critcal pair.
    critsForNew  rows singles h =
      let 
        k = ePolCoord h 
        p = ppP (ePolPP h)   
      in                     ncr  k p (singles++(map fst rows)) []
        where
          -- critical pairs  cs= [(g1,t_g1_h)..(g2,t_gi2h)..]  for
          -- h  are accumulated.  Also  cs  if filtered by  M-, F-
          -- criterions.
          -- * current  t_g_h  is skipped if it is a  multiple  of
          --   some previous  t  from  cs,
          -- * otherwise t_g_h  filters out its multiples from the
          --   the previous  cs 

        ncr  _ _ []     cs =  cs
        ncr  k p (g:gs) cs =  
          if  k/=(ePolCoord g)  then   ncr  k p gs cs
          else
            let  q     = ppP (ePolPP g)
                 t_g_h = ppLcm p q           --t(i,v+1) from paper
            in
              if  any (\q->ppDivides q t_g_h) (map snd cs)  
                                               then  ncr k p gs cs
              else 
                let 
                  cs1= [(f,q)| (f,q)<-cs, not (ppDivides t_g_h q)]
                in
                  ncr  k p gs (insertPair cs1 (g,t_g_h))
    --------------------------------------------------------------

                             -- initiate fs -> (rows,singles,gs0)

    initiate [f]    =   ( [], [f], [f] )
    initiate (f:fs) = 
      let 
        (rows,singles,gs) =  initiate fs
        f_crits           =  critsForNew rows singles f
        (newRows,newSingles,newGs) =
              b_criterion 
                    rows singles gs (ppP (ePolPP f)) (ePolCoord f)
      in
        if null f_crits then 
                (newRows, insertEPol singles f, 
                       reduceIns newGs (cnAs (polNF_e "" newGs f)) 
                )
        else       (insertRow newRows (f,f_crits), singles, newGs)
    --------------------------------------------------------------

                       -- redTout mode fs  -->  fsReduced    
                       -- Reduces  fi  from  fs  w.r.to each other
    redTout mode fs =  redt  [] fs   where
      redt  rs []     =  rs                      --
      redt  rs (f:fs) =  case  cnAs (polNF_e mode (rs++fs) f)  
                         of                    []-> redt rs     fs
                                               r -> redt (r:rs) fs
    --------------------------------------------------------------

                       -- Main loop.  Process the critical pairs 
                       -- from  rows  until  rows  is empty

    prPairs  []         _       gs =  gs
    prPairs  (row:rows) singles gs =  
      let
        (fi, (fj,tij):row1) =  row  
        h                   =  cnAs (polNF_e "" gs (sEPol fi fj)) 
      in
        case  (h,row1)  
        of
          ([], []) ->  prPairs  rows (insertEPol singles fi) 
                          (reduceIns gs (cnAs (polNF_e "" gs fi)))

          ([], _ ) ->  prPairs  ((fi,row1):rows) singles gs
          (h , _ ) -> 
            let  
              gs1     = reduceIns gs h
              h_crits = critsForNew (row:rows) singles h
              (newRows,newSingles,new_gs) = 
                       b_criterion  ((fi,row1):rows) singles gs1 
                                    (ppP (ePolPP h)) (ePolCoord h)
            in
              if  null h_crits  then     
                  prPairs newRows (insertEPol newSingles h) new_gs
              else   
                  prPairs  (insertRow newRows (h,h_crits)) 
                                                 newSingles new_gs
    --------------------------------------------------------------

  in                             -- grBas_e_field   itself starts 

    (case  filter (not.null) (map cnAs fs)  of

      []  ->  []
      [f] ->  [f]
      _   ->  let  (rows,singles,gs0) =  initiate fs    
                   gs                 =  prPairs rows singles gs0
              in
                   if  mode==""  then  gs   else  redTout "r" gs
    )

------------------------------------------------------------------




grBas_e_euc  _ _  =  error "no  grBas_e_euc  so far"



-- grBas_field_e_q  rM fs =  error "no  grBas_field_q  so far"



*****************
-}

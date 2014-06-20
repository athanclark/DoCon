------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- Groebner basis





module  GrBas ( grBas )   where

import  PreludeInteger
import  Generic
import  Categ
import  Categ1
import  Matrix
import  PP
import  Pol
import  NF
import  IParse  --?




grBas  mode coefProp  fs =

   if  (mode/="")&&(mode/="r")  then
                           error( "(grBas mode prop fs):  " ++
                                  " mode should be  \"\" | \"r\" "
                                )
   else
     case  fs 
     of
       []            ->  ([], Mt [])
       ((Pol []):fs) ->  error "(grBas _ _ fs):   zero among  fs "
       (f :fs) -> 
         let
           c        =  lc f
           unityPol =  cToPol (zero c) (ppCp (lpp f)) (unity c)
           fvs      =  initVectors (Pol []) unityPol (f:fs) 
           gvs      = 
             (case  coefProp  of  "field" ->  grBas_field mode fvs
                                  "euc"   ->  grBas_euc   mode fvs 
                                  -- more cases ?
             )
         in 
           ( map fst gvs,  Mt (map snd gvs) )

------------------------------------------------------------------





grBas_field ::  (SyzygySolvableRing a, Num a)
                =>
                String -> [VecPol a] -> [VecPol a]
             -- mode      fs            gs
        



-- Groebner basis  for  Non-zero Vec-polynomials over a  Field  a.

-- Vector parts are used only  to  accumulate  the  transformation 
-- matrix from initial basis.  Operations on the vector parts  are 
-- "parallel" (with the same coeficients) to ones on polynomials.

-- The core method is taken from  H.M.Moeller:  
-- "On the  Construction of Groebner Bases Using Syzygies",  
-- Journal of Symbolic Computation (1988), Vol. 6. 

-- IGNORING the Vector parts, the methog is the following.

--    The Critical Pairs   pps   are  organized  into   rows  =
-- [row1,row2,..],    each row corresponds to certain  f  from the
-- current basis  fS = [f1..fm],

-- row = ( f,  [(g1, t_g1_f)..(gk,t_gk_f)] ),  
--                            where t_f_g = ppLcm (lpp f) (lpp g).

-- The symmetric duplicates (f,t_f_g) for  (f,t_g_f)  are skipped.

-- Some critical pairs may be removed in the process.
-- As the row turns to singleton (f,[]),  it is deleted, and  f is
-- is iserted into `singles' list.

-- Ordering: 
--   Critical pairs  (fj,tij)  keep ordered so that the  pairs  of
-- smaller  totalDeg(tij)  go in the head.
--   The Rows  (f,crits)  of smaller  totalDeg(f)  are kept in the
-- head.
--   Similar are the polynomials in the `singles' list.  This  has 
-- the aim of the smaller objects to be reduced first  (and to  be
-- used earlier for reducing of other objects).
--   This ordering is supported by the local functions below:
--           insert, insertPair, insertRow, merge.
-- See more comments in  prPairs  function.

   



grBas_field  mode fs  =  
  let
    --------------------------------------------------------------
    cnAs (Pol [], fs) =  (Pol [], fs)
    cnAs (f     , fs) =  let  a = lc f  in 

      if  a==(unity a)  then  (f,fs)
      else                let  ai = inv a
                          in   (cPolMul ai f, map (cPolMul ai) fs)

                              -- insert vec-polynomial:  
                              -- polynomials of smaller total 
                              -- degree go to the head of the list
    insert  fs g =  ins  fs (totalDeg (fst g))
      where 
      ins []     d =  [g]
      ins (f:fs) d =  if  (totalDeg (fst f))<d  then  f:(ins fs d)
                      else                            g:f:fs

    insertMany fs []    =  fs 
    insertMany fs (g:gs)=  insertMany (insert fs g) gs

                        -- insert critical pair  (f,pp):
                        -- ones of smaller totalDeg(pp) go to head
    insertPair  prs (f,p) =  ins  prs (sum p)
      where 
      ins []          d =  [(f,p)]
      ins ((g,q):prs) d =  if  (sum q)<d  then  (g,q):(ins prs d)
                           else                 (f,p):(g,q):prs

                         -- insert row  (f,crits):
                         -- rows of smaller totalDeg(f) go to head
    insertRow  rows (f,cs) =  ins  rows (totalDeg (fst f))
      where 
      ins []           d =  [(f,cs)]
      ins ((g,cs1):rs) d = 
              if  (totalDeg (fst g)) < d  then  (g,cs1):(ins rs d)
              else                              (f,cs):(g,cs1):rs

    merge fs gs =  
        mergeP  (\ f g -> (totalDeg (fst f)) < (totalDeg (fst g))) 
                fs  gs

                        -- reduce fs with h and insert h in result
    reduceIns  fs (Pol [],_) =  fs  
    reduceIns  fs h          =  insert fs h    -- SO FAR

     {-
           rdi  fs []           ********  WHY this is incorrect ?          
        where
        rdi  []     gs =  insert gs h
        rdi  (f:fs) gs =  case  cnAs (polNF_v "" [h] f)
                          of     
                            (Pol [], _) ->  rdi fs gs
                            r           ->  rdi fs (insert gs r)
     -}

    reduceInsMany  fs []     =  fs 
    reduceInsMany  fs (g:gs) =  reduceInsMany (reduceIns fs g) gs
    --------------------------------------------------------------

         -- b_criterion  rows singles gs p  -> 
         --                            (newRows,newSingles,gew_gs)

         -- deletes from  rows  all the critical pairs (f,t_g_f) 
         -- such that   the power product  p  divides t_g_f  
         --             and  t_p_f /= t_g_f /= t_p_g.
         -- If a row turns to singleton  (f,[]),  then it is remo-
         -- ved, and f joins `singles', gs

    b_criterion  rows sgs gs p = 
      let
        singleton (_,crits) =  null crits

        remains t_f_h (g,t) = 
          let 
            d = sub t p 
          in       
            (any (<0) d)  ||  (all (==0) d)  ||  t_f_h==t  ||
            ((ppLcm p (ppP (lpp (fst g)))) == t)
         
        makeRow (f,crits) =
          let  t_f_h = ppLcm p (ppP (lpp (fst f)))
          in                     (f, filter (remains t_f_h) crits)

        newRows =  map makeRow rows

        moreSingles =  map  fst  (filter singleton newRows)
        moreSgs     =  map  (cnAs.(polNF_v "" gs))  moreSingles
      in
        ( filter (not.singleton) newRows, 
          insertMany  sgs moreSingles,
          reduceInsMany  gs moreSgs
        )
    --------------------------------------------------------------
                       -- critical pair list for new polynomial  h
    critsForNew  rows singles h =
      let 
         p = ppP (lpp h)  
      in                   ncr p (singles++(map fst rows)) []
        where

          -- critical pairs  cs= [(g1,t_g1_h)..(g2,t_gi2h)..]  for
          -- h  are accumulated.  Also  cs  if filtered by  
          -- mutPrime- , M- , F-  criterions - see the paper on M,
          -- F-criterions.

          -- * mutPrime(g,h)  criterion
          --             (from widely known B.Buchberger's work) :
          --   t_g_h  is skipped if
          --          lpp g  and  lpp h   are  mutually prime.

          --   *** This criterion is NOT Valid for  the  Vectors -
          --   *** i.e. for the grBasis variant  for  the  modules
          --   *** over the polynomial ring.
          
          -- For this  newCrits  finction,   M-, F-  criterions ::
          -- (cs, t_g_h) -> new_cs   simply mean that

          -- * current  t_g_h  is skipped if it is a  multiple  of
          --   some previous  t  from  cs,
          -- * otherwise t_g_h  filters out its multiples from the
          --   the previous  cs 

        ncr  _ []     cs =  cs
        ncr  p (g:gs) cs =  
          let
            q = ppP (lpp (fst g))
          in
            if  ppMutPrime p q  then   ncr p gs cs
            else 
              let  t_g_h = ppLcm p q  
              in
                if  any (\q->ppDivides q t_g_h) (map snd cs)  
                                                 then  ncr p gs cs
                else 
                  let cs1 =  
                       [(f,q)| (f,q)<-cs, not (ppDivides t_g_h q)]
                  in
                      ncr  p gs (insertPair cs1 (g,t_g_h))
    --------------------------------------------------------------

                              -- initiate fs -> (rows,singles,gs0)
    initiate [f]    =  ( [], [f], [f] )
    initiate (f:fs) = 
      let 
        (rows,singles,gs) =  initiate fs
        f_crits           =  critsForNew rows singles (fst f)
        (newRows,newSingles,newGs) =
                  b_criterion  rows singles gs (ppP (lpp (fst f)))
      in
        if null f_crits then 
               (newRows,  insert singles f, 
                       reduceIns newGs (cnAs (polNF_v "" newGs f)) 
               )
        else       (insertRow newRows (f,f_crits), singles, newGs)
    --------------------------------------------------------------

   {-  RESERVE       -- if  f  is from the Groebner basis  fs  and
                     -- lpp(f)  is reducible,  then  fs\{f}  is  a
                     -- Groebner basis for the same ideal.
    delRedexes []     = [] 
    delRedexes (f:fs) = 
      let  p   = ppP (lpp f)
           fs1 = delRedexes 
                    [ g | g<-fs, not (ppDivides p (ppP (lpp g))) ]
      in
         if  any (\g-> ppDivides (ppP (lpp g)) p) fs1  then  fs1
         else                                                f:fs1
   -}

                              -- redTout mode fs  ->  fsReduced    
                              -- Reduces fi from w.r.to each other
    redTout mode fs =  redt  [] fs   where
      redt  rs []     =  rs                      --
      redt  rs (f:fs) =  
        case  cnAs (polNF_v mode (rs++fs) f)  of
                                     (Pol [], _) -> redt rs     fs
                                     r           -> redt (r:rs) fs
    --------------------------------------------------------------

       -- Main loop.  Process the critical pairs from  rows  until
       -- rows  is empty.   gs  turns a Groebner basis in the end.
       -- It copies  singles  except that  gi  are being  mutually
       -- reduced now and then.

    prPairs  []         _       gs =  gs
    prPairs  (row:rows) singles gs =  
      let
        (fi, (fj,tij):row1) =  row  
        (h1,_,_)            =  sVecPol fi fj
        h                   =  cnAs (polNF_v "" gs h1)
      in
        case  (h,row1)  
        of
          ((Pol [],_), []) ->
                              --trivial pair and new singleton row
                 prPairs  rows (insert singles fi) 
                          (reduceIns gs (cnAs (polNF_v "" gs fi)))
          
          ((Pol [],_), _ ) -> prPairs  ((fi,row1):rows) singles gs
                                                   -- to next pair
          ((h,hs)    , _ ) -> 
            let  
              gs1     = reduceIns gs (h,hs)
              h_crits = critsForNew (row:rows) singles h
              (newRows,newSingles,new_gs) = 
                    b_criterion 
                        ((fi,row1):rows) singles gs1 (ppP (lpp h))
            in
              if  null h_crits  then     
                         prPairs newRows 
                                 (insert newSingles (h,hs)) new_gs
              else   
                   prPairs (insertRow newRows ((h,hs),h_crits)) 
                                                 newSingles new_gs
    --------------------------------------------------------------

  in                                -- grBas_field   itself starts 

{-
    (case   redTout "" (map cnAs fs)   of
      []  ->  []
      [f] ->  [f]
      fs  ->  let  (rows,singles,gs0) = initiate fs    
              in
                redTout mode (prPairs rows singles gs0)
    )
-}


           -- This will work when  reduce & insert  become correct.

    (case  filter (not.isZeroPol.fst) (map cnAs fs)  of

      []  ->  []
      [f] ->  [f]
      fs  ->  let  (rows,singles,gs0) =  initiate fs    
                   gs                 =  prPairs rows singles gs0
              in
                   if  mode==""  then  gs   else  redTout "r" gs
    )


------------------------------------------------------------------





grBas_euc  mode fs  =  error "no  grBas_v_euc_q  so far"



{-
******  To be developed : *********


grBas_euc ::  (SyzygySolvableRing a, Num a)
              =>
              String -> [Pol a] -> [Pol a]


   -- Groebner basis  for Non-zero polynomials over a 
   -- Euclidean ring  a.

   -- The core method is taken from  H.M.Moeller:  
   -- "On the  Construction of Groebner Bases Using Syzygies",  
   -- Journal of Symbolic Computation (1988), Vol. 6. 

   -- SEE FIRST THE FIELD CASE in  grBas_field.

   -- Here is where the method differs from the one of the 
   -- Field case.

   -- row = ( f,  [(g1, t_g1_f)..(gk,t_gk_f)] ),  
   --                          where t_f_g = monLcm (lm f) (lm g).

   --   The Completion  cfS = c fS   is computed through the  ex-
   -- tended GCD function on  R  (see the Moeller's paper).  This 
   -- reduces the Weak Groebner basis construction to the  Strong
   -- one i.e. the  Normal Forms are computed Strongly w.r. to 
   -- c(fS)  as it is done in the case  field(R).

   -- We represent  cfS  as   (pp1,g1),...,(ppl,gl),   were   ppi 
   -- are All the Divisors of the power product 
   -- lcm [lpp f1,...,lpp fm],   and  gi is the corresponding po-
   -- lynomial for the set 
   --    ppDivs(fS,ppi) =  {f from fS: lpp(f) divides ppi} 


grBas_euc  mode fS  =  
  let
    --------------------------------------------------------------
    cancelLastZeroes xs = reverse (dropWhile (==0) (reverse xs))

                    -- decrement last power cancelling last zeroes
    decr []     = [] 
    decr [1]    = []
    decr [n]    = [n-1]
    decr (n:ns) = case  n:(decr ns)  of  [0] -> []
                                         ms  -> ms

    butLastLast []     = 
             error "grBas_euc...newCompletion...(butLastLast []) "
    butLastLast [x]    = ([],x)
    butLastLast (x:xs) = let  (bl,y)= butLastLast xs  in  (x:bl,y)

    ppLcmL ps = pl ps []   where  pl []     r = r
                                  pl (p:ps) r = pl ps (ppLcm r p)


    monDivides (a,p) (b,q) =       -- monomial (a,p) divides (b,q)

      all (>=0) (powPr (sub q p))  &&  not (null (divide_l b a))

    --------------------------------------------------------------

       -- ***********
       -- Sadly, these  "inserts-s"  repeat the Field case.
       -- HUGS needs Modularity is needed.
       -- ***********

    insertPol  fs g =  ins  fs (totalDeg g)
      where 
      ins []     d =  [g]
      ins (f:fs) d =  if  (totalDeg f) < d  then  f:(ins fs d)
                      else                        g:f:fs

    insertPols  fs []     =  fs 
    insertPols  fs (g:gs) =  insertPols (insertPol fs g) gs

    insertPair  prs (f,m) =  ins  prs (totalDeg [m])
      where 
      ins []          d =  [(f,m)]
      ins ((g,n):prs) d = 
                   if  (totalDeg [n]) < d  then  (g,n):(ins prs d)
                   else                          (f,m):(g,n):prs

    insertRow  rows (f,cs) =  ins  rows (totalDeg f)
      where 
      ins []           d =  [(f,cs)]
      ins ((g,cs1):rs) d = 
                    if  (totalDeg g) < d  then  (g,cs1):(ins rs d)
                    else                        (f,cs):(g,cs1):rs

    mergePolLists =  mergeP (\ f g -> (totalDeg f)<(totalDeg g))
 
    --------------------------------------------------------------

    redTout mode fs =  redt  [] fs   where
      redt  rs []     =  rs                      --
      redt  rs (f:fs) =  case  (polNF mode (rs++fs) f)  
                         of                    []-> redt rs     fs
                                               r -> redt (r:rs) fs
    --------------------------------------------------------------
    complete :: 
              (SyzygySolvableRing a, Num a, PP pp, Ring(Pol a pp))
              =>
              [Pol a pp] -> [ (PowPr, Pol a pp) ] 

    complete (f:fs) = 
                let  pf = powPr (lpp f)  in   compl fs [(pf,f)] pf
      where
      compl  []     cs _   =  cs
      compl  (f:fs) cs lCM =  compl  fs (newCompletion cs lCM f)
                                       (ppLcm lCM (powPr (lpp f)))



        --     newCompletion  cfs lCM g  ->  newCfs

        -- Returns   c(g:fs)                           and  ( ? )
        -- lcm = ppLcmL [ lpp h |  h <- (g:fs) ].            
        -- METHOD (see the paper). 
        -- ps   =  {p |  p+lpp(g)  divides  lCM}
        -- newC =  { (p+lpp(g), t(p,cfs)) } :  p from ps }
        --   where  
        --   t p cfs =  let  p1  = p+lpp(g)
        --                   p11 = cancelLastZeroes (butLast p1)
        --                   find (p11,fx) in  cfs,  
        --                   a = lc(fx),
        --                   b = lc(g), 
        --                   find  u,v:  u*a+v*b = gcd(a,b)
        --              in               u*(p1/lpp(fx))*fx + v*p*g
    

    newCompletion  cfs lCM g = 
                        newCompl  cfs g (lc g) (powPr (lpp g)) lCM
        where
        newCompl cfs g a pg lCM = 
          let
            p1      =  addL pg lCM
            (bp1,p) =  butLastLast p1
            bp1C    =  cancelLastZeroes bp1
            ((pp11,fx):_) =  dropWhile (\(p,_)->p/=bp1C) cfs
            ppfx    =  lpp fx
            pp2     =  sub (pp ppfx p1) ppfx  
            (d,u,v) =  eucGCDE a (lc fx)
            h1      =  mPolMul (u, pp2       ) fx 
            h2      =  mPolMul (v, pp pp2 lCM) g  
            critP   =  (p1 {-?-}, polAdd h1 h2)
          in
            case decr lCM of  [] -> [critP]
                              l1 -> critP:(newCompl cfs g a pg l1)
    --------------------------------------------------------------
          -- b_criterion  rows singles m  ->  (newRows,newSingles)

          -- deletes from  rows  all the critical pairs (f,t)  with 
          -- the monomial  t  (= tij)  the multiple of monomial  m.
          --   If a row turns to singleton  (f,[]),  then it is re-
          -- moved, and f joins  singles.

    b_criterion  rows sgs m =
      let
        notMultiple (_,t)     =  not (monDivides m t)
        makeRow     (f,crits) =  (f, filter notMultiple crits)
        singleton   (_,crits) =  null crits
        newRows               =  map makeRow rows
      in        
        ( filter (not.singleton) newRows, 
          insertPols sgs (map fst (filter singleton newRows)) 
        )
    --------------------------------------------------------------
                       -- critical pair list for new polynomial  h
    newCrits  rows singles h =
      let
        a  = lc  h
        p  = lpp h
        pr = powPr p
      in     ncr  a p pr (mergePolLists (map fst rows) singles) []
        where

          -- critical pairs  cs= [(g1,t_g1_h)..(g2,t_gi2h)..]  for
          -- h  are accumulated.  Also  cs  if filtered by  
          -- mutPrime- , M- , F-  criterions - see the paper on M,
          -- F-criterions.

          -- * mutPrime(g,h)  criterion
          --             (from widely known B.Buchberger's work) :
          --   t_g_h  is skipped if
          --   (lpp g  and  lpp h   are  mutually prime)  &
          --   (lc g, lc h  are invertible  
          --         (i.e. have the same Euclidean norm as  unity)
          --   )
          --   *** This criterion is NOT Valid for the VECTORS.***
          
          -- For this  newCrits  finction,  M-, F-  criterions ::
          -- (cs, t_g_h) -> new_cs   simply mean that

          -- * last  t_g_h  is skipped if it is a multiple of some
          --   previous  t  from  cs,
          -- * otherwise t_g_h  filters out its multiples from the
          --   the previous  cs 

        ncr  _ _ _  []     cs =  cs
        ncr  a p pr (g:gs) cs =  
          let
            b      = lc  g
            q      = lpp g
            t_g_h  = monLcm (a,p) (b,q)     -- t(i,v+1) from paper
            unNorm = eucNorm (unity a)
          in
            if  ppMutPrime pr (powPr q)  &&   
                (eucNorm a)==unNorm      &&
                (eucNorm b)==unNorm        then   ncr a p pr gs cs
            else  
              if  any (\m->monDivides m t_g_h) (map snd cs)  
                                            then  ncr a p pr gs cs
              else 
                let  filt (_,m) = not (monDivides t_g_h m)
                in
                  ncr  a p pr gs
                           (insertPair (filter filt cs) (g,t_g_h))
    --------------------------------------------------------------

    initRows [f,g] = 
                (  [ (f,  [(g, monLcm (lm f) (lm g))]) ],   [g]  )
    initRows (f:fs)  = 
      let 
        (rows,singles)        =  initRows fs
        critsFor_f            =  newCrits rows singles f
        (newRows, newSingles) =  b_criterion  rows singles (lm f)
      in
        if  null critsFor_f  then  (newRows, insertPol singles f)
        else          (insertRow newRows (f,critsFor_f), singles)
    --------------------------------------------------------------

                       -- Main loop.  Process the critical pairs 
                       -- from  rows  until  rows  is empty

    prPairs  []         _       cfs _  =  map snd cfs

    prPairs  (row:rows) singles cfs l  =  
      let
        (fi, (fj,tij):row1) =  row  
        h                  = (polNF "" (map snd cfs) (sPol fi fj))
      in
        case  (h,row1)  of
          ([], []) -> prPairs rows (insertPol singles fi) cfs l
                                              -- trivial pair and
                                              -- new singleton row

          ([], _ ) -> prPairs  ((fi,row1):rows) singles cfs l
                                     -- trivial pair and 
                                     -- non-singleton row. Delete 
                                     -- critical pair (fj,tij)
          (h , _ ) -> 
            let  
              newCfs   = newCompletion cfs l h 
              newcrits = newCrits (row:rows) singles h
              (newRows,newSingles) = 
                      b_criterion  ((fi,row1):rows) singles (lm h)

              newL = ppLcm l (powPr (lpp h))  -- ?
            in
              if  null newcrits  then     
                       prPairs  newRows (insertPol newSingles h) 
                                                       newCfs newL
              else     prPairs  (insertRow newRows (h,newcrits)) 
                                            newSingles newCfs newL
    --------------------------------------------------------------

  in
                                      -- grBas_euc   itself starts 
    (case  redTout "" fS  of
      []  -> []
      [f] -> [f]
      fs  -> let  cfS =  complete fs 
                  lCM =  ppLcmL (map (powPr.lpp) fs)
                  (rows,singletons) =  initRows fs    
             in
                  redTout mode (prPairs rows singletons cfS lCM)               
    )


-}

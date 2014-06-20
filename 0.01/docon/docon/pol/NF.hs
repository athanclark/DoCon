------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- Normal form for polynomial. 

-- This relates to the Groebner bases.




module  NF  where

import  PreludeInteger
import  PreludeList
import  Categ 
import  Categ1 
import  Matrix
import  PP
import  Pol
import  IParse  --?




initVectors  zr a xs =  let  (Mt rows) = scalMatr xs a zr
                        in
                          zip xs rows
------------------------------------------------------------------



polNF ::  SyzygySolvableRing c 
          => 
          String -> [Pol c] -> Pol c -> (Pol c, [Pol c])


      -- Normal Form of Polynomial over a EUCLIDEAN ring  c.

      -- gs  should NOT contain zeroes.
      -- The reduction continues while  head f  is reducible. 
      -- Coefficients are divided with the Minimal Norm remainder.

      -- Also the Quotient Vector is accumulated.
      -- First each each  gi  is paired with its factor qi.  This
      -- makes  gqs.
      -- In the end   f = nf + g1*q1+...+gn*qn,   and  qi  are
      -- extracted from pairs.
      -- gqs  is divided into parts  gq1s and gqs.   gg1s contain
      -- gi  that were tried as the  lm-divisors  in  the current
      -- circle.  Restart "from head of gs" implies the return to
      -- initial_gqs =  (reverse gq1s)++gqs.


polNF  mode gs (Pol fMons) = 
  let
    --------------------------------------------------------------
    gqs =  map  (\g-> (g, Pol []))  gs

                 -- nf0 mode gqs f ->  (gqs',remainder),
                 -- it accumulates the quotient part of each  gi.

    nf0 "r" gqs fMons = 
          let
            nr  mons (gqs, []    ) =  (gqs,mons)
            nr  mons (gqs, (m:ms)) =  nr  (m:mons) (nf0 "" gqs ms)

            (gqs',rMons) =  nr [] (nf0 "" gqs fMons)
          in
            (gqs', reverse rMons)  

    nf0 ""  gqs fMons =  nf [] gqs fMons  
                                           -- initiate  gqs1 = []
      where
      nf  gq1s gqs              [] =  ((reverse gq1s)++gqs, [])
      nf  gq1s []               ms =  (reverse gq1s, ms) 
      nf  _    ((Pol [],_):_  ) _  =  
                         error "(polNF_q _ gs _):   zero among gs"
      nf gq1s  ((g,g1):gqs)     ms  =
        let
          a  = lc  (Pol ms)
          p  = lpp (Pol ms)
          dp = sub p (lpp g) 
        in
          if  any (<0) (ppP dp)  then  nf ((g,g1):gq1s) gqs ms
                                                 --does not divide
          else                         
            let  [qt,a1] = divRem "m" a (lc g)  
                 norm    = (eucNorm a )
                 norm1   = (eucNorm a1)  
            in
              if a1==(zero a1) then   --monomial divided presizely
                    let
                      (Pol ms1) = polSub (Pol (tail ms))
                                     (mPolMul (qt,dp) (polTail g))
                      g1New = polAdd (Pol [(qt,dp)]) g1
                    in
                      nf  [] ((reverse gq1s)++((g,g1New):gqs)) ms1
              else                      
                (case  compare norm1 norm  of
                  GT -> 
                   error (
                        ( (shows "INTERNAL DoCon ERROR.  TEST  ").
                          (shows "divRem m ").
                          (shows a).(' ':).show
                        )                        (lc g)
                         )

                  EQ ->  nf  ((g,g1):gq1s) gqs ms    
                                         --coefficient not reduced
                  _  -> 
                   let  (Pol ms1) = polSub (Pol (tail ms))
                                     (mPolMul (qt,dp) (polTail g))
                        g1New     = polAdd (Pol [(qt,dp)]) g1
                   in
                     nf  ((g,g1New):gq1s) gqs ((a1,p):ms1)
                                              -- lc became smaller
                )
    --------------------------------------------------------------

  in

    let  (gqs',rMons) =  nf0 mode gqs fMons  
    in  
         ( Pol rMons,  map snd gqs' )







------------------------------------------------------------------

polNF_v :: SyzygySolvableRing c =>
                      String -> [VecPol c] -> VecPol c -> VecPol c

                   -- Differs from  polNF  in that the reduction 
                   -- on the polynomial parts is extended  (with 
                   -- the same coefficients to the vector parts.

polNF_v  mode gvs (f,v0) = 
  let
    vSub u v =  binOpList polAdd u (map polNeg v)

                             -- redV u qs vs  ->  u-q1*v1-..-qn*vn
    redV u []     []     =  u         
    redV u (q:qs) (v:vs) =  redV (vSub u (map (polMul q) v)) qs vs

    (r,qs) = polNF mode (map fst gvs) f    -- f-q1*g1-..-qn*gn =r
  in   
    ( r,  redV v0 qs (map snd gvs) )

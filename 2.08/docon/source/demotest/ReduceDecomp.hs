{- TASK by S.V.Duzhin  --------------------------------------------

For each of the given polynomials do the following:
1. Expand (you will get a homogeneous polynomial in xi's
of degree 4 in each variable).
2. Make substitution  xi^3 -> 1  for all  i.
(you will get a a non-homogeneous polynomial of degree 2 in each
variable).
3. Symmetrize (take the average over the complete symmetric group
in all variables that appear).
4. Express through some basis in the algebra of symmetric polynomials
(elementary symmetric, power sums etc.). In principle, any basis will 
do, but if possible choose the one that gives the shortest results -- 
and use it in all calculations.
Examples.
g11 = -((x1-x2)*(x2-x3)*(x3-x1))^2
sym = 3*(SymPol 2*[2*3] -1*[2,1] 2*[1*3] 2*[]  )
inE = -3*e1*e2 + 6*e3^2 + 15*e3 + 6
------------------
g21 = product [x1-x2,x2-x5,x5-x1, x2-x3,x3-x6,x6-x2,
               x3-x4,x4-x5,x5-x3, x4-x1,x1-x6,x6-x4
              ]
sym = coef*
      (SymPol 10*[2*6] -2*[2*4,1] 1*[2*3,1*3] 1*[2*3] 1*[2*2,1*2] 
              -2*[2,1*4] -2*[2,1] 10*[1*6] 1*[1*3] 10*[]  
      )
inE = coef * (-2*e1*e2 - 4*e1*e5 - e2*e4 + e3^2 + 7*e3*e6 + 7*e3 
              - 2*e4*e5 + 10*e6^2 + 29*e6 + 10
             )
---------------------------------------------------------------------
-}




module ReduceDecomp where

import Maybe   (isJust                    )
import List    (genericLength, genericDrop)
import DExport 


reduceSymmDecompose :: 
                 (Field k) => PrttComp -> Pol k -> (SymPol k, Pol k)

  -- reduce  f <- a[x1..xn]  by  [xi^3 - 1 |...];
  -- symmetrize it to  sym <- SymPol F,  F = Fraction a,
  --                        (division by n! may bring denominators);
  -- decompose to polynomial of F[e1,e2..] in elementary symmetrics,
  -- the result projected to subalgebra of variables  [e1..en].
  -- RESTRICTION:  char k = 0  or  > n.

reduceSymmDecompose pcp f =
  let  
    n        = genericLength $ pVars f
    f'       = reduce 3 f
    sym'     = symmetrizePol pcp f' 
    Just sym = sym'
    w        = deg sym
    inE      = snd $ to_e_pol "mn" eFM (lexPPO w) sym

                      -- Other bases are possible too. For example,  
                      -- inS = snd $ to_s_pol "m" eFM (lexPPO w) sym
                      -- expresses it in Schur functions

    project f = ct f $ filter notDep $ polMons f
                    -- remove monomials that depend on ei with i > n
                     where
                     notDep = all (==0) .genericDrop n .vecRepr .snd
  in  
  if  isJust sym'  then  (sym, project inE)
  else
    error ("symmetrize  failed\n."++
           "Mind that a field  k  is needed for coefficients, "++
           "char k = 0  or  > n \n"
          )


reduce n f =                 -- remainder by [xi^n - 1 | xi <- vars]
         ctr f $ similars $ 
                 sortBy (\ (_,p) (_,q)-> cp q p)
                   [(a, fmap (flip rem n) pp) | (a,pp) <- polMons f]
  where 
  cp = ppoComp $ pPPO f
  similars []            = []
  similars ((a,pp):mons) = 
                    (sum1 (a:(map fst mons')), pp):(similars mons'')
                             where
                             (mons',mons'') = span ((==pp).snd) mons


                                     -- invariant part of data input
un      = 1:/1  :: Fraction Z
dQ      = upField un eFM
vars n  = map (('x':).show) [1..n]    
unPol n = cToPol (lexPPO n) (vars n) dQ un     -- 1 of P = Z[x1..xn]
                 --example

readPol n = smParse (unPol n)

 ;




{- reserved for testing --------------------------------------------

symmSumPol_direct_test :: (CommutativeRing a) => Pol a -> Pol a
symmSumPol_direct_test                           f = 
                                      case  (polMons f, pVars f)  of
  ([]  , _   ) -> zeroS f
  (mons, vars) -> sum1 $ map sysumMon $ mons
    where
    sysumMon (a,Vec js) = 
                 sum1 [ct f (a, Vec$ applyPermut pm js)| pm<- pmts]
    ordList = map fst $ zip [1 ..] vars
    pmts    = map permutRepr $ allPermuts ordList
                        --------------------------------------------
-} 





{- Preparing Input Data ********************************************

module Main where
import DExport      
import ReduceDecomp

main = let (sym,inE) = reduceSymmDecompose pLexComp g11  --edit this
       in 
       putStr $ shows sym $ ("\n\n"++) $ shows inE "\n"


g11 = readPol 3  " -((x1-x2)*(x2-x3)*(x3-x1))^2 "

g21 = product1 $ map (readPol 6) 
        [
         "x1-x2","x2-x5","x5-x1", "x2-x3","x3-x6","x6-x2",
         "x3-x4","x4-x5","x5-x3", "x4-x1","x1-x6","x6-x4"
        ]
-- ...
--------------------------------------------------------------------
Makefile:          in standard  docon/../sampleProjects/Makefile
--------           put
ReduceDecomp.o :
        $(HC) -c  ReduceDecomp.hs  $(HCFlags)
Main.o :
        $(HC) -c  Main.hs  $(HCFlags)
run :
        $(HC) -o $@  Main.o ReduceDecomp.o  $(linkFlags)
-------------------------------------------------------------------- 
Preparation and running:
  cd  ...docon/../sampleProjects
  make ReduceDecomp.o                            -- to be done once
  edit Main.hs                                   -- repeat for each
  make Main.o;  make run;  ./run +RTS -M...m     -- example




RESULTS  ***********************************************************

COST:  n = 9,  g31  needs  16 sec  and 33 Mb space
                           - for  DoCon-2.01,  GHC-4.04,  PC i686.

--------------------------------------------------------------------
g11 = readPol 3 " -((x1-x2)*(x2-x3)*(x3-x1))^2 "

sym = (SymPol 6*[2*3] -3*[2,1] 6*[1*3] 6*[]  )

inE = -3*e1*e2 + 6*e3^2 + 15*e3 + 6
--------------------------------------------------------------------
n   = 6;
g21 = product1 $ map (readPol 6)
                  ["x1-x2","x2-x5","x5-x1", "x2-x3","x3-x6","x6-x2",
                   "x3-x4","x4-x5","x5-x3", "x4-x1","x1-x6","x6-x4"
                  ]
sym = (SymPol 6*[2*6] (-6/5)*[2*4,1] (3/5)*[2*3,1*3] (3/5)*[2*3] 
              (3/5)*[2*2,1*2] (-6/5)*[2,1*4] (-6/5)*[2,1] 6*[1*6]
              (3/5)*[1*3] 6*[] 
      )
inE = 
  (-6/5)*e1*e2 - (12/5)*e1*e5 - (3/5)*e2*e4 + (3/5)*e3^2
   + (21/5)*e3*e6 + (21/5)*e3 - (6/5)*e4*e5 + 6*e6^2 + (87/5)*e6 + 6
--------------------------------------------------------------------
g22 = product1 $ map (readPol 6)
              ["x1-x2","x2-x3","x3-x1", "x2-x4","x4-x3","x3-x2",
               "x4-x5","x5-x6","x6-x4", "x1-x5","x5-x6","x6-x1"
              ]
sym = (SymPol
        -12*[2*6] (12/5)*[2*4,1] (-6/5)*[2*3,1*3] (-6/5)*[2*3] 
        (-6/5)*[2*2,1*2] (12/5)*[2,1*4] (12/5)*[2,1] -12*[1*6] 
        (-6/5)*[1*3] -12*[] 
      )
inE =
  (12/5)*e1*e2 + (24/5)*e1*e5 + (6/5)*e2*e4 -(6/5)*e3^2 -(42/5)*e3*e6 
   - (42/5)*e3 + (12/5)*e4*e5 - 12*e6^2 - (174/5)*e6 - 12
---------------------------------------------------------------------
g31 = product1 $ map (readPol 9)
              ["x1-x2","x2-x7","x7-x1", "x2-x3","x3-x8","x8-x2",
               "x3-x4","x4-x7","x7-x3", "x4-x5","x5-x9","x9-x4",
               "x5-x6","x6-x8","x8-x5", "x6-x1","x1-x9","x9-x6"
              ]
sym = (SymPol 
    6*[2*9] (-3/4)*[2*7,1] (3/14)*[2*6,1*3] (3/14)*[2*6] 
    (3/14)*[2*5,1*2] (-6/35)*[2*4,1*4] (-6/35)*[2*4,1] 
    (3/14)*[2*3,1*6] (-3/40)*[2*3,1*3] (3/14)*[2*3] 
    (3/14)*[2*2,1*5] (3/14)*[2*2,1*2] (-3/4)*[2,1*7] (-6/35)*[2,1*4]
    (-3/4)*[2,1] 6*[1*9] (3/14)*[1*6] (3/14)*[1*3] 6*[]  
      )
inE =
  (-3/4)*e1*e2 - (3/5)*e1*e5 - (21/10)*e1*e8 - (3/14)*e2*e4 
   - (15/56)*e2*e7 + (3/14)*e3^2 + (123/280)*e3*e6 + (96/35)*e3*e9 
   + (69/28)*e3 - (6/35)*e4*e5 - (3/5)*e4*e8 - (3/14)*e5*e7 
   + (3/14)*e6^2 + (69/28)*e6*e9 + (96/35)*e6 - (3/4)*e7*e8 + 6*e9^2
   + (1347/70)*e9 + 6
-------------------------------------------------------------------- 
g32 = product1 $ map (readPol 9)
              ["x1-x2","x2-x7","x7-x1", "x2-x3","x3-x8","x8-x2",
               "x3-x4","x4-x9","x9-x3", "x4-x5","x5-x7","x7-x4",
               "x5-x6","x6-x8","x8-x5", "x6-x1","x1-x9","x9-x6"
              ]
sym = 0
-------------------------------------------------------------------- 
g33 = product1 $ map (readPol 9)
              ["x1-x2","x2-x7","x7-x1", "x2-x3","x3-x8","x8-x2",
               "x3-x4","x4-x9","x9-x3", "x4-x5","x5-x9","x9-x4",
               "x5-x6","x6-x8","x8-x5", "x6-x1","x1-x7","x7-x6"
              ]
sym = (SymPol
    24*[2*9] -3*[2*7,1] (6/7)*[2*6,1*3] (6/7)*[2*6] (6/7)*[2*5,1*2]
    (-24/35)*[2*4,1*4] (-24/35)*[2*4,1] (6/7)*[2*3,1*6] 
    (-3/10)*[2*3,1*3] (6/7)*[2*3] (6/7)*[2*2,1*5] (6/7)*[2*2,1*2] 
    -3*[2,1*7] (-24/35)*[2,1*4] -3*[2,1] 24*[1*9] (6/7)*[1*6] 
    (6/7)*[1*3] 24*[]
      )
inE =
  -3*e1*e2 - (12/5)*e1*e5 - (42/5)*e1*e8 - (6/7)*e2*e4 
   - (15/14)*e2*e7 + (6/7)*e3^2 + (123/70)*e3*e6 + (384/35)*e3*e9 
   + (69/7)*e3 - (24/35)*e4*e5 - (12/5)*e4*e8 - (6/7)*e5*e7 
   + (6/7)*e6^2 + (69/7)*e6*e9 + (384/35)*e6 - 3*e7*e8 + 24*e9^2 
   + (2694/35)*e9 + 24
--------------------------------------------------------------------
g34 = product1 $ map (readPol 9)
                  ["x1-x2","x2-x7","x7-x1", "x2-x3","x3-x8","x8-x2",
                   "x3-x4","x4-x8","x8-x3", "x4-x5","x5-x9","x9-x4",
                   "x5-x6","x6-x9","x9-x5", "x6-x1","x1-x7","x7-x6"
                  ]
-------------------------------------------------------------------- 
g35 = product1 $ map (readPol 9)
                  ["x1-x2","x2-x7","x7-x1", "x2-x3","x3-x8","x8-x2",
                   "x3-x4","x4-x9","x9-x3", "x4-x5","x5-x9","x9-x4",
                   "x5-x6","x6-x7","x7-x5", "x6-x1","x1-x8","x8-x6"
                  ]
-------------------------------------------------------------------- 
g36 = product1 $ map (readPol 9)
                  ["x1-x2","x2-x3","x3-x1", "x2-x5","x5-x4","x4-x2",
                   "x3-x4","x4-x5","x5-x3", "x1-x6","x6-x7","x7-x1",
                   "x6-x9","x9-x8","x8-x6", "x7-x8","x8-x9","x9-x7"
                  ]
-}





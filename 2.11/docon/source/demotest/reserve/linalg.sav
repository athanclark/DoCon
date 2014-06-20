------------------------------------------------------------------
------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.02
--
--  Copyright  Serge Mechveliani,  2002
------------------------------------------------------------------
------------------------------------------------------------------




-- Tests, benchmarks, demonstration.




{- --------------------------------------------------------------
   Linear Algebra, polynomial arithmetics, gcd, 
   domain description processing.


The below script presents the  

  staircase form, diagonal form, determinant  of a matrix over an
  Euclidean ring  R[x],  R = Z/(p),  p prime,

  inversion of matrices over  Fraction (R[x]), Fraction (Z[x,y]),

  fraction arithmetics,  gcd  for  R[x,y],  R a finite field,
  a GCD-ring  - for the matrix inversion applies these fraction
  cancelation by gcd,

  parsing  the Set elements - here it is reading of polynomial.
------------------------------------------------------------------
-}



import DPrelude   (eFM, ctr, smParse, mapmap)
import Categs     (Subring(..)              )

import RingModule (Ring(..), eucIdeal, upField, upEucFactrRing)
import Z          (dZ                                         )
import VecMatr    (Matrix(..)                                 )
import Fraction   (Fraction(..), zeroFr                       )
import Pol        (UPol(..), Pol(..), cToUPol, cToPol, degLex )
import Residue    (ResidueE(..)                               ) 

import LinAlg     (inverseMatr_euc, det_euc, test_toDiagMatr_euc, 
                   test_inverseMatr_euc
                  )

type R  = ResidueE Z
type P  = Pol Z

main =   
  let  
    d             = 5 :: Z
    iI            = eucIdeal "bef" d [] [] [] 
    r0            = Rse 0 iI dZ                        -- 0 of Z/I
    [r1,r2,r3,r4] = map (ctr r0) [1..4::Z]

    dR     = upField r0 eFM           -- domains of Z/(5),
    (_,rR) = baseRing r0 dR           -- in particular, its ring
    propsR = subringProps rR
    o2     = (("degLex",2), degLex, [])
    unP     = cToPol o2 ["x","y"] dZ 1  :: P        -- 1 of Z[x,y]
    unXR    = cToUPol "x" dR r1         :: UPol R   --   of R[x]
    dXR     = upEucFactrRing unXR eFM
    (_,rXR) = baseRing unXR dXR
    propsXR = subringProps rXR
    mM      = mapmap (smParse unXR)
                                 [[ "2*x+1", "(x+2)^2+1",  "0" ],
                                  [ "x"    , "0"        ,  "x" ],
                                  [ "x^2"  , "2"        ,  "1" ]
                                 ] ::[[UPol R]]   --parsing matrix
    mM_xy = mapmap (smParse unP) 
                      [[ "2*x^2*y+x*y+1",  "0"     ,  "x"       ],
                       [ "0"            ,  "x+y+2" ,  "x-y"     ],
                       [ "x+y^2"        ,  "3"     ,  "x*y^2-x" ]
                      ] :: [[P]]
    mM'    = Mt mM dXR
    detM   = det_euc mM       -- determinant, Gauss method
    det_s  = show detM        -- writing element of R[x] to string

    diag_s = test_toDiagMatr_euc mM    
                    -- string expressing the test for transforming
                    -- matrix to the diagonal form 
    --------------------------------------------------------------
    -- embed  mM  to over fractions appending the denominator 1:

    mM_f     = mapmap (:/ unXR) mM     :: [[Fraction (UPol R)]]
    mM_xy_f  = mapmap (:/ unP ) mM_xy  :: [[Fraction P]]
    iM_f     = inverseMatr_euc mM_f      
    det_iM_f = if null iM_f  then  zeroFr unXR  else  det_euc iM_f
                                        
     -- det_iM_f has to be inverse to detM - if the inverse exists

    det_iM_f_s = if  null iM_f  then  "No inverse for M_f"
                 else                 show det_iM_f 
    --------------------------------------------------------------
  in  
  writeFile 
    "result" 
    ( 
     ("propsR  = "             ++) $ (shows propsR ) $("\n\n"++)$ 
     ("propsXR = "             ++) $ (shows propsXR) $("\n\n"++)$ 
     ("given matrix M =     \n"++) $ (shows mM'    ) $("\n\n"++)$
     ("test_toDiagMatr_euc: \n"++) $ (diag_s++    ) $("\n\n\n"++)$
     ("det M        =       \n"++) $ (det_s++     ) $("\n\n\n"++)$
     ("det(inverse) =       \n"++) $ (det_iM_f_s++) $("\n\n\n"++)$
     (test_inverseMatr_euc mM_xy_f)
    )

    -- See the printing in the file  ./result
;







{- ---------------------------------------------------------------
                          Timing
January 1998.
platform:  Linux, PC-486, 120MHz.
ghc-2.08,  
DoCon-1.06, Main.hs  compiled with `-O':       
running:                        time ./run +RTS -H.., -K..

Heap, Stack  are the minimal values at which the given minimal 
running time is achieved:
                                time      heap   stack
                                5.1 sec   500k    9k
--------------
November 1998.
i586, 166MHz.
ghc-3.02,  DoCon-2,  -Onot:     2.2 sec   500k   12k
ghc-4      ...                  2.65      H+S = 4k

March 1999 ... ghc-4.02 ...     2.17      150k    4

-}










{- reserve  ******************************************************

-- Linear algebra for the large matrices over  Integer/(d).

OLD.

main =                                   
  let 
    d      = 2311 :: Integer 
    dProps = [(Prime,Yes)]
    rR     = baseRing d

    [r0,r1,r2,r3,r4] = map (\x->Rse x d dProps) [0,1,2,3,4]
                                       -- short names for residues

    rProps   = subringProperties    rR
    rRes     = baseRing r0
    resProps = subringProperties rRes

    vA =  Vec (copy 17 r0)
    mM = 
      Mt (map Vec
           [[r2,r0,r1,r4,r3,r0,r1,r2,r0,r0,r4,r0,r1,r0],  
            [r4,r0,r2,r4,r1,r0,r1,r2,r0,r1,r4,r1,r1,r0],
            [r4,r0,r1,r4,r0,r0,r1,r0,r3,r1,r4,r0,r3,r1], 
            [r4,r1,r0,r4,r0,r0,r1,r4,r0,r1,r4,r1,r2,r2], 
            [r2,r0,r1,r4,r0,r0,r1,r0,r0,r0,r4,r3,r3,r1],

            [r0,r0,r0,r4,r0,r2,r0,r2,r0,r0,r4,r3,r2,r1],
            [r4,r0,r1,r4,r0,r0,r1,r2,r0,r0,r4,r0,r4,r0],
            [r0,r2,r2,r4,r2,r0,r3,r4,r1,r1,r4,r0,r0,r1],
            [r4,r3,r0,r4,r2,r4,r1,r2,r1,r1,r4,r1,r0,r0],
            [r0,r0,r0,r4,r0,r2,r1,r4,r0,r0,r1,r0,r2,r0],

            [r0,r0,r0,r4,r3,r2,r0,r3,r0,r0,r4,r0,r2,r1],
            [r2,r0,r0,r4,r0,r2,r0,r2,r0,r3,r4,r3,r2,r1],
            [r0,r0,r0,r4,r0,r2,r0,r2,r0,r0,r2,r3,r1,r0],
            [r4,r0,r2,r4,r0,r2,r0,r2,r0,r0,r4,r3,r2,r1],
            [r0,r0,r0,r4,r0,r2,r0,r2,r0,r0,r3,r3,r0,r1],

            [r0,r0,r0,r4,r0,r2,r0,r2,r0,r0,r2,r3,r2,r0],
            [r2,r0,r3,r4,r0,r2,r3,r2,r0,r2,r4,r3,r2,r1]
           ]     
                             :: Matrix (ResidueE Integer)  --17x14


    (mS,_,_) =  toStairMatrix_euc "" mM (Mt [])
  in  
    writeFile "result" 
              ( 
                (w mS "")
                ++"\n\n"++ (test_inverseMatrix_euc    mM   )
                ++"\n\n"++ (test_toDiagonalMatrix_euc mM   )

                --++"\n\n"++ (test_solveLinear_euc    mM vA)
              )


     {-    "rProps       = "    ++ (w    rProps   "")
        ++ "\n\nconstr   = "    ++ (show constr     )
        ++ "\n\nresProps = "    ++ (w    resProps "")          
        ++ "\n\nr2+r3    = "    ++ (w (add r2 r3)   "")
        ++ "\nr2-r3      = "    ++ (w (sub r2 r3)   "")
        ++ "\ntimes r2 7 = "    ++ (w (times r2 7)  "")
    -}


Protocol for the above example.

ghc-0.26-sparc-sun-sunos4,  ghc -c -O ...


                             docon-1.00        |  docon-0.02
                             --------------------------------
                             d      time [sec] 
                             --------------------------------
run  +RTS -K2000k -H14000k      5     3.8      |  3.4
                             2311     6.5      |  4.5                  

END reserve ******************************************************
-}



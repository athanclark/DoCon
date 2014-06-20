------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- demonstration and test




module  Main ( main )   where

import  PreludeChar
import  PreludePair
import  PreludeList
import  PreludeRational
import  PreludeInteger
import  Generic
import  Categ 
import  Categ1 
import  Matrix
import  StrCase
import  ToDiag
import  Det
import  PP
import  Pol
import  VarPol
import  Fraction
import  IParse  
import  ParOpTab
  



type  Z  =  Integer
type  ZZ =  (Z,Z)

type  K  =  Rational
type  FZ =  Fraction Integer
type  A  =  VarPol K


vars = ["x"]

unp = cToPol (0%1) lexComp (1%1)  :: Pol K
                                         -- build unity polynomial
un  = VarP unp vars                       


--unpz = cToPol 0 lexComp 1  :: Pol Z
--unz  = VarP unpz vars



-- Testing linear algebra.
-- The below script presents the  
--
--   staircase form, diagonal form, inversion, determinant 
--        of matrix  over a Euclidean domain R  (here R = K[x]),
--
--   fraction arithmetics over a factorial ring R (here R = K[x])
--        - for the inverse matrix computes over the fractions,
--
--   gcd  for the univariate polynomials over a factorial ring R - 
--        here  R = K  - for the fraction arithmetics implies the 
--        cancellation by gcd,
--        See also the gcd test for Z[x] in the end of this file,
--
--   parsing  for the domains of the Set category - here it is the
--            reading of polynomials.
--
-- make depend;   make run;     produce the executable file  "run"
-- run  sets results into the file  RESULT.





main =   
  let  
    m  = Mt (map (map (r un))
                       [ [ "2*x+1" ,  "(x+2)^2+1",  "0"  ],
                         [ "x"     ,  "0"        ,  "x"  ],
                         [ "x^2"   ,  "2"        ,  "1"  ]
                       ]
            )
         :: Matrix A                             -- parsing matrix

    d   = det "g" m      -- "g" means Gauss method (linalg/Det.hs)
    d_s = w d ""          -- writing element to string

    diag_s = test_toDiagMatr m    
                    -- string expressing the test for transforming
                    -- matrix to digonal form  (lin/ToDiag.hs)

    mf = let  (Mt rows) = m  
         in   Mt (map (map (:/ un)) rows)   :: Matrix (Fraction A)
                        -- this
                        -- imbeds  m  to the matrix over fractions

    imf_s = test_matrInv mf    
                           -- inversion of matrix (lin/StrCase.hs)
    imf   = matrInv "" mf                     -- compute once more

    det_imf =  if  imf==(Mt [])  then  (zero un):/un
               else                    canFr "i" (det "g" imf)

                                -- det_imf  should be the inverse 
                                -- for  d  - if the inverse exists

    det_imf_s = if  imf==(Mt [])  then  "No inverse for  mf"
                else                    w det_imf ""


  in  

    writeFile "RESULT" 
              ( 
                "test_toDiagMatr: \n\n" ++  diag_s     ++
                "\n\n\n" ++
                " det(m) = \n"          ++  d_s        ++
                "\n\n\n" ++
                "test_matrInv: \n\n"    ++  imf_s      ++
                "det(inverse) = \n"     ++  det_imf_s
              )
              exit done










{-
PARSING

main =  let  n   = 1 ::Z 
             fr  = n:/n
             frr = n:%n

             s1  = " -(2+3)^2*2 "
             s2  = " 1:2+3:nil  " 
             s3  = " 1:a:3:nil  "
             --s4  = " ((3,0)*x+(1,0)*z)^2 "

             --([e],msg) = infixParse parenTable opTable (lexLots s2)

             s1' = w (r n        s1)  ""
             s2' = w (r [n]      s2)  ""
             s3' = w (r [(n,n)]  s3)  ""        

             --s4' = w (r un2      s4)  ""           -- VarPol ZZ

        in     
          writeFile  
            "RESULT" 
            ( 
              (
               -- (shows  (r (n,n) "(2,3)" )    )   
               --.('\n':)
               --.(shows  (r fr  "( 2:/ 3 )" )  )     [(:/ 2 3, "")]
               --.('\n':)

                 (w s1).('\n':).(w s1').('\n':).('\n':) 
                .(w s2).('\n':).(w s2').('\n':).('\n':) 
                .(w s3).('\n':).(w s3')

                --.(w s4).('\n':).(w s4') 

              )
              ""
            )
            exit done
-}




{-
--GCD of polynomials

main =  let  d  = r unz " x*(x-1)  *(x-2)^2 *(x-3)^3 "
             x1 = r unz " x*(x-1)^2*(x-2)^4 *(x-4)^5 "
             y1 = r unz " (x-5)^4  *(x-6)^3 *(x-7)^3 "
             x  = d*x1
             y  = d*y1
             gcdSum = genSum (map gcD (copy 100 [x,y])) 
        in         
           writeFile "RESULT" 
                     ( (gcd_test d x1 y1) 
                       ++ "\n\n" ++
                       "gcdSum =  " ++ (w gcdSum "")
                     )
                     exit done
                                    -- ghc -c   ghc -c -O2
                                    -- 19 sec   15  ??
-}



{-
Fraction

main =  let  smp = unz:/unz  :: Fraction (VarPol Z)

             s = " ((x+1)^2)/(x^2-1) + 2 " 
             f = r smp s
        in
             writeFile "RESULT" 
                       ( s ++ "\n\nreads to\n\n" ++ (w f "") )
                       exit done
-}


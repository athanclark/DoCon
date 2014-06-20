------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- The thing is not ready







------------------------------------------------------------------
{-

The below program module is designed for the testing of the 

           Adjacency Relations Hypothesis  (ARH).


Namely, let  mt  be a symmetric matrix  n x n,   who's elements we
denote as the indexed indeterminates ("variables")  xij or x(i,j).

Let  K = Rational,  the field of rational numbers,

A = K[vars],  
  vars = [ xij  |  1 <= i <= j <= n ]  
                                    - a list of length  n*(n+1)/2,
  A  - a polynomial ring.

Then   d = Det(mt) <- A   and  mij = Det(Minor(i,j,mt))  <- A.


------------------------------------------------------------------
Adjacency Relations Hypothesis:

The A-module of the linear relations for the vector
               [ mij .. d ],   1 <= i <= j <= n 

( of length  (n*(n+1)/2)+1 )    is  generated  by  the   adjacency
relations i.e. the ones that are contained in the matrix  equality

                   mm * mt = Det(mt)*E                       (AEQ)

Here  E  is the unity matrix,  and  mm  is the matrix who's 
elements are so-called   Adjacency Minors  of  mt  - the ones that 
are used to express symbolically the inverse matrix.

Thus  each   (i,j),    1 <= i < j <= n,     produces the adjacency 
relation.

This hypothesis was proved for  n = 2, 3  by N.V.Ilyutchetchkin.

Here we test it for  n = 4,5,6.
  - using the program for the computing of the Groebner bases 
  and syzygy bases.

The idea is quite simple. 
Let the adjacency relations make a list  adB  of vectors in the
A-module  A +...+ A   (n*(n+1)/2 + 1) times.

We find the syzygy module basis B using the standard method.

Then the Groebner bases (for the vectors over the ring A)
                      G_adB and G_B 
should be equivalent i.e. reduce each other to zeroes.
------------------------------------------------------------------

The Adjacency Groebner basis Hypothesis  (AGH).

It appeares (for  n = 2,3,4,5,6) that choosing the so-called 
diagonal ordering on monomials we obtain that the minores  mij  
form a Groebner basis themself.
Thus the basic syzygies for them are very simple: 
...

It seems that AGH assertion would make it easy to prove ARH.


AG hypothesis:

The adjacency  minors   mij   form  a  Groebner  basis  under  the
diagonal ordering.

We call the diagonal ordering the  one  that  compares  the  power 
products of  xij  lexicographically, and according to the rule:

x(i,j) > x(k,l)  
  if  x(i,j)  is closier to the main diagonal,  

  and if they are on the same diagonal (parallel to the main one),  
  then there should be  i < j.

-}
------------------------------------------------------------------





Module  ConeFld  where

import  Matrix
import  Pol





------------------------------------------------------------------
-- Let  xij  be the indexed variables which denote the elements of
-- a Symmetric Matrix  n x n.
-- indexedVars   produces the maximal independent sublist of these
--               variables.


type  IndVar =  (String,Integer,Integer)

indexedVars ::  String -> Integer -> [IndVar]  

indexedVars x 3 =  [ (x,1,1), (x,2,2), (x,3,3),           
                     (x,1,2), (x,2,3),
                     (x,1,3) 
                   ]

            {- indexedVars x 5 = 
                {- {&x 1 1} {&x 2 2} {&x 3 3} {&x 4 4} {&x 5 5} 
                {&x 1 2} {&x 2 3} {&x 3 4} {&x 4 5} 
                {&x 1 3} {&x 2 4} {&x 3 5} 
                {&x 1 4} {&x 2 5} 
                {&x 1 5} 
            -}


-- For the Var-Polynomial operation we need to press the indices 
-- into Strings :

pressInd :: IndVar -> String

pressInd (x,i,j) =  x++(show i)++(show j)



------------------------------------------------------------------
--  The  ConeFields  experiment requires the following 
--  Environment to be built as a prelude :
--
--  A =  Rational[vars],   vars = map pressInd (indexedVars x n) 
--  AM = A[ mij | ..],
--                 mij is the variable corresponding to the
--                 minor(i,j), 
--                 these minors are the polynomials over A,
--  M  the E-polynomial module over AM.

--  The mentioned *diagonal* ordering is presented simply by 
--  lexComp,  only when  xij  is being read to polynomial,  it  is
--  essential that the argument list  vars   is  produced  by  the 
--  function  indexedVars  who lists  xij  according to the  above 
--  diagonal order. 
------------------------------------------------------------------



type  K  =  Rational
type  A  =  VarPol K
type  AM =  VarPol A

iVars =  indexedVars x 3 
vars  =  map pressInd iVars


unp        =  cToPol ((fromInt 0)::K) lexComp ((fromInt 1)::K)
unityOf_A  =  VarP unp vars
unp1       =  cToPol (zero unityOf_A) lexComp unityOf_A
unityOf_AM =  VarP unp1 vars


------------------------------------------------------------------
-- Symmetric Matrix  xij,   1 <= i,j <= n,  
-- where  xij  are the Var-Polynomials over the Rational numbers:
--
-- xij <- Rational[vars]


symMatrix :: Integer -> String -> Matrix A

symMatrix  n x =  Mt (sm 1 (n+1))
  where
  sm i n =  if  i==n  then  []
            else            (row i 1 n) : (sm (i+1) n)
    where
    row i j n =  
      if  j==n  then  []
      else
        let 
          elem =  if  j<i  then  varToVarPol un (pressInd (x,j,i))
                  else           varToVarPol un (pressInd (x,i,j))
        in
          elem : (row i (j+1) n)



------------------------------------------------------------------
-- a list of the adjacent determinates of  mt  - for  x(i,j)  from 
-- the  iVars  list  (i <= j).


adjMinores ::  Matrix A -> [indVar] -> [A]

adjMinores  matr iVars =
  let
    indPairs      =  map (\ (_,i,j)->(i,j)) iVars

    signDet i j m =  if  even (i+j)  then  det "" m
                     else                  (neg (det "" m))
  in
    [ signDet (minor i j matr)  |  (i,j) <- indPairs ]



------------------------------------------------------------------
matrOverAM :: Matrix A -> Matrix AM

matrOverAM  (Mt rows) =  Mt  (map (map toAM) rows)
  where
  toAM f =  VarP  (cToPol (zero f) unityOf_AM f) vars

------------------------------------------------------------------
-- Adjacence Relations.

adjRels ::  Integer -> String -> [[Pol A]]
         -- n          x            

adjRels  n x = 
  let  xAMmt = matrOverAM (symMatrix n x)
  in
    ars  xAMmt ((&n*(&n+1))/2 + 1)
      where
      ars  xAMmt l =  
           ar  xAMmt  (scalarMatrix &M ($ &AM unity) () l)
                          {(copy () &l)} 


  (ir1  &A &AM  &M &X &E &V ) =
           (ir2  &A  (MatrSub (MatrMul &M &X &AM) &E &AM)  &V ) ; 






(IlRels  &n &y &x) = 
          (ir  (TOP A) (TOP AM) &n &y &x 
               (SymMatr &n &y) (SymMatr &n &x)  (&n*(&n+1))/2 + 1
          );

(ir  &A &AM &n &y &x &M &X &l ) = 
                    (ir1  &A &AM 
                          (ReadMatrix &M &AM) (ReadMatrix &X &AM)
                          (ScalarMatrix &M ($ &AM unity) () l)
                          {(copy () &l)} 
                    );

  (ir1  &A &AM  &M &X &E &V ) =
           (ir2  &A  (MatrSub (MatrMul &M &X &AM) &E &AM)  &V ) ; 

   (ir2 &A  (#M) &V ) =  { (ir3  &A #M &V) } ; 

    (ir3 &A (#row) #M  &V) =  (ir4  &A #row &V) (ir3 &A #M &V) ; 
    (ir3 &A            &V) =  ; 

      (ir4  &A (#F) #Row &V) =  (ilr &A #F &V) (ir4 &A #Row &V) ; 
      (ir4  &A           &V) =  ; 

        (ilr &A  &m #F  &V) =  (ilr  &A #F (addmon &A &m &V) ) ; 
        (ilr &A         &V) =  &V ; 

         (addmon  &A (&a) (#V &b)) =  {#V ($ &A add &a &b)} ; 
         (addmon  #x             ) =  (addmon1 #x) ; 

          (addmon1 &A (&a 0 #e)  #V1 (&b #V)) = 
                            (addmon1  &A {&a #e}  #V1 &b {#V} ) ; 
          (addmon1 &A (&a 1 #e)  #V1 (&b #V)) = 
                                      {#V1 ($ &A add &a &b) #V} ;


  
/* 
OLD

(IlRels  &n  &y &x) = 
           (ilrels   (SymMatr &n &y) (SymMatr &n &x)   
                     ($ AM~ unity)    (&n*(&n+1))/2 + 1   ) ; 

(ilrels  (#M) &X &un &l) = (ilrels1  (ReadMatrix {#M} AM~) 
                                     (ReadMatrix  &X  AM~) 
                                     (ScalarMatrix {#M} &un () l)
                                     {(copy () &l)} 
                           ); 
        

(ilrels1  &M &X &E &V) = 
             (ilrels2  (MatrSub (MatrMul &M &X AM) &E AM)  &V ) ; 

  (ilrels2  (#M)  &V ) =  { (ilrels3 #M &V) } ; 
    (ilrels3  (#row) #M  &V) = 
                          (ilrels4  #row &V)   (ilrels3  #M &V) ; 
    (ilrels3             &V) =  ; 

      (ilrels4  (#F) #Row  &V) = (ilr  #F &V) (ilrels4 #Row &V) ; 
      (ilrels4             &V) = ; 

        (ilr  &m #F  &V) =  (ilr  #F (addmon &m &V) ) ; 
        (ilr         &V) =  &V ; 

         (addmon  (&a) (#V &b)) =   { #V  ($ A~ add &a &b) } ; 
         (addmon  #x          ) =   (addmon1  #x) ; 

          (addmon1  (&a 0 #e)  #V1 (&b #V)) = 
                               (addmon1  {&a #e}  #V1 &b {#V} ) ; 
          (addmon1  (&a 1 #e)  #V1 (&b #V)) = 
                                  { #V1  ($ A~ add &a &b)  #V } ;

*/



              /*  Testing.                                   */
              /*  Reduce vectors  #F  from module  M  w.r.to */ 
              /*  the Groebner basis  G                      */ 
              /*          (Reduce  #F (#G) )  =   #H         */ 

(Reduce  &f #F &G) = 
               ($ (TOP M) ModuloBasis &f &G gr)  (Reduce #F &G) ;
(Reduce        &G) = ; 


	unuse frames ; 
end ; 



                 COMPUTING SYSYGIES  FOR  MINORES 


xv: ((variables x)) ; 
mv: ((variables m)) ; 

A: (polynomial  (rational) xv~  (named A)) ; 

AM: (polynomial  A~ mv~  (named AM)) ; 

M: (PolynomialVector  A~ (named M))

                    /* CAC: (EPolModule  M Rt A  Lex (FL1) ) ;   
                            (FL1)=(ExtendFlag Lex 6 () () (Lex));
                    */

XE: (SymMatr 3 x) ; 
X:  (ReadMatrix XE~ A~); 

(push MINS  (minores X~ xv~)) ; 
D:    (det X~ A~) ; 
MID:  ((TOP (MINS)) D~) ; 

RI:   (IlRels  3 m x) ; 
RIM:  ( ($ M~ FromVector (BR RI~)) ) ; 
RIMC: ($ M~ GroebnerBasis RIM~) ; 

R: ($ A~ SyzygyBasis MID~) ; 

RM: ( ($ M~ FromVector (BR R~)) ) ; 

(LESST  RM~ RIMC~) ; 

/*
(Reduce 

*/
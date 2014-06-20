------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





module  Matrix
  (
    Matrix(Mt), 

    matrWidth, matrHeight, matrElem, transp,    coefMatrMul, 
    constMatr, matrAdd, matrMul, matrNeg, matrSub, rowMatrMul, 
    scalMatr, mainMatrDiag, isDiagMatr, 

    Eq(..), Text(..), Num(..), Set(..), AddGroup(..), 
    AddMonoid(..), AddSemigroup(..), MulMonoid(..), 
    MulSemigroup(..), Ring(..)
  )

where

import  Categ 
import  Categ1
import  PreludeList
import  PreludeChar
import  Generic
import  StrCase
import  IParse





data  Matrix a =  Mt [[a]]    deriving(Eq,Text)




                   -- [[a]]  is a Non-empty list of rows (lists),
                   -- each of the Same length.


matrHeight (Mt rows) =  genericLength rows
matrWidth  (Mt rows) =  genericLength (head rows)



    ------------------------------------------------------------  
    --  Matrix a  contains the matrices  NxM  for All  N,M > 0.

    -- Each matrix  m  defines the  Ring of matrixes compatible
    -- with  m  by sizes.
    -- Thus,  zero (Mt [[1,2],[1,3]] ) =  (Mt [[0,0],[0,0]] ),
    -- and    zero (Mt [[1]] )            is other.
    
    -- "mulSemigroup", "ring"  etc.  refer to the compatible 
    -- subset of  (Matrix a)  is each individual case.
    ------------------------------------------------------------  



matrElem ::  (a -> Bool) -> Matrix a -> [a] 

               -- returns  [x],  where x is an element of matrix
               --                satisfying the predicate  p,
               --          []    - if there are no such elements.

matrElem  p (Mt rows) =  e  rows
  where  
  e []     = []
  e (r:rs) = case  dropWhile (not.p) r  of  (x:_) -> [x]
                                            _     -> e rs




matrNeg :: AddGroup a =>  Matrix a -> Matrix a 

matrNeg (Mt rs) =  Mt (neg rs)
  


matrAdd, matrSub::  AddGroup a=>  Matrix a -> Matrix a -> Matrix a


matrAdd (Mt rs1) (Mt rs2) =  Mt (add rs1 rs2)

matrSub (Mt rs1) (Mt rs2) =  matrAdd (Mt rs1) (matrNeg (Mt rs2))



coefMatrMul :: MulSemigroup a =>  a -> Matrix a -> Matrix a

coefMatrMul  c (Mt rows) =  Mt  (map (map (mul c)) rows)



rowMatrMul :: CommutativeRing a =>  [a] -> [[a]] -> [a]

         -- multiply Row by Matrix
         -- product =  x1*row1 +...+ xN*rowN,  where  row=[x1..xN]

rowMatrMul  (x:xs) (row:rows) =  rmm  xs rows (map (mul x) row)
  where
  rmm []     []         res =  res
  rmm (x:xs) (row:rows) res =
              rmm  xs rows  (binOpList add res (map (mul x) row) )
  rmm _      _          _   =  
                  error "rowMatrMul:  incompatible matrix heights"



matrMul ::  CommutativeRing a => 
            Matrix a -> Matrix a -> Matrix a

               --  product of matrices  (n x m),(m x k) -> (n x k)

matrMul  (Mt rows1) (Mt rows2) =
                      Mt  (map  (\r-> rowMatrMul r rows2)  rows1 )




transp (Mt rows) =  Mt (transpose rows)



constMatr :: Matrix a -> b -> Matrix b

                      -- replaces each element with the given one
constMatr  (Mt (r:rows)) x =  
                   Mt  (map  (const (map (const x) r))  (r:rows) )




scalMatr :: [a] -> b -> b -> Matrix b
         -- xs     c    z

   -- Make  scalar matrix  NxN  from the given elements  c, z
   --   and the list  xs  of length N,  xs  serves as a counter.
   -- c  is placed on the main diagonal,  z in the rest of matrix.

scalMatr  xs c z =  Mt (sm xs)
  where  
  sm  [x]    =  [[c]]                           -- COSTS  n^2
  sm  (x:xs) =  let  ((x:row):rows) = sm xs
                in        (c:z:row):(z:x:row):(map (\r->z:r) rows)




mainMatrDiag ::  Matrix a -> [a]

mainMatrDiag  (Mt rows) =  dg rows  
  where  
  dg []      =  []
  dg ([]:rs) =  error "mainMatrDiag:  empty row occured"
  dg (r :rs) =  (head r):(dg (map tail rs))



isDiagMatr ::  AddGroup a =>  Matrix a -> Bool

isDiagMatr  m =  
  case  matrElem (const True) m
  of
    []  -> error "isDiagMatr:  empty matrix"
    [x] -> 
      let  zr        = zero x
           (Mt rows) = m
      in
        d  zr rows
          where      
          d  _  []         =  True
          d  _  [[_]]      =  True
          d  zr ([] :_   ) =  
                            error "isDiagMatr:  empty row occured"
          d  zr (row:rows) =  (all (== zr) (tail row)     )  &&
                              (all (== zr) (map head rows))  &&
                              (d zr (map tail rows))











--------------------------  Set  ---------------------------------


instance  Set a =>  Set (Matrix a)    where   

  card  (Mt ((x:r):rows)) =  
    let  
      mt = (Mt ((x:r):rows))  
    in 
      case  card x  of
                   []    -> []
                   [[]]  -> [[]]
                   [[n]] -> [ [n*(matrHeight mt)*(matrWidth mt)] ]

  setTerm  (Mt ((x:_):_) ) = 
            (setDomFuncs 
               (funcNames "set") 
               (setDomCons  (MatrixC (setTerm x))  trivialDomain)
            )

  w (Mt rows) =  ("(Mt \n"++).(w1 rows).("\n)"++)
                              where
                              w1 []     = id
                              w1 [r]    = (w r)
                              w1 (r:rs) = (w r).("\n\n"++).(w1 rs)


                -- on input, matrix is expressed as a list of rows

  fromExpr (Mt []  ) _ =  ( [], "empty sample matrix" )
  fromExpr (Mt rows) e =  case  fromExpr rows e  of
                                      ([rs],"" ) -> ([Mt rs], "" )
                                      (_   ,msg) -> ([]     , msg)






-----------------------  Semigroup  ------------------------------



instance  AddGroup a =>  AddSemigroup (Matrix a)    where 

  addSmgTerm  (Mt ((x:_):_) ) =  

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+", Unknown),  ("gr+", groupAdd x), 
                     --tmp.
           ("ord+", Unknown) 
         ]
         (setDomCons (MatrixC (addSmgTerm x)) trivialDomain)
    ) )


  cyclicAdd _              =  Unknown       --SO FAR
  groupAdd  (Mt ((x:_):_)) =  groupAdd x
  ordAdd    _              =  Unknown

  add =  matrAdd

  zero  m =  let (Mt ((x:xs):rows))= m  in  constMatr m (zero x)

  zero_l m  =  [zero m]

  neg =  matrNeg

  neg_l  mt =  [matrNeg mt]

  times  (Mt rows) n =  Mt (times rows n)

  times_l mt n =  [times mt n]



instance  AddGroup a =>  AddMonoid (Matrix a)  
instance  AddGroup a =>  AddGroup  (Matrix a)  



------------------------------------------------------------------

                   
instance  CommutativeRing a =>  MulSemigroup (Matrix a)   
  where
            -- For the  MulSemigroup  class the matrix should be 
            -- SQUARE.

            -- Though  *  is defined not only for square matrices.


  mulSmgTerm  mt =  
    let 
      (Mt ((x:_):_)) =  mt   
      h              =  matrHeight mt
      w              =  matrWidth  mt
    in  
      (setDomFuncs    (funcs x h w) 
        (setDomProps  (props x h w)
           (setDomCons (MatrixC (ringTerm x)) trivialDomain)
      ) )
        where

        funcs x h w =  (funcNames "mulSmg")  -- SO FAR

        props x h w =  
          if  h/=w  then  []
          else
            [ ("comm", commutative x),  ("cyc*", Unknown), 
                                                 --tmp
              ("gr*", No)
            ]



  commutative  mt =  
      let   (Mt ((x:_):_)) = mt  
            h              =  matrHeight mt
            wd             =  matrWidth  mt
      in                      
        if  h /= wd  then
             error ((w "commutative ") (w mt "Non-Square matrix"))
        else
            if  ((commutative x)==Yes)&&(h==1)  then  Yes
            else                                      Unknown
                                      
  cyclicMul _  =  Unknown 
  groupMul  _  =  No                   

  mul  = matrMul


  unity_l  (Mt rows) =  case  concat rows  of
     []     -> []  
     (x:xs) -> let  zr = zero x 
               in
                 (case  dropWhile ((==) zr) (x:xs)  of
                   []    -> []
                   (y:_) -> (case  unity_l y  of 
                                    []   ->  []
                                    [un] ->  [scalMatr rows un zr]
                            )
                 )
             
--  inv_l  m  =  case  matrInv "" m  of  (Mt []) ->  []
--                                       im      ->  [im]


  -- divide_l  t u =   ... toDiagMatr ...





instance  (CommutativeRing a, MulMonoid a) => MulMonoid (Matrix a)







--------------------------  Ring  --------------------------------


instance  CommutativeRing a =>  Ring (Matrix a)   where
                   
  ringTerm  mt =  
    let 
      (Mt ((x:_):_)) =  mt   
      h              =  matrHeight mt
      w              =  matrWidth  mt
    in  
      (setDomFuncs    (funcs x h w) 
        (setDomProps  (props x h w)
           (setDomCons (MatrixC (ringTerm x)) trivialDomain)
      ) )
        where

        funcs x h w =  (funcNames "ring")  -- SO FAR

        props x h w =  []    -- SO FAR



  euclidean  (Mt [[x]] ) =  euclidean x
  euclidean  _           =  No

  factorizeIsTotal   (Mt [[x]] ) =  factorizeIsTotal x
  factorizeIsTotal   _           =  No

  minNormRemValid    (Mt [[x]] ) =  minNormRemValid  x
  minNormRemValid    _           =  No

  field  (Mt [[x]] ) =  field x
  field  _           =  No


  char  (Mt ((x:_):_)) =  char x




instance  CommutativeRing a =>  Num (Matrix a) 
  where
  negate = matrNeg 
  (+)    = matrAdd 
  (-)    = matrSub 
  (*)    = matrMul 

  -- (/)    = divide

;
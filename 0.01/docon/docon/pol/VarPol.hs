------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Polynomial with Variables  




module  VarPol 
  {- 
    Eq(..),Text(..),Fractional(..),    Set(..), 
    AddSemigroup(..),AddMonoid(..),AddGroup(..),
    MulSemigroup(..),MulMonoid(..),
    Ring(..),CommutativeRing(..),SyzygySolvableRing(..),
    varToVarPol
  -}
where

import  PreludeChar
import  PreludeList
import  Categ
import  Categ1
import  PP
import  Pol
import  ExprPol
import  Matrix
import  IParse





data  VarPol c =  VarP (Pol c) [String]       deriving(Text)
                               --variable list

fromVarP  (VarP  f vs) =  f     

toVarP  vs f =  VarP  f vs      
                                    --fromVarP1 (VarP1 f v ) =  f
                                    --toVarP1 v  f =  VarP1 f v



  {- -------------------------------------------------------------
     vars      is a list of variables (indeterminates) serving for
               the reading-writing of polynmial.

     Restrictions:

     * in  (VarP f vars)  the monomials of  f  should be ordered
       according to the (one and the same) order  cp  on PP-s;
       this  cp function is stroed inside of each monomial.

     * length vars > length (ppP pp)    for all  pp  from f

     EXAMPLE.
     for  A = VarPol Integer,  cp = degLex  
     let  
      f = (VarP 
            (Pol 
               [(1, PP [2,0,2] cp), (2, PP [3] cp), (1, PP [] cp)]
            )
            ["x","y","z"]
          )
     in 
       w f 
     -->        " x^2*z^2  +  2*x^3  +  1 "

     The same result will be for  ["x","y","z","u"].
     ----------------------------------------------------------
   -} 




          --  Any subring of                     VarPol c   
          --  associated with the list  l  from [String]
          --  is isomorphic to the subring of    Pol c 



lmV  (VarP f _) =  lm f
lcV  (VarP f _) =  lc f

lppV (VarP f _ ) =   ppP (lpp f)


varpEmp   x []  =  []
varpEmp   x [y] =  [ VarP y x ]
                                    --varp1Emp x []  = []
                                    --varp1Emp x [y] = [VarP1 y x]



------------------------------------------------------------------
instance  Eq a =>  Eq (VarPol a)   where

  (VarP f _)==(VarP g _) =  f==g 

              -- we presume that all operations take polynomials 
              -- supplied with in the Same variable list.


------------------------------------------------------------------

instance  CommutativeRing a =>  Set (VarPol a)   where

  card _ = [[]]

  setTerm (VarP f vars) = 
      (setDomFuncs  (funcNames "set")
         (setDomCons  (Polynomial (ringTerm (lc f)) vars) 
                      trivialDomain
      ))

  w (VarP f vars) =  showsPol vars f    


  fromExpr (VarP (Pol []) _   ) _ =  
                       error( "(fromExpr f e):  Non-zero sample "
                              ++ "var-polynomial f needed"
                            )
  fromExpr (VarP f        vars) e =  
    let  
      { un = unity (lc f);  cp = ppCp (lpp f) }
    in   
      case  exprToPol vars (zero un) un cp e  
      of 
        ([f],"" ) -> ( [VarP f vars], ""  )
        (_  ,msg) -> ( []           , msg )


------------------------------------------------------------------


instance  CommutativeRing a =>  AddSemigroup (VarPol a)
  where

  addSmgTerm (VarP f vars) =   
         (setDomCons  
            (Polynomial (ringTerm (lc f)) vars)  (addSmgTerm f)
         ) 

  cyclicAdd (VarP f _) =  cyclicAdd f 
  groupAdd  (VarP f _) =  groupAdd  f 
  ordAdd    _          =  No

  add     (VarP f vs) (VarP g _)  =  VarP (add f g) vs
  zero    (VarP f vs)             =  VarP (zero f)  vs
  zero_l  (VarP _ vs)             =  [ (VarP (Pol []) vs) ]
  neg     (VarP f vs)             =  VarP (neg f) vs
  neg_l   (VarP f vs)             =  varpEmp vs (neg_l f)
  sub_l   (VarP f vs) (VarP g _)  =  varpEmp vs (sub_l f g)
  times_l (VarP f vs) n           =  varpEmp vs (times_l f n)



instance  CommutativeRing a =>  AddMonoid (VarPol a)

instance  CommutativeRing a =>  AddGroup  (VarPol a)


------------------------------------------------------------------

instance  CommutativeRing a =>  MulSemigroup (VarPol a)
  where

  mulSmgTerm  (VarP f vars) =   
         (setDomCons  
            (Polynomial (ringTerm (lc f)) vars)  (mulSmgTerm f)
         ) 

  commutative (VarP f _) =  commutative f
  cyclicMul   (VarP f _) =  cyclicMul   f 
  groupMul    (VarP f _) =  groupMul    f

  mul        (VarP f vs) (VarP g _)  =  VarP (mul f g) vs

  unity_l  (VarP f vs)            =  varpEmp vs (unity_l f)
  inv_l    (VarP f vs)            =  varpEmp vs (inv_l   f)
  divide_l (VarP f vs) (VarP g _) =  varpEmp vs (divide_l f g)




instance  CommutativeRing a =>  MulMonoid (VarPol a)


------------------------------------------------------------------


instance  CommutativeRing a =>  Ring (VarPol a)
  where

  ringTerm  (VarP f vars) =   
           (setDomCons  
              (Polynomial (ringTerm (lc f)) vars)  (ringTerm f)
           ) 

  hasZeroDiv       (VarP f _) =  hasZeroDiv       f
  hasNilp          (VarP f _) =  hasNilp          f
  field            (VarP f _) =  field            f
  princIdeals      (VarP f _) =  princIdeals      f     
  syzygySolvable   (VarP f _) =  syzygySolvable   f
  factorial        (VarP f _) =  factorial        f
  factorizeIsTotal (VarP f _) =  factorizeIsTotal f  
  hasGrBas         (VarP f _) =  hasGrBas         f
  moduloIsCanonic  (VarP f _) =  moduloIsCanonic  f
  minNormRemValid  (VarP f _) =  minNormRemValid  f

                   -- R[x1..xn] (+ divRem + eucNorm)  is Euclidean 
                   -- when  n==1  and  R is a field
  euclidean  (VarP _ (_:_:_)) =  No             
  euclidean  (VarP f _      ) =
                            if  (field (lc f))==Yes  then  Yes
                            else                           Unknown


  char (VarP f _ )   =  char f
  i_l  (VarP f vs) n =  varpEmp vs (i_l f n)

 

instance  CommutativeRing a =>  CommutativeRing (VarPol a)


instance  CommutativeRing a =>  Num (VarPol a) 
  where
  negate  (VarP f vs)      =  VarP (negate f) vs
  (VarP f vs) + (VarP g _) =  VarP (f+g) vs
  (VarP f vs) - (VarP g _) =  VarP (f-g) vs
  (VarP f vs) * (VarP g _) =  VarP (f*g) vs


instance  CommutativeRing a =>  Fractional (VarPol a) 
  where
  (VarP f vs) / (VarP g _) =  VarP (f/g) vs 


------------------------------------------------------------------

--instance  ModuleOver (Pol c) c =>  ModuleOver (VarPol c) c
--  where
-- moduleTerm (VarP f vars) = 
--  cMul c (VarP f vs) =  VarP (cMul c f) vs


------------------------------------------------------------------


instance  (SyzygySolvableRing a, Num a) =>  
                             SyzygySolvableRing (VarPol a)   where

  canInv    (VarP f vs) =  VarP (canInv f) vs

  factorize (VarP f vs) = 
                   map  (\(g,n)-> ((VarP g vs),n) )  (factorize f)

  gcD  ((VarP f vs):fs) =  VarP  (gcD  (f:(map fromVarP fs)) )  vs

  ----------------------------------------------------------------
                             -- correct provided  field(coef)==Yes
                             -- and  length(vars) == 1
  eucNorm  (VarP f vs) =  totalDeg f

  divRem _ (VarP f vs) (VarP g _) =  
            let  (q,r) = polDivRem f g  in  [VarP q vs, VarP r vs]
  ----------------------------------------------------------------

  moduloBasis  modes vgs (VarP f vs) = 
    let
      (r,qs) =  moduloBasis modes  (map fromVarP vgs)  f
    in
      (VarP r vs, map (toVarP vs) qs)
  ----------------------------------------------------------------
  grBasis _    []                =  ( [], Mt [] )
  grBasis mode ((VarP f vs):vfs) = 
    let
      (gs, Mt rows) =  grBasis mode (f: (map fromVarP vfs))
    in
      ( map (toVarP vs) gs,  
        Mt  (map (\row-> map (toVarP vs) row) rows)
      )
  ----------------------------------------------------------------
  syzygyBasis  mode ((VarP f vs):vfs)  = 
    map 
     (map (toVarP vs))  (syzygyBasis mode (f:(map fromVarP vfs)) )
  ----------------------------------------------------------------





------------------------------------------  Reading var-Polynomial


varToVarPol :: VarPol c -> String -> VarPol c

                 -- given Any non-zero var-polynomial  f  returns
                 -- the monomial var-polynomial  lc(f)*v

varToVarPol  (VarP (Pol []) _   )  _  = 
                        error "(varToVarPol (VarP (Pol []) _) _)"
varToVarPol  (VarP f        vars)  v  =
  let  
    q  = lpp f
    p  = vpp vars v  
    cp = ppP q
  in           
    VarP  (Pol [(lc f, PP p (ppCp q))])  vars
      where
      vpp []     _ =  
             error (w "varToVarPol:  variable  "
                     (w v  "  not in variable list of polynomial")
                   )
      vpp (u:vs) v =  if  u==v  then  [1]  else  0:(vpp vs v)
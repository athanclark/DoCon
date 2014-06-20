------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- continuation for Categ.hs 



module  Categ1   where   

import  Categ
import  Generic
import  Matrix
import  IParse
import  ParOpTab





------------------------------------------------------------------
--                           Monoid                             --
------------------------------------------------------------------



class  AddSemigroup a  =>  AddMonoid a 

                --  inherits operations from AddSemigroup,
                --  only  (zero x)  should give true zero element.


class  MulSemigroup a  =>  MulMonoid a                -- unity





------------------------------------------------------------------
--                            Group                             --
------------------------------------------------------------------



class  AddMonoid a  =>  AddGroup a 

        -- the Monoid should satisfy:  groupAdd == Yes, 
        --                             zero,add,neg  form a group.



class  MulMonoid a  =>  MulGroup a         -- groupMul == Yes
                                           -- mul,unity,inv
                                    






------------------------------------------------------------------
--                        Ordered Group                         --
------------------------------------------------------------------



class  AddMonoid a =>  OrdAddMonoid a              -- ordAdd==Yes
  

class  (AddGroup a, OrdAddMonoid a) =>  OrdAddGroup a 





------------------------------------------------------------------
------------------------------------------------------------------
--                            Ring                              --
------------------------------------------------------------------
------------------------------------------------------------------



class  (AddGroup a, MulSemigroup a) =>  Ring a    where

                            --  groupAdd == Yes, 
                            --  add, mul   satisfy DISTRIBUTIVITY

  ringTerm :: a -> DomainTerm

  field, euclidean, princIdeals, factorial, factorizeIsTotal, 
   hasNilp, hasZeroDiv, syzygySolvable, hasGrBas, 
    moduloIsCanonic, minNormRemValid             :: a -> PropValue
	


      -- RINGS are NON-ZERO,  IDEALS are NOT UNITY

      -- `commutative'  is from  MulSemigroup

      -- `factorial'  means an abstract unique-factorization ring,
      -- `factorizeIsTotal'   means that the function  `factorize'
      --                      is totally defined.



  char    :: a -> [Integer]          -- x  is Dummy in  (char x)
                                     -- [] means fail.

  i       :: a -> Integer -> a       --  from integer
  i_l     :: a -> Integer -> [a]   




    -------- First goes the Implementation for Properties: --------



  field x =  case  (unity_l x, commutative x)  of
                                               ([], _ ) -> No
                                               (_ , No) -> No
                                               _        -> Unknown

        -- Here we depict certain simple directed graph for the 
        -- logical dependencies, with the property names in the 
        -- nodes.
        -- The rules below free us of writing many rules for each
        -- instance.   When any property is  Redefined  for  some  
        -- instance, others are determined further automatically.
   

  euclidean x = 
       solvePropEmptyProp  (commutative x, unity_l x, field x)
  factorial x =
       solvePropEmptyProp  (commutative x, unity_l x, euclidean x)

                                  --*****************************
                                  --  Euclidean  =>  factorial  ?
                                  --*****************************

  factorizeIsTotal x =  case (factorial x, field x) of 
                                              (No, _  ) -> No
                                              (_ , Yes) -> Yes
                                              _         -> Unknown
  hasZeroDiv x =  case (hasNilp x, factorial x) of
                                             (Yes, _  ) -> Yes
                                             (_  , Yes) -> No
                                             _          -> Unknown

  hasNilp     x =  if  (factorial x)==Yes  then No   else Unknown
  princIdeals x =  if  (euclidean x)==Yes  then Yes  else Unknown

  hasGrBas x =
       solvePropEmptyProp  (commutative x, unity_l x, euclidean x)
  moduloIsCanonic  x =  
       solvePropEmptyProp  (commutative x, unity_l x, euclidean x)
  syzygySolvable  x =  
       solvePropEmptyProp  (commutative x, unity_l x, hasGrBas x )
  minNormRemValid x =  
       solvePropEmptyProp  (commutative x, unity_l x, field x    )



           -------- Implementation for other members : --------


  i    x n =  lValue (i_l  x n) ((("i "++).(w x).(' ':)) (show n))

  i_l  x n =  case  unity_l x  of  [u] ->  [times u n]
                                   _   ->  []







--------------------  Commutative Ring  --------------------------


class  Ring a  =>  CommutativeRing a         -- commutative == Yes







------------------------------------------------------------------
------------------------------------------------------------------
--             Ring with  Solvable Linear Equations             --
------------------------------------------------------------------
------------------------------------------------------------------
 
                --  Mainly, DoCon deals with this kind of rings.




class  CommutativeRing a  =>  SyzygySolvableRing a    where

                                            -- syzygySolvable==Yes

  syzygyBasis :: String -> [a] -> [[a]]                 -- total

  moduloBasis :: String -> [a] -> a -> (a, [a])
                                  -- any x from Ideal reduces to 0

  grBasis :: String -> [a] -> ([a], Matrix a)
                                          --valid if hasGrBas==Yes

              ------------------------------------------------
              -- See comments for  moduloBasis, grBasis  below
              ------------------------------------------------


              -- GCD-group functions  are valid if  factorial==Yes
  canAssoc :: a -> a              
                              -- (canAssoc x)==(canAssoc y) <=> 
                              -- x == e*y  for some invertible  e.
  canInv   :: a -> a  
  gcD      :: [a] -> a             -- gcdD, lcM  are for the Lists
  lcM      :: [a] -> a
  factorize:: a -> [(a,Integer)]       
                        -- returns  []  when fails  or for  unity


  eucNorm :: a -> Integer              -- valid if  euclidean==Yes
  divRem  :: String -> a -> a -> [a]    
                         -- "m"  means the Minimal-norm remainder:
                         --      divRem ""  5 3 -> [1,2]
                         --      divRem "m" 5 3 -> [2,-1]
                         -- "m"-mode may fail to  []  if
                         --                 minNormRemValid /= Yes

          -- Extended GCD  (GCD = u1*x1+..+un*xn)  is obtained via
          -- (moduloBasis_q . gcD)  or  grBasis_q




   ---------------------------------------------------------------
   {- 
      hasGrBas==Yes   means that 
                   either
                 a = c[x1..xn]  for the SyzygySolvable ring  c,  
                 (and  grBasis guarantees the Groebner basis)
                   OR  
                 a  is Euclidean 
                   OR
                 a = (b,c)   where  b,c  posess  hasGrBas property
                   OR
                 a = [b]  a direct sum of several copies of  b,
                          where  b  posesses  hasGrBas.

      grBasis  mode fs --> (groebnerBasis, mt)

        Here the matrix  mt  is also accumulated such that 
              mt*(transp (Mt [fs])) == transp (Mt [groebnerBasis])
        
        mode = ""  |  "r" 
                 "r"  means to reduce the tails of polynomials too
                      (if  fs  are polynomials !)
   -}
   ---------------------------------------------------------------


   ---------------------------------------------------------------
   {- 
      (moduloBasis mode xs x) ->  (r, qs)

         reduces  x  to remainder  r  modulo basis  xs   and accu-
         mulates the vector (list)  qs  of quotients such that
                       x = b1*q1+..+bn*qn + r   

         Requirement:  x<-Ideal(xs) <==> r==zero
                                --  - the Detachability condition.

         Zeroes are NOT allowed in  xs.

         mode =  "" | "c" | "g" | "cg"   

           mode = ('c':_)  means the Strong Detachablity :
                            x-y <- Ideal(basis)  <==>  r(x)==r(y).

           'c'  mode is valid if  moduloIsCanonic == Yes.

           In this case  (moduloBasis ('c':_) basis)   can be con-
           sidered as a canonical projection to the Quotient-Ring.

           If there is a  Groebner bases  structure on the ring  
                           (hasGrBas==Yes),  
           then  moduloBasis  can be computed through the Groebner
           basis and the reduction by the  Groebner basis  to  the 
           normal form.

           The mode  'g'   is for this case.  

           It means that the  xs  is already a Groebner basis, 
           hence the first stage of above reduction will be  skip-
           ped.
           For the Cartesian Product  'g'  means that all the com-
           ponent domain(s) have the 'g' quality.
   -}
   ---------------------------------------------------------------



      -----------------------------------------------------------
      -- Euclidean rings  are also treated as the Rings with  the
      -- Groebner bases
      -- (and a Field is a Euclidean ring too).
      -- In such a ring the reduction is the Euclidedan remainder
      -- modulo  GCD(xs)
      -----------------------------------------------------------



   ---------------------------------------------------------------
   {- euclidean==Yes   
            means that the functions   eucNorm, divRem  supply the  
            Euclidean structure on the ring. 
      FUTHERMORE: 
      we require for each  d   \x -> divRem x d
      to be a Canonical projection modulo d
      i.e.  x-y <- Ideal(d)  <=>  (divRem x d)==(divRem y d).

      A  Field  is considered as a trivial  Euclidean ring.
   -}
   ---------------------------------------------------------------




  canAssoc x =  divide x (canInv x)  


  lcM []     =  error "lcM []"
  lcM [x]    =  x
  lcM [x,y]  =  mul y (divide x (gcD [x,y]))
  lcM (x:xs) =  lcM [x, lcM xs]





------------------------------------------------------------------
------------------------------------------------------------------
--                          Field                               --
------------------------------------------------------------------
------------------------------------------------------------------



class  SyzygySolvableRing k =>  Field k    where     -- field==Yes

  hasAbs, real :: k -> PropValue

        -- hasAbs==Yes  means  absV  is a field Absolute Value.
        --   Also  k  should have an ordering  compare (<, <=),
        --   agreed with  absV 
        -- real==Yes    means  -1    is not a sum of squares in k






------------------------------------------------------------------
------------------------------------------------------------------
--                     Module over a ring                       --
------------------------------------------------------------------
------------------------------------------------------------------




-- Since a Haskell class does ** not allow multiple parameters **,

-- we represent a Module  b  over a Ring  c  as a  Ring  a  which 
-- is
-- * isomorphic to the direct sum    b' + c    of the coefficient
--   ring  c  and a ring obtained from the additive group  b  of 
--   vectors by supplying it with zero multiplication,
-- * supplied with the function  cMul  to multiply "vector" by 
--   "coefficient".

 

class  CommutativeRing a =>  ModuleOver a     where

  moduleTerm :: a -> DomainTerm

  -- hasNilp_m, hasZeroDiv_m, 
  syzygySolvable_m, hasGrBas_m, moduloIsCanonic_m :: 
                                                    a -> PropValue
  vec        :: a -> a
  cf         :: a -> a
  cMul       :: a -> a -> a

    -- vec,cf         are the pojections for the above direct sum.
    -- vec(cMul c v)  represents the product of vector (vec v) by 
    --                coefficient  (cf c)

    -- Modules are NON-zero,  Submodules are the proper ones.

  syzygySolvable_m  x =  
                   if  (hasGrBas_m x)==Yes  then Yes  else Unknown





class  ModuleOver a =>  SyzygySolvableModule a     where

  canAssoc_m :: a -> a
  canInv_m   :: a -> a            -- cf (canInv x)  is the factor

  moduloBasis_m :: String -> [a] -> a -> (a,[a])
  grBasis_m     :: String -> [a] -> ([a], Matrix a)
  syzygyBasis_m :: String -> [a] -> [[a]]

  canAssoc_m  x  =  cMul (inv (canInv_m x)) x


       --  ***************************************************** 
       --  see the instances of ModuleOver for  ModOverInt  etc.
       --  *****************************************************

;
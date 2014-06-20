------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------








-------------------- Category Hierarchy --------------------------







module  Categ   where   

import  Categ1
import  Generic
import  Matrix
import  IParse
import  ParOpTab



lValue  [x] _       =  x
lValue  _   message =  error message

      -- Example:   inv x =  lValue  (inv_l x)  ("inv "++(show x))



data  PropValue =  Yes | No | Unknown     deriving (Eq,Text)

data  Comp      =  LT | GT | EQ           deriving (Eq,Text)

data  Tree a =  EmptyTree  |  Tree a [Tree a]   deriving (Eq,Text)

data  BinTree a = 
  Leaf a |  BinTree a (BinTree a) (BinTree a)   deriving (Eq,Text)
                      -- left,    right subtree

type  PowPr =  [Integer]               -- polynomial power product
------------------------------------------------------------------



instance  Set  Comp       where    

  card _ =  [[3]]
  w      =  shows
  fromExpr _ (L "LT") = ([LT],"")
  fromExpr _ (L "GT") = ([GT],"")
  fromExpr _ (L "EQ") = ([EQ],"")
  fromExpr _ e        =
    ( [] , "wrong expression for type Comp:  "++(showsExpr e "") )


instance  Set  PropValue  where   

  card _ =  [[3]]
  w      =  shows
  fromExpr _ (L "Yes"    ) = ([Yes]    , "")
  fromExpr _ (L "No"     ) = ([No]     , "")
  fromExpr _ (L "Unknown") = ([Unknown], "")
  fromExpr _ e             = 
      ( [] , 
        "wrong expression for type PropValue:  "++(showsExpr e "")
      )


type  DomainTerm =  (String,DomCons,DomProps,DomFuncs,DomAttr)

domName  (nm, _ , _ , _ , _ ) =  nm
domCons  (_ , c , _ , _ , _ ) =  c
domProps (_ , _ , ps, _ , _ ) =  ps
domFuncs (_ , _ , _ , fs, _ ) =  fs
domAttr  (_ , _ , _ , _ , as) =  as

trivialDomain =  ( "", NoCons, [], [], Tree "" [] )

setDomName  n (_ , x , y , z , u ) =  (n , x , y , z , u )
setDomCons  c (x , _ , y , z , u ) =  (x , c , y , z , u )
setDomProps p (x , y , _ , z , u ) =  (x , y , p , z , u )
setDomFuncs f (x , y , z , _ , u ) =  (x , y , z , f , u )
setDomAttr  a (x , y , z , u , _ ) =  (x , y , z , u , a )



data  DomCons = 
        Basic       String 
      | Pair        DomainTerm DomainTerm            -- (a,b)
      | List        DomainTerm 
      | MatrixC     DomainTerm
      | FractionC   DomainTerm                       -- Fraction a 
      | RatioC      DomainTerm
      | Polynomial  DomainTerm [String]
                                    -- variable list, [] for `Pol'
      | EPolynomial DomainTerm [String]
      | Ideal       DomainTerm DomainTerm      --ideal description
      | ModOverIntC DomainTerm
      | NoCons


type  DomProps =  [(String,PropValue)]
type  DomFuncs =  [String] 
type  DomAttr  =  Tree String



funcNames :: String -> [String]

funcNames "set"     =  [ "card" ]  
funcNames "addSmg"  =  [ "+", "0L", "negL", "timL", "cp" ] 
funcNames "mulSmg"  =  [ "*", "1L", "InvL", "dvL", "^L" ]
                            --unity_l
funcNames "ring"    =  
        [ "ch", "iL",  "cnAs","cnInv", "dvR","eNorm",
          "gcd",  "fact", "syzB", "mB", "mBq",  "gB", "gBq"
                                  --moduloBasis
        ]
funcNames s         =  error ("funcNames  " ++ (show s))



propNames :: String -> [String]

propNames "addSmg"  =  [ "cyc",  -- cyclic
                         "grp",  -- is a group 
                         "ord"   -- `compare', <=  agree with (+)
                       ]  
propNames "mulSmg"  =  [ "comm",                -- commmutative
                          "cyc", "grp", "ord"   -- as in "add"
                       ]
propNames "ring"    =  
  [ "comm",     -- commutative
    "fld",      -- field
    "euc",      -- Euclidean 
    "minD",     -- divRem  supports the 
                --                  minimal-norm-remainder mode "m"
    "princI",   -- principal ideals ring
    "zrD",      -- has zero dvisors
    "hasNilp",  -- has nilpotents
    "fact",     -- factorial  
    "factT",    -- `factorize'  is totally defined
    "syz",      -- syzygy (linear equations) are solvable
    "GrB",      -- ring has something like Groebner basis function
    "modC"      -- `moduloBasis'  supports the 
                --                canonical remainder mode  'c'
  ]



and3 :: PropValue -> PropValue -> PropValue
and3    Yes  Yes =  Yes
and3    No   _   =  No
and3    _    No  =  No
and3    _    _   =  Unknown


solvePropEmptyProp :: (PropValue, [a], PropValue) -> PropValue 

           -- AUXILIARY for the ring property deduction, see below
solvePropEmptyProp  (No, _ , _  ) =  No
solvePropEmptyProp  (_ , [], _  ) =  No
solvePropEmptyProp  (_ , _ , Yes) =  Yes
solvePropEmptyProp  _             =  Unknown








------------------------------------------------------------------
------------------------------------------------------------------
--                              Set                             --
------------------------------------------------------------------
------------------------------------------------------------------



class  (Eq a, Text a) =>   Set a     where  
  
  setTerm ::  a -> DomainTerm  

  card    ::  a -> [[Integer]]     -- example: 
                                   -- [[4]]
                                   -- [[]]    infinite cardinality
                                   -- []      unknown

  w        ::  a -> String -> String               -- like `shows'

  fromExpr ::  a -> Expression String -> ([a],String)
             --smp  e                         msg
              

     -- fromExpr  is the reading from expression. 
     --           - see the function `r' in Generic.hs, and the
     --           files   parse/princip.txt, IParse.hs.

     -- fromExpr  needs the *sample* element  smp.  
     --
     -- If it succeeds, the result is  ( [elementOf_a], ""      ),
     -- otherwise,                     ( _            , message ),

     -- where message contains some explanation why the 
     -- expression  e  does not fit to represent an element of  a.
     --
     -- For example, let
     --   type IR = (Integer,Rational) ;
     --   infix   = infixParse parenTable opTable;
     --   smp     = (1,1%1) :: IR 
     -- Then
     --    " (1+2,1%3)+ (1,1%3)*(1,2%1)^2 "
     --                                -- (infix.lexLots) -->
     -- certain  ([e],""),  e :: Expression String.
     -- Finally,
     --    (fromExpr smp e)  --> 
     --      ...(+ (3,1/3) ((1,1/3)*(1,4%1)) --> ( [(4,5%3)], "" )

     -- Thus the definition for the class operation `fromExpr' 
     -- makes it possible to apply the general parsing `r'.
     -- See  `r'       in  Generic.hs.
     -- See  fromExpr  definitions for various instances.
     -- See the files  parse/princip.txt, IParse.hs.






------------------------------------------------------------------
------------------------------------------------------------------
--                          Semigroup                           --
------------------------------------------------------------------
------------------------------------------------------------------


class  Set a =>  AddSemigroup a   where  
                                             -- always Commutative

  addSmgTerm :: a -> DomainTerm

  cyclicAdd, groupAdd, ordAdd ::  a -> PropValue

                        -- ordAdd==Yes  means `compare' is defined 
                        --              and it is agreed with `add'
                        -- any  Ord  with its  <=, <  should agree
                        -- with  `compare'.

  add     ::  a -> a -> a
  zero    ::  a -> a        
  zero_l  ::  a -> [a]               -- x  is DUMMY in  (zero_l x)
  neg     ::  a -> a
  neg_l   ::  a -> [a]
  sub     ::  a -> a -> a
  sub_l   ::  a -> a -> [a]
  times   ::  a -> Integer -> a
  times_l ::  a -> Integer -> [a]
  compare ::  a -> a -> Comp
               -- compare x y -> LT|GT|EQ  is valid if ordAdd==Yes
  absV    ::  a -> a
               -- absV is valid if  ordAdd==Yes &  groupAdd==Yes


  absV  x =  case  (compare x (zero x))  of  LT ->  neg x
                                             _  ->  x




    -------------------------------------------------------------
    {-  
       `add'  should be an Associative and Commutative operation
              Agreed With  == 

       HERE and EVERYWHERE:

       Some operations may cause  (error ...)  and break.  
       For example, in Semigroup
                              zero x   
       may cause a break.

       "_l"-functions  never break, they return  []  when failed.

       Thus   zero_l x   may produce  [<zeroOfsemigroup>]  or [].
        
       Property values show Which operations are Totally Defined,
       for this operations there is no need in  "_l"-functions.
          
       Thus  (groupAdd x)==Yes   means that  `zero',`neg',`times' 
       are totally defined.

       *  also  (zero_l x)   tests whether the  AddSemigroup  to
          which  x  belongs has zero.
    -}
    -------------------------------------------------------------



  cyclicAdd x = case  card x  of
         [[]]  -> Unknown  
         []    -> Unknown
         [[n]] -> if ((groupAdd x)==Yes)&&(isPrimeInt n)
                                                     then  Yes
                  else                                     Unknown

  zero  x   =  lValue (zero_l x)  ((("zero "++).(w x)) "")
  neg   x   =  lValue (neg_l  x)  ((("neg " ++).(w x)) "")
  sub   x y =  lValue (sub_l x y) 
                          ( (("sub "  ++).(w x).(' ':).(w y))  "")
  times x n =  lValue  (times_l x n)  
                          ( (("times "++).(w x).(' ':)) (show n) )

                          -- lValue  may yield Break + message 


  neg_l  x  =  case  zero_l x  of  []  -> []
                                   [z] -> sub_l z x

  times_l x n  | n==1      =  [x]
               | n==0      =  zero_l x
               | n<0       =  (case  (neg_l x)  of 
                                             []  -> []
                                             [y] -> times_l y (-n)
                              )
               | otherwise =
                      let  [h] = times_l x (div n 2) 
                      in     if  even n  then  [h `add` h]
                             else          [ (h `add` h) `add` x ]






class  Set a  =>  MulSemigroup a    where

  mulSmgTerm :: a -> DomainTerm

  commutative, cyclicMul, groupMul ::  a -> PropValue

        -- `mul' should be an Associative operation agreed with ==
  mul        ::  a -> a -> a
  unity      ::  a -> a
  unity_l    ::  a -> [a]
  inv        ::  a -> a
  inv_l      ::  a -> [a]
  divide     ::  a -> a -> a
  divide_l   ::  a -> a -> [a]
  power      ::  a -> Integer -> a
  power_l    ::  a -> Integer -> [a]
  rootN      ::  String -> a -> Integer -> [a]





              -- rootN  returns []  when failed,
              -- String= "int"  means the Integer Part of the root


       -- *******************************************************
       -- `divide'  is the solving of the equation  a*x = b
       -- in algebraic domain.  x  may be NOT UNIQUE. Returned is
       -- some x, may be not the "best".   
       -- In the general case, we can only rely on that  x1-x2 is 
       -- a Zero Divisor or zero for any solutions  x1,x2.
       -- x  is unique if a ring has Not zero divisors. 
       --   Similar  are  divide_l, inv, inv_l.
       -- *******************************************************



  cyclicMul x = case  card x  of
     []    -> Unknown  
     [[]]  -> Unknown  
     [[n]] -> if ((groupMul x)==Yes)&&(isPrimeInt n) then  Yes
              else                                         Unknown

  commutative x =  if (cyclicMul x)==Yes  then  Yes  else  Unknown



  unity  x  =  lValue  (unity_l x)  ((("unity "++).(w x)) "")
  inv    x  =  lValue  (inv_l   x)  ((("inv "  ++).(w x)) "")

  divide  x y =  lValue  (divide_l x y)  
                           ((("divide "++).(w x).(' ':).(w y)) "")
  power   x n =  lValue  (power_l x n) 
                         ( (("power "++) .(w x).(' ':)) (show n) )
  inv_l  x  =  case  unity_l x  of  []   -> []
                                    [un] -> divide_l un x

  power_l x n  | n==1      =  [x]
               | n==0      =  unity_l x
               | n<0       =  (case  (inv_l x)  of 
                                             []  -> []
                                             [y] -> power_l y (-n)
                              )
               | otherwise =
                      let  [h] = power_l x (div n 2) 
                      in     if  even n  then  [ h `mul` h ]
                             else          [ (h `mul` h) `mul` x ]
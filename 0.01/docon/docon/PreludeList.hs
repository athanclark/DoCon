------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





      --  List  is one of the  Vector  representations.

      --  For a ring a  [a]  is supplied with the structure of
      --  the Direct Sum of  n  copies of a ring  a.


      ----------------------------------------------------------
      --  Algebraic operations and properties refer to the lists
      --  of one and the same length.  
      --  For example:
      --    mul, divide  for  xs, ys  make sense only for  xs,ys
      --       of the same length;
      --    SyzygySolvableRing xs   for  xs :: [a]
      --       means that the ring of all  ys :: [a]  such that 
      --       (length ys)==(length xs)   has the property 
      --       SyzygySolvableRing.
      ----------------------------------------------------------




module  PreludeList 
  (
    Num(..),Set(..),AddSemigroup(..),AddMonoid(..),AddGroup(..),
      MulSemigroup(..),MulMonoid(..),MulGroup(..),
    Ring(..),CommutativeRing(..),SyzygySolvableRing(..),

    binOpList, binOpListD
  )

where


import  PreludeChar
import  Categ
import  Categ1
import  Matrix
import  ParOpTab
import  IParse  --?



------------------------------------------------------------------

binOpListD :: (a->b->c) -> [a] -> [b] -> [c]

binOpListD  _ []     []     =  []
binOpListD  f (x:xs) (y:ys) =  (f x y):(binOpListD f xs ys)


                  -- The following variant appends the exheeding
                  -- part of a list.
                  -- Only there is one type  a  instead of  a,b,c

binOpList :: (a->a->a) -> [a] -> [a] -> [a]

binOpList  _ []     gs     =  gs
binOpList  _ fs     []     =  fs
binOpList  f (x:xs) (y:ys) =  (f x y):(binOpList f xs ys)



allNotNullThenUnpar xs =  
              if  any null xs  then []  else  [ map (\[x]->x) xs ]



------------------------------------------------------------------
-- Auxiliary function for the list parsing.

-- ":" is an operation like "+".
-- See  manual on "infix", ParOpTab.hs, IParse.hs.


fromExprL []    _ =
               ( [], "(fromExpr <List> _): empty sample list \n" )
fromExprL (x:_) e = fre e
  where
  fre (L "nil")             = ( [[]], "" )
  fre (E (L ":") [e1] [e2]) = case  (fromExpr x e1, fre e2)  of

      ( ([y],"" ), ([ys],"" ) ) -> ( [y:ys], "" )
      ( ([y],"" ), (_   ,msg) ) -> 
            ( [], 
              (w "(fromExpr <List> e): could not parse the tail.")
                $('\n':)$(w "tail = ")$(showsExpr e2 "\n\n")
            )
      ( (_  ,msg), _          ) -> 
            ( [], 
              (w "(fromExpr <List> e): could not parse the head.") 
                $('\n':)$(w "head = ")$(showsExpr e1 "\n\n")
            )
  fre e                     =  
            ( [], 
              ( "(fromExpr <List> e): wrong syntax for e = "++ ) $
              ('\n':)$(showsExpr e "\n\n")
            )




{-
  RESERVE.  Attempt to supply  [,]  as the operations.

  fre ( E  (L "[")  []                  [L "]"] ) = ( [[]], "" )
  fre ( E  (L "]")  [L "["]             []      ) = ( [[]], "" )
  fre ( E  (L "]")  [E (L "[") [] [e]]  []      ) = fromPairs e
  fre ( E  (L "[")  _                   _       ) =  
      ( [], 
        ( "(fromExpr <List> e):  [,] wrongly used in  e = "++ ) $
        ('\n':)$(showsExpr e)$ ""
      )     
  fre ( E  (L "]")  _                   _       ) =  
      ( [], 
        ( "(fromExpr <List> e):  [,] wrongly used in  e = "++ ) $
        ('\n':)$(showsExpr e)$ ""
      )     


  fromPairs e =  case  fromExpr x e  of

    ([y],"") -> ([[y]], "")       -- this was a singleton (no ",")
    _        ->
      (case  e  of

        (E (L ",") [e1] [e2]) ->
            (case  (fromExpr x e1, fromPairs e2)  of

              ( ([y],"" ), ([ys],"" ) ) -> ( [y:ys], "" )
              ( ([y],"" ), (_   ,msg) ) -> 
                              ( [], "(fromExpr <List> e): could"++
                                    " not parse the tail"
                              )
              ( (_  ,msg), _          ) -> 
                              ( [], "(fromExpr <List> e): could"++
                                    " not parse the element"
                              )
            )

        (E (L ",") _    _   ) ->
          ( [], 
            ("(fromExpr <List> e):  [..,..]:  wrong expression"++)
            $ (" somewhere between  , "++) 
            $("\ne =  "++) $ (showsExpr e "\n\n")
          )
        _                     ->
          ( [], 
            ( "(fromExpr <List> e):  inside  [..] should be "++ )
            $ ("nested pairs, "++) $
            ("\ne =  "++) $ (showsExpr e "\n\n")
          )
      )

   -}
------------------------------------------------------------------










---------------------------  Set  --------------------------------


instance  Set a  =>  Set [a]   where   

  setTerm (x:_) = 
            (setDomFuncs    (funcNames "set")  
               (setDomCons  (List (setTerm x)) trivialDomain
            ))

  card []     = error "(card []):  list should not be empty"
  card (x:xs) = case  (card x)  of  []    -> []
                                    [[0]] -> [[1]]
                                    [[n]] -> [[]]

  w []     =  shows "[]"
  w (x:xs) =  case  domCons (setTerm x)  
              of
                (Basic "Char")-> shows (x:xs)
                _             -> ('[':).(w x).(w1 xs).(']':)
                                   where
                                   w1 []     = id
                                   w1 (x:xs) = 
                                           (",  "++).(w x).(w1 xs)

  fromExpr = fromExprL







---------------------  AddSemigroup  -----------------------------


instance  AddGroup a =>  AddSemigroup [a]    where

  addSmgTerm (x:_) =  

    (setDomFuncs  (funcNames "addSmg")  
      (setDomProps
         [ ("cyc+", Unknown), --
           ("gr+",  groupAdd x),  ("ord+", Unknown)
         ]
         (setDomCons  (List (addSmgTerm x))  trivialDomain
    ) )  )


  groupAdd (x:_) =  groupAdd x

  -- cyclicAdd
  -- ordAdd

  add []     xs     =  xs
  add xs     []     =  xs
  add (x:xs) (y:ys) =  (add x y):(add xs ys)

  zero    _     =  []
  zero_l  _     =  [[]]
  neg     xs    =  map neg xs             
  neg_l   xs    =  [map neg xs]
  sub_l   xs ys =  [add xs (map neg ys)]
  times_l xs n  =  [ map (\x-> times x n) xs ]



instance  AddGroup  a =>  AddMonoid [a]  
instance  AddGroup  a =>  AddGroup  [a]  






--------------------------- MulSemigroup -------------------------


instance  MulSemigroup a =>  MulSemigroup [a]   where

  mulSmgTerm (x:_) =  

    (setDomFuncs  (funcNames "mulSmg")  
      (setDomProps
         [ ("cyc*", cyclicMul   x ),
           ("comm", commutative x ),
           ("gr*",  groupMul    x ),
           ("ord*", Unknown)
         ]
         (setDomCons  (List (mulSmgTerm x))  trivialDomain)
    ) )


  mul =  binOpList mul     -- ************************************
                           -- This implies that the Exheeding part 
                           -- of a list is Appended to the result.
                           -- ************************************

  unity       =  map unity 

  unity_l xs =  allNotNullThenUnpar (map unity_l xs)
  inv_l   xs =  allNotNullThenUnpar (map inv_l   xs)

                                 -- divide (_l)  makes sense only 
                                 -- for the lists of Equal length
                                 --
  divide_l xs ys = allNotNullThenUnpar (binOpListD divide_l xs ys)

  power_l  xs n =  allNotNullThenUnpar (map (\x-> power_l x n) xs)



------------------------------------------------------------------

instance  MulMonoid a =>  MulMonoid [a]  
instance  MulGroup  a =>  MulGroup  [a]  





----------------------------  Ring  ------------------------------

instance  Ring a =>  Ring [a]    where
                  
                         -- Direct Sum of  n  copies of a ring  a.


  ringTerm (x:xs) = 

    (setDomFuncs      (funcNames "ring")
      (setDomProps    (listRing_props (ringTerm x))
         (setDomCons  (List (ringTerm x))  trivialDomain
         )
    ) )
      where
      listRing_props xTerm =  []   --SO FAR



  hasZeroDiv  (x:xs) =  if  (hasZeroDiv x)==Yes  then  Yes
                        else
                          if  null xs  then hasZeroDiv x  else Yes

  hasNilp        (x:_ ) =  hasNilp x    
  field          (x:xs) =  if  null xs  then  field x      else No
  euclidean      (x:xs) =  if  null xs  then  euclidean x  else No
  princIdeals    (x:_)  =  princIdeals x 
  syzygySolvable (x:_)  =  syzygySolvable x
  factorial      (x:xs) =  if  null xs  then  factorial x  else No
  factorial (x:xs) = if  null xs  then factorizeIsTotal x  else No

  hasGrBas        (x:_ ) =  hasGrBas x
  moduloIsCanonic (x:_ ) =  moduloIsCanonic x
  minNormRemValid (x:xs) = 
                    if  null xs  then  minNormRemValid x  else  No

  i_l   xs n  =  allNotNullThenUnpar (map (\x-> i_l x n) xs)

  char  (x:_) =  char x 




instance  CommutativeRing a =>  CommutativeRing [a]






------------------------------------------------------------------

instance  Ring a =>  Num [a]   where  (+)    = add
                                      (-)    = sub
                                      negate = neg
                                      (*)    = mul
                                            -- (/)    = divide







instance  SyzygySolvableRing a =>  SyzygySolvableRing [a]  
  where

                       -- for  moduloBasis  the mode 'g' means 'g'
                       -- for Each Projection of the basis  xss.

  moduloBasis  modes xss ys =
    let
      xssT     =  transpose xss
      (rs,qss) =  unzip ((binOpListD (moduloBasis modes) xssT) ys)
    in
      (rs, transpose qss)


  ----------------------------------------------------------------
        -- Let we have the vectors  vects,  length(vects) = m,
        -- each of length  n,  and let  bas_i  be the syzygy basis
        -- for the vector of  i-th  components.
        --   Let  basV_i  is obtained by prepending of (i-1) zero-
        -- es and appending of  (m-i) zeroes  to each  element  of 
        -- each vector from  bas_i.
        --   Then  basV_1 ++...++ basV_m   are the independent sy-
        -- zygies for  vects.

  syzygyBasis  mode vects =
    let
      x      =  head (head vects)
      zeroV  =  map (const (zero x)) vects

      extendVec  ls rs =  map (\x-> ls++(x:rs)) 

      extendBases _  []     []          =  []
      extendBases ls (z:rs) (bas:bases) =  
                                    (map (extendVec ls rs) bas) ++
                                    (extendBases (z:ls) rs bases) 
      extendBases _  _       _          = 
             error "Error in DoCon:   syzygyBasis  for direct sum"

      rBases =  map  (syzygyBasis mode) (transpose vects)
    in
      extendBases  [] zeroV rBases
  ----------------------------------------------------------------




{- 
         ************* CONTINUE FROM HERE *******************

  grBasis  mode vects =  
    let
      x     =  head (head vects)
      zeroV =  map (const (zero x)) vects
      extendVec  ls rs =  map (\x-> ls++(x:rs)) 

      extendBases _  []     []          =  []
      extendBases ls (z:rs) (bas:bases) =  
                                     (extendVec ls rs bas) ++
                                     (extendBases (z:ls) rs bases) 
      extendBases _  _       _          = 
                 error "Error in DoCon:   grBasis  for direct sum"
    in
      extendBases  [] zeroV (map (grBasis mode) (transpose vects))

-}







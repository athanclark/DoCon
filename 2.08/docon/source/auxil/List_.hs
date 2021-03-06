--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------





module List_ 

-- Set instance for the domain [a]  of the lists over the `a'.
--
-- All needed from here is  reexported by  DPrelude.

where
import Data.FiniteMap (lookupFM, addToFM)

import Prelude_  (PropValue(..), InfUnn(..), Z, eFM)
import Iparse_   (Expression(..), showsExpr        )
import Categs    (Dom(..), CategoryName(..), Domain1(..), OSet(..), 
                  Property_OSet(..)
                 )
import Set_      (Set(..), compareTrivially)





--------------------------------------------------------------------
binOpListD :: (a -> b -> c) -> [a] -> [b] -> [c]

binOpListD _ []     []     = []
binOpListD f (x:xs) (y:ys) = (f x y):(binOpListD f xs ys)
binOpListD _ _      _      =  
       error "List1.binOpListD f xs ys:   xs,ys  differ in length\n"
        
                  -- The second binOp variant appends the exceeding
                  -- part of a list.
                  -- Only there is one type  a  instead of  a,b,c:
          
binOpList :: (a->a->a) -> [a] -> [a] -> [a]

binOpList _ []     gs     = gs
binOpList _ fs     []     = fs
binOpList f (x:xs) (y:ys) = (f x y):(binOpList f xs ys)


--------------------------------------------------------------------
fromExprL :: (Set a) => [a] -> Expression String -> ([[a]],String)

  -- Auxiliary function for the list parsing.
  --
  -- ":" is an operation like "+".
  -- See  manual on "infix", OpTab_.hs, Iparse_.hs.

fromExprL []    _ =
                 ( [], "(fromExpr <List> _): empty sample list \n" )
fromExprL (x:_) e = fre e
  where
  fre (L "nil")             = ( [[]], "" )

  fre (E (L ":") [e1] [e2]) = case  (fromExpr x e1, fre e2)  of

         ( ([y],"" ), ([ys],"" ) ) -> ([y:ys], "")
         ( ([_],"" ), _          ) -> 
            ([], 
             shows "fromExpr <List> e:  could not parse the tail." $
             ('\n':) $ shows "tail = " $ showsExpr e2 "\n\n"
            )
         _                         -> 
           ([], 
            shows "(fromExpr <List> e): could not parse the head." $
            ('\n':) $ shows "head = " $ showsExpr e1 "\n\n"
           )
  fre e                     =  
              ([], ("fromExpr <List> e:  wrong syntax for e = "++) $
                   ('\n':) $ showsExpr e "\n\n"
               )


--------------------------------------------------------------------
instance Dom []  
  where 
  sample = head
  dom _  = error "dom []:  dom  is not defined for List\n"



{- reserve *************************************
instance (Convertible a b) => Convertible a [b]  
  where
  cvm _ []     = Nothing
  cvm a (b:bs) = case  cvm a b  of 
                            Just b' -> Just (b':(map (const b') bs))
                            _       -> Nothing
                                 -- example:  cv 'f' "abc" = "fff"
instance (Convertible a b) => Convertible [a] [b]  
  where
  cvm []     _     = Just []
  cvm _      []    = Nothing
  cvm (a:as) (b:_) = case  cvm a b  of
                                Just a' -> Just (a':[cv x b| x<-as])
                                _       -> Nothing
               -- example:  cv [1,2,3] ((1:/2):_) = [1:/1,2:/1,3:/1]
***********************************
-} 




instance (Set a) => Set [a]   
  where   
  fromExpr  = fromExprL
  compare_m = compareTrivially

  showsDomOf []    = ("(List ?)"++)
  showsDomOf (x:_) = ("(List "++). showsDomOf x .(')':)

  baseSet xs dom = (case  (lookupFM dom Set, xs)  
                    of
                      (Just (D1Set o), _  ) -> (dom, o)
                      (_             , x:_) -> bs x
                      _                     -> 
                                           error "baseSet [] dom'\n"
                   )
    where
    bs x = (addToFM dom Set $ D1Set o, o)
      where
      o = OSet {osetSample  = [x],
                membership  = bel', 
                osetCard    = Infinity,
                osetPointed = Just $ Just [x],
                osetList    = Nothing,
                osetBounds  = (Nothing,Nothing,Nothing,Nothing),
                osetProps   = props',
                osetConstrs = [],
                osetOpers   = []
               }                        
        where
        bel' 'r' ys = not (null ys) && all (bel 'r') ys
        bel' _   ys = not (null ys) 
        bel         = membership $ snd $ baseSet x eFM

        props' = [(IsBaseSet, Yes), (Finite, No),
                  (FullType , No ),
                         -- for [] does not belong to the base set
                  (OrderIsTrivial,Yes),
                  (OrderIsTotal  ,No ), (OrderIsNoether, Yes),
                  (OrderIsArtin  ,Yes)
                 ]  


--------------------------------------------------------------------
cubeList_lex :: (Show a,Ord a,Enum a) => [(a,a)] -> [[a]]
                                         --bounds  
  -- lists in the lex-increasing order all the vectors  [a(1)..a(n)]
  -- over `a' in the cube   a(i) <- [l(i) .. h(i)],  1 <= i <= n,
  -- defined by  bounds = [(l(1),h(1))..(l(n),h(n))],  l(i) <= h(i)

cubeList_lex bns = case  (bns, all (\ (l,h)->l <= h) bns)  of

  ([], _    ) -> error "cubeList_lex []\n"
  (_ , False) -> error $ ("cubeList_lex bounds, \n"++) $
                         ("bounds = "++) $ shows bns
                         "\n\nl > h in some (l,h) from  bounds\n"
  _           -> lst bns
                where
                lst [(l,h)]    = [[i]| i <- [l..h]]
                lst ((l,h):ps) = concat [map (i:) xss | i <- [l..h]]
                                                 where  xss = lst ps
                              
{-# specialize cubeList_lex :: [(Z,Z)] -> [[Z]] #-}

 ;








{-
**********************
RESERVE.  
Attempt to view  [ , ]  as the operations.

  fre ( E  (L "[")  []                  [L "]"] ) = ( [[]], "" )
  fre ( E  (L "]")  [L "["]             []      ) = ( [[]], "" )
  fre ( E  (L "]")  [E (L "[") [] [e]]  []      ) = fromPairs e
  fre ( E  (L "[")  _                   _       ) =  
      ( [], 
        ("(fromExpr <List> e):  [,] wrongly used in  e = "++) $
        ('\n':) $ showsExpr e ""
      )     
  fre ( E  (L "]")  _                   _       ) =  
      ( [], 
        ("(fromExpr <List> e):  [,] wrongly used in  e = "++) $
        ('\n':) $ showsExpr e ""
      )     

  fromPairs e =  case  fromExpr x e  of

    ([y],"") -> ([[y]], "")       -- this was a singleton (no ",")
    _        ->
      (case  e  of
        (E (L ",") [e1] [e2]) ->
            (case  (fromExpr x e1, fromPairs e2)  of
              ( ([y],"" ), ([ys],"" ) ) -> ( [y:ys], "" )
              ( ([y],"" ), (_   ,msg) ) -> 
                               ([], "(fromExpr <List> e): could"++
                                    " not parse the tail"
                               )
              ( (_  ,msg), _          ) -> 
                                 ([], "(fromExpr <List> e): could"
                                      ++" not parse the element"
                                 )
            )
        (E (L ",") _    _   ) ->
             ([], 
              ("fromExpr <List> e:  [..,..]:  wrong expression"++) $
              (" somewhere between  , "++) $ ("\ne =  "++) $ 
              showsExpr e "\n\n"
             )
        _                     ->
          ([], 
           ("fromExpr <List> e:  inside  [..] should be "++) $
           ("nested pairs, "++) $ ("\ne =  "++) $ showsExpr e "\n\n"
          )
      )
**********************************************
-}











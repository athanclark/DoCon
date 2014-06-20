------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- Parentheses and Operation symbol tables for the infix parsing.





module  ParOpTab  where

import  IParse



------------------------------------------------------------------
-- Edit the below scripts to change the parenthesis symbol list or
--
-- the infix operation symbol list.
--
-- See the files  princip.txt, IParse.hs.
------------------------------------------------------------------



                 -- These are the DoCon prelude parentheses pairs.

parenTable ::  ParenTable String
parenTable =   [  ("(",")"), ("{","}"), ("<",">")  ]




------------------------------------------------------------------

-- The Operation Table for the  infixParse  function.

-- The DoCon prelude infix table:


opTable ::  OpTable String
opTable =        
         -- (0,r)            (l,r)            (l,0)
  [
   ("+",  ( [(0,1,210,190)], [(1,1,100,100)], []              ) ),
   ("-",  ( [(0,1,210,190)], [(1,1,100,100)], []              ) ),
   ("*",  ( []             , [(1,1,195,195)], []              ) ),
   ("^",  ( []             , [(1,1,200,199)], []              ) ),
   ("/",  ( []             , [(1,1,196,196)], []              ) ),
   ("%",  ( []             , [(1,1,196,196)], []              ) ),
                                        -- usually, for ratioanals

   (":/", ( []             , [(1,1,196,196)], []              ) ),
                                        -- usually, for fractions

   (",",  ( []             , [(1,1, 80, 70)], []              ) ),
                                    -- usually, a pair constructor

   ("'",  ( [(0,1,220,190)], []             , []              ) ),
                                 -- usually, a  Char  constructor.
                                 -- Thus  'a  reads to  'a'

   (":",  ( []             , [(1,1, 80, 70)], []              ) )
                                    -- usually, a list constructor


   --("[",  ( [(0,1, 50, 40)], []             , []              ) ),
   -- ?? more list constructors 
   --("]",  ( []             , []             , [(1,0, 20, 20)] ) )
                                                      --?           

  ]





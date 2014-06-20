------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------





module  PreludeChar ( Set(..) )    where

import  Categ
import  Categ1
import  Matrix
import  IParse  




instance  Set Char    where   

  w   =  shows

  fromExpr _ (E (L "'") [] [L [c]]) =  ([c],"")
  fromExpr _ e                      =  
          ( [], 
            "(fromExpr <Char> e):  wrong e = " ++ (showsExpr e "")
          )

  card    _ =  [[128]]    -- ?

  setTerm _ =  (setDomFuncs  [ "card" ]  
                  (setDomCons   (Basic "Char") 
                     (setDomName  "Char" trivialDomain )))
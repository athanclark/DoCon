------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- Parsing Polynomial  

-- Study first `fromExpr' operation from  Pol.Set,  VarPol.Set




module  ExprPol  where

import  PreludeInteger
import  PreludeList
import  Categ
import  Categ1
import  Generic
import  PP
import  Pol
import  VarPol
import  Matrix
import  IParse





exprToPol :: CommutativeRing a => 
             [String] -> a -> a  -> PPComp -> Expression String ->
             --vars      zero unity cp        e
                                                 ([Pol a], String)

           -- SO FAR it requires a ring  a  with  UNITY.

           -- If  vars = []  then the variables are "x1","x2",...
           -- else             the variables are listed in  vars.


exprToPol  vars zr un cp e  =  rd e
  where

  rd e =  case  fromExpr un e  of        -- try coefficient first

    ([c],"") ->  ([cToPol zr cp c], "")
    _        -> 
      (case  e  of
        (E (L "-") []   [e2]) -> f "-u" ([],"") (rd e2)
        (E (L "-") [e1] [e2]) -> f "-"  (rd e1) (rd e2)
        (E (L "+") [e1] [e2]) -> f "+"  (rd e1) (rd e2)
        (E (L "*") [e1] [e2]) -> f "*"  (rd e1) (rd e2)
        (E (L "/") [e1] [e2]) -> f "/"  (rd e1) (rd e2)
        (E (L "^") [e1] [e2]) -> 
                             pw (rd e1) (fromExpr (1::Integer) e2)
        (L s)                 -> variable s (elem s vars) 
        _                     ->
         ( [], "exprToPol: wrong expression  "++(showsExpr e "") )
      )
        where

        f "-u" _        ([f],"") = ( [(-f)], "" )
        f "-"  ([f],"") ([g],"") = ( [f-g] , "" )
        f "+"  ([f],"") ([g],"") = ( [f+g] , "" )
        f "*"  ([f],"") ([g],"") = ( [f*g] , "" )
        f "/"  ([f],"") ([g],"") = 
                  case  divide_l f g  of
                    [q] -> ( [q], "" )
                    []  -> ( [] , "exprToPol:  expression = \n" ++
                                  (showsExpr e ")\n")           ++
                                  "failed to divide with  / "
                           )

        f _    ([x],"") pair     = pair
        f _    pair     _        = pair

        pw  ([f],"" ) ([n],"" ) = ([f^n], "" )
        pw  ([f],"" ) (_  ,msg) = ([]   , msg)
        pw  (_  ,msg) ([n],"" ) = ([]   , msg)
 
        variable s       True  = varFromList s (span (/=s) vars)
        variable ('x':s) False =
              (case  (reads s :: [(Integer,String)] )  of

                [(i,"")] -> let  p = (copy (i-1) 0)++[1] :: PowPr
                            in
                                      ( [Pol [(un,PP p cp)]], "" )
                _        -> 
                 ([], "exprToPol: wrong syntax for  xi -variable")
              )

        varFromList s (_ ,[]) =
             ( [], "exprToPol: variable  " ++s++ "  not in list" )
        varFromList _ (vs,_ ) = 
                            let  p=(map (const 0) vs)++[1] ::PowPr
                            in
                                 ( [Pol [(un,PP p cp)]], "" )
                               




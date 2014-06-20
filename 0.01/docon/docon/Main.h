module  Main ( main )   where

import  PreludeChar
import  PreludePair
import  PreludeList
import  PreludeRational
import  PreludeInteger
import  Generic
import  Categ 
import  Matrix
import  Fraction
import  IParse  
import  ParOpTab
  

type  Z  =  Integer
type  FZ =  Fraction Integer



main = let  
         un = 1:/1  :: FZ
         zr = zero un

         a = un
         b = un
         r11 = un
         r12 = zr
         r21 = zr
         r22 = un         
         row1 = [r11,r12]
         row2 = [r21,r22]

         [q,rm] = divRem "" b a
         row2'  = row2 - (map (mul q) row1)

       in  

         writeFile 
           "RESULT" 
           ( 
             (w row2' "")  ++ "\n\n"     ++ 
             "zr = "       ++ (show zr)  ++
             "   rm = "    ++ (show rm)  ++
             "rm==zr =  " ++ (show (rm==zr))
             
             -- (w a' "  ") ++ (w b' "    ") ++ (w rows' "")
           )
           exit done



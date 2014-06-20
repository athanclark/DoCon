module Main(main) where

import Iparse_
import OpTab_

------------------------------------------------------------------
--  This is to test and demonstrate the   infixParse   function.
------------------------------------------------------------------




main =  let  
          inf s =  case  infixParse parenTable opTable (lexLots s)
                   of
                     ([e], ""     ) -> showsExpr e
                     (_  , message) -> (message++)

          s1 =  "2* ~ b* ~ c  def"    
 
          --" +  ab-  cd        "
          --s2 =  " 1*2 + 3*4 + 5 - 6 "
          --s3 =  " [1,2,3] "

               --"  ( (1:2:nil), (a+1,b) )  "
               -- " (2*(1+(x**y)))^3 "                
               -- " (1+2) * * 3  "
             
        in     
        writeFile  
          "result" 
          ( 
            (
             (shows s1) 

               -- .('\n':) .(shows s2) .('\n':) .(shows s3)

               .('\n':).('\n':) .(inf s1)

               --.('\n':).('\n':)
               --.(inf s2)
               --.('\n':).('\n':)
               --.(inf s3)
            )
            ""
          )









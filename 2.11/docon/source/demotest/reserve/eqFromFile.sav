-- RESERVE   for  ReduceDecomp.hs
--
-- Reading equations from file.


import Maybe   (fromJust, isJust                     )
import List    (partition, genericDrop, genericLength)
import DExport 


main = interact (parseComputeShow . pairNeighbours . separate ';')
  
  -- This is interface part.  Usage:  ./run < inputFile > outputFile
  --
  -- It reads the string from Input, parses it to equation, 
  -- processes them, makes output string and writes it to Output.
  -- Example for input syntax:
  --
  -- n   = 3;
  -- g11 = - ((x1-x2)*(x2-x3)*(x3-x1))^2 ;
  -- 
  -- n   = 6;
  -- g21 = product [x1-x2,x2-x5,x5-x1,  x2-x3, (x3-x6)^2, x6-x2,
  --                x1*(x2-2*x3)^2,     x3-x4,x4-x5,x5-x3
  --               ];
  -- ...

parseComputeShow :: [(String,String)] -> String 
                              -- each pair contains equation strings
parseComputeShow pairs =      -- for  n  and for polynomial
  showsResults 
    (map processEqPair $ [(nstr, pstr, lexemes nstr, lexemes pstr) |
                          (nstr,pstr) <- pairs
                         ]
    ) "\n"
  where  -- Example:  lexemes  " n  =12;  g11 = x*(! "  -->
         --    ["n", "=", "12", ";", "g11", "=", "x", "*", "(", "!"]

  -- ask variable name ?

  msgEqs = ("input should be several pairs of "++) .
           ("equations of kind\n  <name> = <expression> "++)

  processEqPair (nstr, pstr, ["n","=",lx],  _:"=":ys) = 
   
           (("----------\n"++).(nstr++).(';':).(pstr++).(";\n\n"++),
            prEqP (read lx :: Z) (makePolStrings ys)
           )
  processEqPair _                                     = 
                                                 error $ msgEqs "\n"

  prEqP n polStrings = reduceSymmDecompose pcp f 
          where
          f       = product1 $ map (smParse unP) polStrings
          unP     = cToPol o vars dQ un        -- 1 of P = Z[x1..xn]
          un      = 1:/1  :: Fraction Z
          dQ      = upField un eFM
          vars    = map (('x':).show) [1..n]   -- ["x1".."x<n>"]
          (pcp,o) = (pLexComp, lexPPO n)

       -- Expression for polynomial goes after '='.
       -- It is either       <simpleExpression>  or
       --                    product [<list of simple expressions>],
       -- `,' is the separator for list elements.
       -- Example of <simple expression>:  " -2*(x1 +3*x2)^4 *x5^2 "
       -- makePolStrings makes string for each simple expression.
       --
  makePolStrings (pname:"[":lxs) = 
     if
       elem pname ["product","product1"]  &&  (last lxs)=="]" 
                                 then  
                                 map concat $ separate "," $ init lxs
     else 
       error ("input polynomial expression is either  simple  or "++
            "it is\n   product [ ls ]  \n,"++
            "ls  a list of simple expressions separated by commas\n"
             )
  makePolStrings lxs                 = [concat lxs]

  showsResults []                            = id
  showsResults ((showsData,(sym,inE)): ress) =
              showsData .
              ("sym =\n  "++) .shows sym .('\n':) . 
              ("inE =\n  "++) .shows inE .('\n':) .showsResults ress
   
 
  lexemes :: String -> [String]
    -- Break string to list of lexemes - according to standard
    -- Haskell set of delimiters.
    -- Example:                   " n  =12; g11= x1*(x2  " 
    --         -->
    --       ["n", "=", "12", ";", "g11", "=", "x1", "*", "(", "x2"]

  lexemes xs = case  lex xs  of  [("", _  )] -> []
                                 [(lx, xs')] -> lx:(lexemes xs')
                                 _           -> []



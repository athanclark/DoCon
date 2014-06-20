------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------



-- Parsing generic infix expressions





module  IParse  where




data  Expression a = 
         L a  |  E (Expression a) [Expression a] [Expression a]   
                                                 deriving(Eq,Text)

     -- L  is a tag of lexeme expression,
     -- E  -           expression.
     -- a  is the type of lexeme.

     -- E op ls rs   
     --   denotes an expression which is an application of the
     --   *operation expression*  op,  the left-hand argument list 
     --   ls,  and the right-hand argument list  rs.

     --   Usually,  op  is a lexeme, say (L "++").

     -- Example:  
     -- If  a = String,  then the string   " (1+ 22)*- 3a " 
     -- may parse to the expression
     --              (E  (L "*")  [ (E (L "+") [L "1"] [L "22"]) ]
     --                           [ (E (L "-") []      [L "3a"]) ]  
     --              )



------------------------------------------------------------------
lexLots ::  String -> [Expression String]

     -- Break string to the list of lexems - according to standars
     -- Haskell set of delimiters.
     -- Example:    (lexLots  " {2+ 33}*3 " )  ->
     --       [ L "{", L "2", L "+", L "33", L "}", L "*", L "3" ]

lexLots xs =  case  lex xs  of  [("", _  )]-> []
                                [(lx, xs')]-> (L lx):(lexLots xs')
                                _          -> [] 



showsExpr ::  Text a =>  Expression a -> String -> String
                                   
showsExpr (L x)        = shows x     --pretty print for expression
showsExpr (E op ls rs) = 
           let  
             sh_op = showsExpr op
             sh_ls = map showsExpr ls
             sh_rs = map showsExpr rs
           in
             ('(':)  .sh_op  
               .(' ':).('[':) .(foldl (.) id sh_ls) .(']':).(' ':)
               .(' ':).('[':) .(foldl (.) id sh_rs) .(']':).(' ':)
             .(')':)

showsExpr _            =  error "(showExpr e): wrong expression e"




------------------  Infix Operation Table  -----------------------



type  OpDescr =  (Int,Int,Int,Int)

   -- (left arity, right arity, left precedence, right precedence)


type  OpGroupDescr a =  (a, ([OpDescr],[OpDescr],[OpDescr]))

    --                        0r_class   l0_class  lr_class


    -- a  is a type of *operation name*.  For example, "+." may be
    -- an operation name - if  a = String.
         
    -- Each operation name corresponds to the *group* of the three 
    -- possible operations of class
    --   (0,r) - prefix  operation of arity r   - say,  -x,
    --   (l,0) - postfix operation of arity l   - say,  n!,
    --   (l,r) - general infix operation of arities l,r -say, x+y.
    -- ij_class = []  
    -- means that the given operation name cannot denote an 
    -- operation of class (i,j).
    -- Example 1.    
    -- ( "+",  ( [(0,1,210,190)], [(1,1,100,100)], [] )  )

    -- decsribes the group "+" which may denote either a prefix 
    -- operation of arity 1,  or a mixed operation of arities 1,1.
    -- Example 2.    
    -- ( ":",  ([], [(1,1,60,50)], [])  )

    -- contained in the standard DoCon table decsribes the  binary
    -- operation symbol which usually denote the *list* 
    -- constructor.  Similar is pair constructor ",".  Thus,

    -- " (1:2-3:nil, a+1) "     would parse to
     
    -- (,  [:  [1]  [: [- [2] [3]] [nil]]  ]
    --     [, [+ [a] [1]] ]
    -- )                  - we omit here the double quotes and ().

    --------------------------------------------------------------
    -- Study  ParOpTab.hs    to get a more definite idea of how to 
    -- set the standard infix operations and how to define the new 
    -- ones.
    --------------------------------------------------------------

------------------------------------------------------------------
type  OpTable a =  [OpGroupDescr a]

           -- This contains all the operations that are processed
           -- by `infix'.


getOp ::  Eq a =>  a -> OpTable a -> [OpGroupDescr a]

                        -- Get operation group from table
                        -- returning  []                if failed,
                        --            [op_group_descr]  otherwise.

getOp x xs =  case  dropWhile ((/= x).fst) xs  of  []    -> []
                                                   (y:_) -> [y]
------------------------------------------------------------------

type  ParenTable a =  [(a,a)]

      -- A *parenthesis* may be any lexeme from  a.
      -- ParenTable  lists all the allowed parentheses pairs.
      -- `parenTable' 
      -- is the standard DoCon parenthesis list:  SEE  ParOpTab.hs


getParen :: Eq a =>  a -> ParenTable a -> [a]

                    -- returns either  []  or
                    --             [ opposite_parenthesis_lexeme ]

getParen  x xs =  case  dropWhile ((/= x).fst) xs  of
                                                  []        -> []
                                                  ((_,y):_) -> [y]






------------------------------------------------------------------
----------------------  Infix Parser  ----------------------------


-- Parsed is a list  xs  of expressions some of which may be 
-- lexemes, say, (L "x1"). 
-- Parenthesis  or an infix  operation sign  should be a lexeme, 
-- say, (L "{"), (L "+").
-- The lexeme expression list can be obtained from the string by 
-- applying the  (lexLots "l")  function.
--
-- The infix parser "sets the parentheses" in  xs  according to 
-- the tables  parenTable, opTable. 
--
-- It returns   (expression_list, message).
--
-- message == ""  when the parse succeeded. 
--                In this case    expression_list == [e].
--
--   Otherwise,  message  is Non-empty,  it tells what is wrong in 
--   the input syntax.
--
-- Examples.
--
-- Let  pT = parenTable;  opT = opTable;  ll = lexLots "L".
--
--  (infixParse pT opT (ll   " x-  ab*20"   ))   -->
--  
--  ( [E  (L "-")  [L "x"]  [E (L "*") [L "ab"] [L "20"]] ],  "" )
--
--  (infixParse pT opT (ll  "0--2" ))   -->  
--       ( [E  (L "-")   [L "0"]  [E (L "-") [] [L "2"]]  ],  "" )
--
--  (infixParse pT opT (ll  "* 2"         ))  -->  
--                                       ([], "wrong arity for *")
--  (infixParse pT opT (ll  "- 2)"        ))  -->  
--                                       ([], "no left ( for )"  )
--  (infixParse pT opT (ll   " (x+1)^2:nil "  ))  -->  
--    (  [E  (L ":")
--           [ E  (L "^")   [E (L "+") [L "x"] [L "1"]]  [L "2"] ]
--           [L "nil"]
--       ],
--       ""
--    )


------------------------------------------------------------------
-- See the file  princip.txt  for the illustration of the method.
-- This real script distincts from what is described in  
-- princip.txt  in that it also treats the parentheses.
--
-- WORNING:  the below program is, probably, very inefficient;
--           it is a subject for optimization.
------------------------------------------------------------------





data  State =  NoArg | WasArg




infixParse ::  (Eq a, Text a) =>  
               ParenTable a -> OpTable a -> [Expression a] ->
               -- pT           oT           xs               
                                          ([Expression a], String)

                                  
infixParse  _      _     []  =  ([], "empty argument")

infixParse  parTab opTab xs  =  scan  NoArg  []  []   xs 
                                           --res stack

  where

  -- First put (left-hand) arguments from  xs  to  res  until the
  -- operation sign appears ...


  scan  _ res stk []         =  clearStack res stk

  scan  s res stk ((L x):xs) =  
         case  
           (getOp x opTab, getParen x parTab)
                                  -- see whether x is an operation
                                  -- or a left parenthesis
         of
           ([]         , []     ) -> 
                                 scan WasArg (res++[(L x)]) stk xs
           ([opGrDescr], _      ) -> 
                    let  (opDescr,new_s) = automaton opGrDescr s
                    in
                      (case  (newStack (L x,opDescr) res stk)  
                       of
                               (stk',"" ) -> scan new_s [] stk' xs
                               (stk',msg) -> (res,msg)
                      )
           (_          , [rPar] ) -> 
                      recurseIntoParenth (L x) (L rPar) res stk xs

  scan  s res stk ( x  : xs) =  scan WasArg (res++[x]) stk xs
                          -- not lexeme, 
                          -- hence not an operation; move x to res


  ----------------------------------------------------------------
  recurseIntoParenth (L lpar) (L rpar) res stk xs =  

         -- x = (L lpar)  was a left parenthesis,   rpar  its 
         -- opposite. 
         -- Find the closing rpar for x in xs, convert recursively
         -- the list between lpar and rpar to expression  e  and
         -- move  e  to res.                     

    (case   opposite [] xs 1   of

      (xs1, []    ) -> 
               ( [],  "no closing parenthesis for "++(show lpar) )
      (xs1, rp:xs2) -> 
         (case  scan NoArg [] [] xs1  of
           ([e],"" ) -> scan WasArg (res++[e]) stk xs2
           (es ,msg) -> 
            ( es, "bad syntax inside "++(show lpar)++(show rpar) )

         )
    )
      where
      opposite xs1 []      _       =  (reverse xs1, [] )
      opposite xs1 (x:xs2) balance = 
                 case  ( balance, x==(L lpar), x==(L rpar) )  
                 of
                   (b, False, False) -> opposite (x:xs1) xs2 b
                   (b, True , _    ) -> opposite (x:xs1) xs2 (b+1)
                   (1, _    , True ) -> (reverse xs1, x:xs2)
                   (b, _    , True ) -> opposite (x:xs1) xs2 (b-1)
  ----------------------------------------------------------------


                -- the following defines the  operation class  and
                -- the  new state  according to the operation 
                -- tripple description  and the  current state.

  automaton  (op,tripple) s =  case  (tripple,s)  of 

                   ( ([]  , _   , [d3] ), _      ) -> (d3, WasArg)
                   ( ([_] , _   , [d3] ), WasArg ) -> (d3, WasArg)
                   ( ([]  , [d2], []   ), _      ) -> (d2, NoArg )
                   ( ([_] , [d2], []   ), WasArg ) -> (d2, NoArg )
                   ( ([d1], _   , _    ), _      ) -> (d1, NoArg )


     -- Each operation in the stack is kept as a *bag*,  a psewdo-
     -- expression  ((opName,lA,rA,rP), arg)
     --     - opName (a lexeme),  arities,  right-hand precedence,
     --     argument list.
     -- The operation names are the lexemes. Pushing to stack does
     -- not change them,  poping from stack appends the expression 
     -- constructor E.   Thus  res  is always a list of  the  true
     -- expressions - which turns to  []  or to a singleton in the 
     -- end.

  newStack  (name,(lA,rA,lP,rP)) res []        = 
                                   ( [((name,lA,rA,rP),res)], "" )

  newStack  op                   res (op1:stk) =

         -- If the left-hand precedence of new operation  op  is 
         -- greater than the right-hand precedence of the stack 
         -- top operation bag (op1 ..),  then  op  takes all  res
         -- in its bag and pushes into  stack.
         -- Otherwise,  op1  pops out to  res  with the new 
         -- (expression) bag in whichs  lA1  of the left-hand 
         -- arguments are taken from the initial  preArg  from 
         -- the bag, and  rA1  of the right-hand one are taken
         -- from  res.
    let
      (name, (lA,rA,lP,rP))         = op
      ((name1,lA1,rA1,rP1), preArg) = op1
    in
      if  lP > rP1  then  ( ((name,lA,rA,rP),res):op1:stk, "" )
      else    
        case  popToRes name1 lA1 rA1 preArg res  
        of
          (res',"" ) -> newStack  op res' stk
          (res',msg) -> (stk,msg)



  popToRes  op lA rA preArg res =  
    case 
      (rA > (genericLength res), lA > (genericLength preArg))
    of
      (True , _    ) -> 
           ( res, (show op)++"  needs more right-hand arguments" )
      (_    , True ) ->
           ( res, (show op)++"  needs more left-hand arguments"  )
      (_    , _    ) -> let (argR,res'   ) = splitAt rA res
                            (argL,preArg') = splitAt lA preArg
                        in   
                            (preArg'++((E op argL argR):res'), "")


  clearStack  res stk =  

    (case  clr res stk  of
             ([e],"") -> ([e], "")
             (es ,"") -> (es, "more than one expression obtained")
             es_msg   -> es_msg
    )
      where  clr res []                          =  (res,"")
             clr res (((op,lA,rA,_),preArg):stk) =  
                                case  popToRes op lA rA preArg res
                                of
                                  (res',"" ) -> clr res' stk
                                  (res',msg) -> (res',msg)
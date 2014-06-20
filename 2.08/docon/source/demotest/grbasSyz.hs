    -- testing  polARels  - algebraic relations for polynomials
    --
    -- Converting the Abyankhar curve equation from the parametric
    -- form.

    xVars = ["t"]                                  
    yVars = ["z","y","x"]
    oX    = lexPPO 1
    oY    = (("degLex",3),degLex,[])
    unPx  = cToPol oX xVars dR unR  :: P       -- 1 of R[t]

                                               -- parameterization
    fs = map (smParse unPx) [ " t^4 "    ,     --  = z 
                              " t^3 "    ,     --    y
                              " t + t^5 "      --    x                       
                            ]
    hs   = []  :: [P]
    rels = algRelsPols hs yVars oY fs

    hsCol   = transp (Mt [hs  ] eFM)
    fsCol   = transp (Mt [fs  ] eFM)
    relsCol = transp (Mt [rels] eFM)


              {- here  rels  is the Groebner basis of the equation
                 ideal for the above curve:
                            [ z^2     - x*y     + z          ,
                              y^3*x   + z*y^2   - z*x^2 + y^2,
                              y^4     - x*y*z   + x*y   - z  ,
                              z*y^2*x + 2*y^2*x - x^3   + z*y + y,
                              z*y^3   + y^3     - y*x^2 + z*x
                            ]
              -}
    -- print  hsCol, fsCol, relsCol 


------------------------------------------------------------------
    -- Groebner bases in  K(u)[x,y]  and  in  K[x,y],
    --
    -- K = Fraction Z

    vars  = ["x","y"]
    vars1 = ["kb","kf"]
    ord   = lexPPO 2
                            -- Px = K[x,y]
                            -- Pk = K[kb,kf]
    type F  = Fraction P    -- F  = K(kb,kf) = Fraction Pk
    type P1 = Pol F         -- P1 = F[x,y],  lexComp, x > y

    unPx = unP                      :: P   
    unPk = cToPol ord vars1 dR unR  :: P   
    unF  = unPk:/unPk
    dF   = upField unF eFM
    unP1 = cToPol ord vars dF unF   :: P1   

    fs@[f1,f2,f3] = map (smParse unP1) 
                      [ " x^2   - x*y        -  kb ",
                        " y^2   + (1-kf)*y   -  kf ",
                        " x^2*y + (2-kb)*x*y + (1-kb)*x - kb*y "
                      ] 
    (gs,mt) = gxBasis fs   -- G-basis in  P1,
                           -- it yields  [y+1, x^2 + x - kb]  

    -- We see, there are two solutions for the system  gs  for the
    -- general position  
    --                  (of kb ?).

    The second polynomial  s2   is proportional to  y+1  over  F,   
    ??
    thus there are 2 solutions in the general position.    Note 
    also that the number of solutions over Q may rise when  kb=kf+1 
    for, 
       ??   as we see, lc(s2)  turns to zero on this line.  ??
     
    {- For example,    y + 1 =  (1/d) * (a1*g1 + a2*g2 + a3*g3),

       d  =  kb*(kb - kf - 1) ,
       a1 =  x*y + (1-kb)*y  - kb + kf + 1
       a2 =  x^2 + (1-kb)*x
       a3 =  -x  + kf
    -}
    -- Putting   kb = 6,   kf = 5   we find another Groebner basis 
    -- in  Px = K[x,y]    for polynomials   fs',  
    -- fi' = fi(x,y,6,5).

    fs' =  map (smParse unPx) [ " x^2   - x*y   - 6 ",
                                " y^2   - 4*y   - 5 ",
                                " x^2*y - 4*x*y - 5*x - 6*y "
                              ] 

    (gs',_) =  gxBasis fs'    -- = [y^2 - 4*y - 5,  x^2 - x*y - 6]

    -- And  gs'  is not a specialization of  gs. 
    -- Note that  d(6,5) = 0.

    fColumn  = transp (Mt [fs]  eFM) :: Matrix P1
    gColumn  = transp (Mt [gs ] eFM) 
    g'Column = transp (Mt [gs'] eFM) :: Matrix P

    -- Thus the Groebner basis over the rational functions 
    -- had automatically found a line  kb = kf+1  on which 
    -- the  2-parametric system  BAS  in  Q[x,y]   has   4 
    -- solutions instead of  2 ones for the General position. 










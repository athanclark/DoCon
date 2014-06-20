------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- GCD of polynomials  



module  PolGCD( polGCD, cont, liftPolCoef, polPseudoRem )   where

import Categ
import Categ1
import PP
import Pol
import Matrix  --?
import IParse  --?





------------------------------------------------------------------
-- content  of polynomial over the factorial coefficient domain --

cont ::  SyzygySolvableRing a =>  Pol a      -> a 
cont                              (Pol mons) =  gcD (map fst mons)



----------  R[x1,x2,...,xn] -> R[x1][x2,...,xn]  -----------------

liftPolCoef ::  CommutativeRing a =>  Pol a -> Pol (Pol a)

liftPolCoef (Pol []  )   = Pol []
liftPolCoef f@(Pol mons) = 
                   let  cmp = ppCp (lpp f)  
                   in   Pol  (map (lift cmp) (partByPPTails mons))
  where
                -- Convert  mons  into groups (ksi,msi), monomials
                -- with the same  tail(pp) = ksi  go to one group. 
                -- The order inside  msi  is the same as it was in
                -- in  mons.
                -- Each msi  is a list of pairs  (c,ks1),  ks1  is 
                -- the power product restricted to x1.

  partByPPTails mons = partT (map breakPP mons)
    where
    breakPP (c,pp) =  case  ppP pp  of  []     -> (c,[] ,[])
                                        (k:ks) -> (c,[k],ks)

    partT [(c,ks1,ks)]      = [ (ks, [(c,ks1)]) ]
    partT ((c,ks1,ks):mons) = (ks, (c,ks1):(pt mons)):(partT mons)
      where
      pt []                = []
      pt [(_,[],  [] )]    = []
      pt ((c,ks1',ks'):ms) = if  ks'==ks  then  (c,ks1'):(pt ms)
                             else               pt ms

                 -- convert mons_i group into monomial over  a[x1]

  lift cmp ([], [(c,[0])]) = ( Pol [(c, PP [] cmp)], PP [] cmp )
  lift cmp (ks, ms       ) = ( Pol (map lft ms)    , PP ks cmp )
                               where
                               lft (c,[0]) = (c, PP []  cmp)
                               lft (c,ks1) = (c, PP ks1 cmp)
------------------------------------------------------------------



deg f = case  ppP (lpp f)  of                    -- this is LOCAL
                   []  -> 0
                   [n] -> n
                   _   -> error "polPseudoRem: many variables \n"





----------------  Pseudodivision in  R[x]  -----------------------

-- See D.Knuth "The art of programming".

-- For non-zero  f,g,  there exist  k,q,r  such that 
--                   (lc(g)^k)*f = q*g + r, 
-- k <= deg(f)-deg(g)+1, 
-- and either  r = 0  or  deg r < deg g.

-- polPseudoRem  returns only  r. 

-- polPseudoRem  is so far used only in  polGCD algorithm (below).
-- It does not use the coefficient division,  and it should be 
-- faster than   polDivRem (lc(g)^(n-m+1)*f) g


polPseudoRem ::  (Num a, CommutativeRing a) => 
                                           Pol a -> Pol a -> Pol a

polPseudoRem _        (Pol [])     = 
                            error "(polPseudoRem _ (Pol [])) \n\n"
polPseudoRem (Pol []) g            = Pol []
polPseudoRem f        g@(Pol mons) = 
  let  
    b     = lc g
    m     = deg g
    cmp   = ppCp (lpp g)
    gTail = Pol (tail mons)

    rem (Pol [])           = Pol []
    rem f@(Pol (mon:mons)) = let  n = deg f  in

             if  n < m  then  f
             else
               let  p    = if  n==m  then []  else [n-m]
                    mon' = (lc f, PP p cmp)
               in
                 rem ((cPolMul b (Pol mons))-(mPolMul mon' gTail))
  in    
    rem f   

               




-------------------  GCD of polynomials  -------------------------




polGCD :: (SyzygySolvableRing a, Num a) =>  
                                 String -> Pol a -> Pol a -> Pol a
                                 --mode

                   -- a  is a factorial ring with the GCD function
polGCD mode f g =  

  (case  mode  of
          "field" -> gc True  f g
          ""      -> gc False f g
          _       ->  
            error( "(polGCD mode f g):  mode =  \"field\" | \"\" "
                   ++ "\nHere f = " ++ (w f "")
                 )
  )                       
  where
  gc _   (Pol [])      g             = g
  gc _   f             (Pol [])      = f 
  gc fld f@(Pol monsF) g@(Pol monsG) = 
                 let  un = unity (lc f)  in   gc' (zero un) un f g
    where

    gc' zr un f g = 
      (case  (numOfVars f, numOfVars g)  of
        
        (0,_) -> cfToPol (gcD ((lc f):(map fst monsG)))
        (_,0) -> cfToPol (gcD ((lc g):(map fst monsF)))
        (1,1) -> gcd1 fld f g
        (1,_) -> gcd1 fld f (cont (liftPolCoef g))
        (_,1) -> gcd1 fld (cont (liftPolCoef f)) g
        _     ->
          error("polGCD: so far I can handle only the case when"++
                "one of f,g depends on the first variable only"
               )
      )
        where
        gcd1 True  f       g        = gcdField  f g
        gcd1 False f       (Pol []) = divByCoef f (cont f)
        gcd1 False (Pol []) g       = divByCoef g (cont g)
        gcd1 False f        g       =     
          case                             -- reduce to primitives
            (deg f, deg g, lc f)     
          of        
              (0,_,a) -> cfToPol (gcD [a   , cont g]) 
              (_,0,_) -> cfToPol (gcD [lc g, cont f]) 
              (_,_,a) -> 
                    let  ctf   = cont f
                         ctg   = cont g
                         cfGcd = gcD [ctf,ctg]
                         fPrim = divByCoef f ctf 
                         gPrim = divByCoef g ctg
                    in   cPolMul cfGcd (gcdPrimitives fPrim gPrim)

        gcdField  f (Pol []) = cnAs f
        gcdField  f g        =  
            if  (deg g)==0  then  unityPol
            else                  gcdField g (snd (polDivRem f g))


                   -- Here  f,g  are primitive and non-constant.
                   -- See D.Knuth "The art of programming".        
                   -- ********************************************
                   -- The following method is not fast at everage. 
                   -- But it is simple.
                   -- ********************************************
                   -- We will try soon the homomorphic images.


        gcdPrimitives f g = (if  (deg f)<(deg g)  then  p g f
                             else                       p f g   
                            )
          where                  -- in this loop  deg f >= deg g
          p f g =      
            case  polPseudoRem f g
            of
              (Pol []) -> divByCoef g (cont g)  
              rem      ->                    
                if  (deg rem)==0  then  unityPol
                else                p g (divByCoef rem (cont rem))
    

        ppCmp     = ppCp (lpp f)
        cfToPol c = cToPol zr ppCmp c
        unityPol  = cfToPol un

        divByCoef f c = 
          if  c==un  then  f
          else
            case  polCoefDiv f c  of  
                    []  -> error( "DoCon error:  polGCD.." ++
                                  "divByCoef:  does not divide \n"
                                )
                    [q] -> q

        cnAs (Pol []) = Pol [] 
        cnAs f        = let  a = lc f
                        in   if a==un then  f  else  divByCoef f a


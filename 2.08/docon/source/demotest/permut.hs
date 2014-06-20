------------------------------------------------------------------
------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2
--
--  Copyright  Serge Mechveliani
------------------------------------------------------------------
------------------------------------------------------------------




-- Tests, benchmarks, demonstration.

-- This is an attempt to find a small subgroup G in S(n) for which
-- the set  coms = {x*y*(inv x)*(inv y) | x<-G, y<-G}  is not 
-- closed under (*).
-- The attempt failed so far:
-- * Each even permutation in S(n) occured in  coms  - for at least
--   n < 8
-- * among the subgroups  S<v, g*w*inv(g)>,   g from S(7),   
--   we could not find so far the needed one:  see the below 
--   program.



import List     (nub, nubBy, (\\))
import DPrelude (Z, sort         ) 
import SetGroup
import Permut



goodSubgroups :: 
           Z -> Permutation -> Permutation -> [(Bool,Z,Permutation)]

  -- bound -> v -> w -> [(boo1,l1,p1), (boo2,l2,p2), ...].
  -- 
  -- Given the permutations  v,w  from S(n),  forms certain 
  -- non-trivial and not too large subgroups of kind  S<v,p>,  
  -- where  p = g*w*inv(g)  are certain chosen congugated to  w
  -- elements.
  -- For each  i
  -- if  boo(i)=True,  then  l(i) = |S<u,p(i)>| < bound
  -- else
  --   l(i) = |xs| >= bound  for the reached (unclosed) subset xs.


goodSubgroups bound v w =  
  let
    n      = length (permutRepr v)
    sS     = allPermuts [1..n]
    wOrbit = w: (filter (/=w) [g*w*(inv g) | g<- sS])
    wpO    = 
            map (\p->(p,cycleSets p)) (filter (\p->v*p/=p*v) wOrbit)
      --
      -- CongugacyOrbit(w)  with  centralizator(v)  removed;
      -- and each  p  is removed who has the same orbit sets in 
      -- [1..n] as some earlier one (do we need it?).
      --
    wO          = nubBy (\ (_,s) (_,s')-> s==s') wpO
    cycleSets p = sort$ map sort$ permutCycles p
        --
        -- finds the the cycle decomposition, converts each cycle
        -- into its subset in {1..n} repesented by the ordered list;
        -- sorts these lists lexicographically
  in
  sgs$ map fst wO
    where
    sgs []     = []
    sgs (p:ps) = case  gensToSemigroupList b [v,p]  
                 of
                   (xs,0) -> (False, length xs, p):(sgs ps)
                   (_ ,l) -> (True , toInt l  , p):(sgs ps)
    b = toInteger bound





------------------------------------------------------------------
main =  
  let  
    n  = 7 :: Z
    js = [1..n] 
    u  = Pm js
    sS = allPermuts js
    sA = filter isEvenPermut sS
     {-
    arithTest =  
           and [ x*(inv x)==u && (inv x)*x==u && (x*y)*x== x*(y*x)
                 | x <- sS, y <- sS
               ]
    testCycles =
      all (\p-> p == (foldl (+) (Pm [])$ map Pm$ permutCycles p)) sS
    ----------------------------------------------------------------
    evenReprss = filter isEvenPermut reprss
    ccs        = nubBy (\ (_,c) (_,d)->c==d)
                     [((x,y), x*y*(inv x)*(inv y)) | x<-sS, y<-sS]

    solveComm e =  case  dropWhile ((/=e).snd) ccs  of
                                                 (pr,_):_ -> Just pr
                                                 _        -> Nothing
    solutions = [(e,solveComm e) | e <- evenReprss]
      -}


    subgrTest xs =  all (`elem` xs) [x*y| x<-xs, y<-xs]  &&
                    all (`elem` xs) (map inv xs)

    showsRows []     = id
    showsRows (x:xs) = (shows x).('\n':).(showsRows xs)
    --------------------------------------------------------------
    bound = 300
    v     = Pm ...  `asTypeOf` u  
    w     = Pm ... 

    (gG,_) = gensToSemigroupList bound [v,w]

    coms     = nub [x*y*(inv x)*(inv y) | x<-gG, y<-gG]
    products = nub [x*y | x<-coms, y<-coms]
    notCom   = case  products \\ coms  of  x:_ -> Just x
                                           _   -> Nothing
  in
  putStr (shows notCom "\n")

;






{- Results -------------------------------------------------------


v = Pm [2,3,4,1, 6,7,5]   

  w = v   -> [ ( 72, [2,4,1,3,6,7,5], [[2,4,1,3],[6,7,5]] ) ]
                                            commutators are closed

      Pm [2,3,1, 5,6,4, 7]  
      ->
      [ ( 72, [2,3,1,4,6,7,5], [[6,7,5],[2,3,1],[4]] )      closed
                                 ----- too close to v
        ( 72, [2,4,3,1,6,7,5], [[6,7,5],[2,4,1],[3]] )
        ( 72, [3,2,4,1,6,7,5], [[6,7,5],[3,4,1],[2]] )
        ( 72, [1,3,4,2,6,7,5], [[6,7,5],[3,4,2],[1]] )
      ]

      Pm [2,3,4,5,6,1, 7]  -> []
      Pm [2,3,4,5,1, 7,6]  -> []

      Pm [2,3,4,1, 6,5, 7] 
      ->
      [ ( 24, [2,3,4,1,6,5,7], [[2,3,4,1],[6,5],[7]] )
                                -------- too close to v
        ( 24, [2,3,4,1,7,6,5], [[2,3,4,1],[7,5],[6]] )
        ( 24, [2,3,4,1,5,7,6], [[2,3,4,1],[7,6],[5]] )
      ]

  
      Pm [2,3,1, 5,4, 7,6] 
      ->
      [ ( 24, [2,1,4,3,6,7,5], [[6,7,5],[4,3],[2,1]] )
                                 -----
        ( 24, [4,3,2,1,6,7,5], [[6,7,5],[3,2],[4,1]] )
      ]
      

      Pm [2,1, 4,3, 6,5, 7]
      ->
      [ ( 24,[2,1,4,3,6,5,7], [[6,5],[4,3],[2,1],[7]] )  closed
        ( 24,[2,1,4,3,7,6,5], [[7,5],[4,3],[2,1],[6]] )
        ( 24,[2,1,4,3,5,7,6], [[7,6],[4,3],[2,1],[5]] )
        ( 24,[3,4,1,2,6,5,7], [[6,5],[4,2],[3,1],[7]] )
        ( 24,[3,4,1,2,7,6,5], [[7,5],[4,2],[3,1],[6]] )
        ( 24,[3,4,1,2,5,7,6], [[7,6],[4,2],[3,1],[5]] )
        ( 24,[4,3,2,1,6,5,7], [[6,5],[3,2],[4,1],[7]] )
        ( 24,[4,3,2,1,7,6,5], [[7,5],[3,2],[4,1],[6]] )
        ( 24,[4,3,2,1,5,7,6], [[7,6],[3,2],[4,1],[5]] )
      ]







------------------------------------------------------------------
conjRepress :: Int -> [Permutation Int]
                       -- Conjugacy class representatives for S(n)
conjRepress 7 =       
            [r1,r2,r3,r4,r5, r6,r7,r8,r9,r10, r11,r12,r13,r14,r15]

r1  = Pm [2,3,4,5,6,7,1]         -- 7 = 7+0   
r2  = Pm [2,3,4,5,6,1, 7]        --     6+1   
r3  = Pm [2,3,4,5,1, 7,6]        --     5+2   
r4  = Pm [2,3,4,5,1, 6, 7]       --     5+1+1 
r5  = Pm [2,3,4,1, 6,7,5]        --     4+3   
r6  = Pm [2,3,4,1, 6,5, 7]       --     4+2+1 
r7  = Pm [2,3,4,1, 5, 6, 7]      --     4+1+1+1       
r8  = Pm [2,3,1, 5,6,4, 7]       --     3+3+1
r9  = Pm [2,3,1, 5,4, 7,6]       --     3+2+2         
r10 = Pm [2,3,1, 5,4, 6, 7]      --     3+2+1+1       
r11 = Pm [2,3,1, 4, 5, 6, 7]     --     3+1+1+1+1     
r12 = Pm [2,1, 4,3, 6,5, 7]      --     2+2+2+1
r13 = Pm [2,1, 4,3, 5, 6, 7]     --     2+2+1+1+1     
r14 = Pm [2,1, 3, 4, 5, 6, 7]    --     2+1+1+1+1+1    
r15 = Pm [1, 2, 3, 4, 5, 6, 7]   --     1+1+1+1+1+1+1  


Answer:  each even thing is commutator.

((Pm [2,3,4,5,6,7,1]),Just ((Pm [1,2,3,5,6,7,4]),(Pm [4,5,6,1,7,3,2])))
((Pm [2,3,4,5,1,6,7]),Just ((Pm [1,2,4,5,3,6,7]),(Pm [3,4,1,5,2,6,7])))
((Pm [2,3,4,1,6,5,7]),Just ((Pm [1,2,4,3,6,7,5]),(Pm [3,5,6,7,1,4,2])))
((Pm [2,3,1,5,6,4,7]),Just ((Pm [1,2,3,5,6,4,7]),(Pm [4,5,6,1,3,2,7])))

((Pm [2,3,1,5,4,7,6]),Just ((Pm [1,2,4,5,6,7,3]),(Pm [4,6,1,3,5,7,2])))
((Pm [2,3,1,4,5,6,7]),Just ((Pm [1,3,2,4,5,6,7]),(Pm [2,1,3,4,5,6,7])))
((Pm [2,1,4,3,5,6,7]),Just ((Pm [1,2,4,3,5,6,7]),(Pm [3,4,1,2,5,6,7])))
((Pm [1,2,3,4,5,6,7]),Just ((Pm [1,2,3,4,5,6,7]),(Pm [1,2,3,4,5,6,7])))
-}









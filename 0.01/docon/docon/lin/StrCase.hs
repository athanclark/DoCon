------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------




-- The  staircase form  and the  inversion  of matrix.




module  StrCase 
  ( 
    toStairMatr, matrInv,  test_matrInv, test_toStairMatr, 
    mulSign, invSign
                                                    , strCase
  )  
where

import  PreludeList
import  PreludeChar
import  Categ
import  Categ1
import  Matrix
import  IParse --?




mulSign ::  Char -> Char -> Char 
mulSign     x       y    =  if  x==y  then '+'  else '-'

invSign ::  Char -> Char 
invSign     '+'  =  '-'
invSign     '-'  =  '+'





------------------------------------------------------------------
-- This is the simplified version supplied as the *commentaries*.
 
-- Study first this script.
-- The full version is   * toStairMatr *   - see it below.



strCase ::  SyzygySolvableRing a =>  Matrix a -> Matrix a
                                  -- m           s


    -- StairCase Form  of matrix  m.

    -- *** Only for the  Euclidean ring  a  - so far  ***

    -- Method:
    -- Gauss reduction applied to the Rows of m. Though  a  may be
    -- not a field,  we repeat the  remainder division  to  obtain 
    -- zeroes down in the column. 


strCase  m  =
  let
    (Mt rows) = m
    zr        = zero (head (head rows))       
  in
    (case  matrElem (/= zr) m  of
      []  ->  m                                       -- m is zero
      [x] ->  let  un = unity x  in   Mt (scm zr un rows)
    )
    where    -- Main loop.   m  is non-empty and non-zero.
             -- Below we operate mostly with the Row Lists.
             -- Clear the first column, store row1,  cut row1 and 
             -- the first column; apply recursively  scm;  restore
             -- first zeroes and prepend row1.

    scm  zr un m =  sc  m
      where
      sc  [row] =  [row]
      sc  m     =
        let  m'   =  clearColumn m
             row1 =  head m'
        in
          if  (head row1)==zr  then       -- first column is zero

                if  (matrWidth (Mt m'))==1  then  m'
                else
                   let  s' = sc  (map tail m')  in   map (zr :) s'
          else
                            -- here  m'(1,1) == gcd(column)/=zero,
                            -- m'(i,1)==zero  for i>1
            let 
                s'' =  sc  (map tail (tail m'))
            in
                row1:(map (zr :) s'') 


          -- clearColumn  m  ->  m'  
          -- From the start,  length(m) > 1.
          -- m'(1,1) = gcd(firstColumn(m)), m'(i,1)==zr  for i>1.
          -- m'(1,1)==zr  means the column was zero.

      clearColumn  m =  
                  case  partition  (\row -> (head row)/=zr) m  of

        ([]  , rest) ->  rest              -- zero column
        ([r] , rest) ->  r:rest            -- single non-zero
        (maxs, rest) ->  c  maxs rest    -- maxs are the rows with
                                         -- the non-zero head. 

          -- Each  ai = maxs(i,1)  is non-zero,  
          -- The subcolumn (a1,a2) reduces to the form (b,zero) by
          -- the Euclidean algorithm,  and the transformation  
          -- matrix  t2  2x2  is acumulated.  Then  t2  applies to 
          -- tail(maxs(1)), tail(maxs(2)),  and  maxs(2)  moves to
          -- rest.  This continues while  length(maxs) > 1.

      c  [r]          rest =  r:rest
      c  (r1:r2:maxs) rest =
        let
          (a1,a2,t2) = 
                  reducePair (head r1) (head r2) [[un,zr],[zr,un]]
                                                        -- a2==zr
          (Mt [r1Tl,r2Tl] ) = 
                            matrMul (Mt t2) (Mt [tail r1,tail r2])
        in
          c  ((a1:r1Tl):maxs) ((a2:r2Tl):rest)



         -- reducePair a b [row1,row2]  ->  (a',b',[row1',row2'])  

         -- a,b  are divided repeatedly with  remainder,  like  in 
         -- extended gcd method.  [row1,row2] is a protocol matrix 
         -- 2 x 2  initiated with the unity matrix.

      reducePair  a b [row1,row2] =
        let  
          [q,r] = divRem "" b a
          row2' = if  q==zr  then  row2  
                  else             row2-(map (mul q) row1)
        in
          if  r==zr  then  ( a, r, [row1,row2'] )
          else             reducePair  r a [row2',row1]
------------------------------------------------------------------







toStairMatr ::  
     SyzygySolvableRing a => 
     String -> Matrix a -> Matrix a ->  (Matrix a, Matrix a, Char)
  -- mode      m           t0            s         t         sign



  -- *** See first  strCase  script. ***

  -- The transformations are applied parallelly to the matrix  t.

  -- t  is the Transformation matrix.
  --    If  t0 = unityMatrix  of size matrHeight(m) then 
  --                m x t = s, 
  --                             where  t  is the protocol matrix
  --                             for the Gauss reductions of  m,
  --    generally:  m  x u = s   for the protocol matrix  u,  and
  --                t0 x u = t,  t0 is any initial square matrix.

  --    t0 = Mt []   is a synonym for the  Unity matrix  of 
  --                 appropriate size.

  --    If m is zero and t0= Mt [],  then  (m,Mt [])  is returned.

  -- mode == "" | "u"
  --  
  --   "u"  means that m is *already staircase*,  and the function 
  --   should try to reduce to zero the elements  *up the main 
  --   diagonal*.
  --   In this case   (s1,t)  are returned where
  --                   s1  has reduced (*as possible*) upper part.
  --                   s1  is  * diagonal if  m  is invertible *. 

  -- sign == '+' | '-'
  --      is the accumulated *signum* of the row transpositions.
  --      It is true that  ( det(m)==det(s) or det(m)== -det(s) ).
  --      sign  shows what of these alternatives take place.

  --      Thus the `det' function uses this "signum" interface.

  --      For the  "u"  mode,  sign  is always  '+'.




toStairMatr  mode m t =

  (case  matrElem (const True) m   of

    []  ->  error "toStairMatr:  empty matrix"
    [x] ->  
      let  zr = zero x
      in
        (case  matrElem (/= zr) m   of
          []  ->  (m,t,'+')
          [y] ->  
            let  un         =  unity y
                 (Mt rowsM) =  m
                 t0         =  
                          if t==(Mt []) then  scalMatr rowsM un zr
                          else                t
                 (Mt rowsT) =  t0
                 hm         =  matrHeight m  
                 ht         =  matrHeight t0  
                 wt         =  matrWidth  t0  
            in
              (case  (hm, hm==ht, ht==wt, (mode==""||mode=="u"))  
               of
                (1, True , True,  _    ) ->  (m,t,'+')
                (_, False, _   ,  _    ) ->
                      error "toStairMatr:  height(m) /= height(t)"
                (_, _    , False, _    ) ->
                   error( "toStairMatr:  the initial " ++
                          "transformation matrix should be Square"
                        )
                (_, _    , _    , False) ->
                      error "toStairMatr:  mode == \"\" | \"u\"  "
                _                        ->
                  if  (euclidean un)/=Yes  then  
                           error( "toStaircMatr:  only Euclidean " 
                                  ++ " domain can handle so far "
                                )
                  else
                    (case  mode  of
                      ""  -> let  (rs,rst,sg) =
                                        scm  zr un '+' rowsM rowsT
                             in   (Mt rs, Mt rst, sg)

                      "u" -> let (rs,rst)= redUpper zr rowsM rowsT
                             in
                                 (Mt rs, Mt rst, '+')
                    )
              ) --case (hm..
        ) --case matrElem
  )
    where
                          -- scm  zr un  m t  ->  m1 t1
                          -- Here  m  is non-empty and non-zero, 
                          -- t  may be NOT square (!)

    scm  zr un sg rows rowsT =  sc  sg rows rowsT
      where
      sc  sg [row] [rowT] =  ([row], [rowT], sg)
      sc  sg m     t      =
        let  
          (m', t', sg') =  clearColumn sg m t
          (r , rt)      =  (head m', head t')
        in
          if  (head r)==zr  then         -- first column is zero

            if  (matrWidth (Mt m'))==1  then  (m',t',sg')
            else
                     let  (s'',t'',sg'') = sc sg' (map tail m') t'
                     in                        
                          ( map (zr :) s'',  t'',  sg'' )
          else
            let  (s'',t'',sg'') =  
                           sc  sg' (map tail (tail m')) (tail t')
            in
                 ( r:(map (zr :) s''),  rt:t'', sg'' )             




      -- clearColumn  sg m t  ->  (m',t',sg')

      clearColumn  sg m t =  
        case  
          part  ( \(row,_)-> (head row)/=zr )  (zip m t)
                                  -- yeilds partition 
                                  -- and the transposition signum
        of
          ([]      , restPairs, sg') -> 
                                   let  (m',t') = unzip restPairs
                                   in
                                        (m', t', mulSign sg sg')
          ([(r,rt)], restPairs, sg') ->  
                                   let  (m',t') = unzip restPairs  
                                   in  
                                     (r:m', rt:t', mulSign sg sg')
          (maxPairs, restPairs, sg') ->
                                let  (maxs,  tm) = unzip maxPairs
                                     (smalls,ts) = unzip restPairs
                                in
                                     c  sg' maxs smalls tm ts


    
                   -- The below `c' differs from one from strCase
                   -- in that  t2  applies also to the rest of  t  
                   -- and in that `c' also processes the sign.

      c  sg [r]          smalls  [rt]         ts = 
                                             (r:smalls, rt:ts, sg)
      c  sg (r1:r2:maxs) smalls  (rt1:rt2:tm) ts =
        let
          (a1,a2,t2,sg') =  
              reducePair '+' (head r1) (head r2) [[un,zr],[zr,un]]
          (Mt [r1Tl,r2Tl])= matrMul (Mt t2) (Mt [tail r1,tail r2])
          (Mt [rt1',rt2'])= matrMul (Mt t2) (Mt [rt1,rt2])
        in
          c  (mulSign sg sg') ((a1:r1Tl):maxs) ((a2:r2Tl):smalls)
                              (rt1'     :tm  ) (rt2'     :ts    )

  

             -- reducePair '+' a b [row1,row2] -> 
             --                        (a',b',[row1',row2'],sign)

      reducePair  sg a b [row1,row2] =
        let  
          [q,r] =  divRem "" b a
          row2' =  if  q==zr  then  row2  
                   else             row2-(map (mul q) row1)
        in
          if  r==zr  then  ( a, r, [row1,row2'], sg )
          else            reducePair (invSign sg) r a [row2',row1]


                      -- part  p xs -> (xs1,xs2,sign)
                      -- xs1,xs2 are like in standard `partition',
                      -- sign  is the transposition signum.
      part  p xs =  
        let                         -- par also forms the evenness
                                    --     flag for  length(xs1)
          par []     =  ( [], [], '+', '+' )
          par (x:xs) = 
            let  (xs1,xs2,sg,evn) = par xs
            in
              if  p x  then
                       (x:xs1, xs2  , sg            , invSign evn)
              else     (xs1  , x:xs2, mulSign sg evn, evn        ) 
                                         -- x jumped over xs1 ...
         
          (xs1,xs2,sg,_) =  par xs
        in
          (xs1,xs2,sg)






redUpper ::  SyzygySolvableRing a =>  
                           a -> [[a]] -> [[a]] -> ( [[a]], [[a]] )
                        -- zr   s        t          s1    t1

          -- See comments on  toStairMatr  on the case  mode=="u".
          -- Here  s  is already staircase.

redUpper  zr [r] [rt] =  ( [r], [rt] )
redUpper  zr s   t    =
  let
    (nzPairs,zPairs) =  break  ((all (== zr)).fst)  (zip s t)
                                             -- separate zero rows
    (zS,t') = unzip  zPairs
    (s1,t1) = unzip  (reverse (ru (reverse nzPairs)))
                                              -- case no zero rows
  in 
    (s1++zS, t1++t')
      where
          -- Here  m,t  are reversed and their rows are paired.
          -- Find first non-zero  b  in the first column; 
          -- replace the "downs" bi in this column with  bi mod b
          -- (the rows of  m  and  t  act "parallel");
          -- cut first column;  recurse  ru ;  prepend column.

      ru  [r_rt] =  [r_rt]
      ru  s_t    =
        let
          wd       =  genericLength (fst (head s_t))
          (stZ,st) =  span (\(r,_)->(head r)==zr) s_t
                              -- st column starts with 
                              -- the first non-zero - if non-empty
          st'   =  reduceColumn st
          stNew =  stZ++st'
        in
          if  wd==1  then  stNew
          else 
            let  stNewTl =  map (\(r,rt)-> (tail r,rt)) stNew
                 heads   =  map (\(r,_ )-> head r     ) stNew
                 st''    =  ru  stNewTl
            in 
                 zipWith (\x (r,rt) -> (x:r,rt)) heads st''
          where
          reduceColumn  []          = []    -- the column was zero
          reduceColumn  ((r,rt):rr) = 
            let  b = head r  
            in                                   -- here  b /= zr
              (r,rt) : (map (red b (r,rt)) rr)
                where
                red  b (row,rowT) (x:row1,rowT1) =
                  let 
                    [q,rem] = divRem "" x b
                  in
                    if  q==zr  then  (x:row1,rowT1)
                    else          ( (x:row1) - (map (mul q) row ),
                                    rowT1    - (map (mul q) rowT)
                                  )

------------------------------------------------------------------




matrInv :: SyzygySolvableRing a =>  String -> Matrix a -> Matrix a
                                 -- mode      m           im

         
     -- Inversion  of matrix  m  (of size N x N).

     -- If  m  is invertible, the inverse matrix  im  is returned,
     -- otherwise             Mt []                   is returned.

     -- mode =  "" | "s"      
     --                "s"  means m is  *staircase*.  In this case
     --                the computation is simpler.

     -- Method:
     -- If  a  is  Not Euclidean, then the  algebraic complements
     -- are computed and so on - see the srcipt.

     -- If  a  is Euclidean,  then the Gauss reduction to the 
     -- staircase form  (s,t)  is applied,  t0 = unityMatrix  is a
     -- protocol.  If the last row of  s  is zero,  return  Mt [].
     -- Otherwise get  (s',t')  by reducing of the  up-diagonal 
     -- part.
     -- m  is invertible if and only if  s'  is diagonal and each
     -- s'(i,i)  is invertible.   
     -- In this case, put    im =  t'/ s'.



matrInv  mode m =

  (case  ( m, (matrHeight m)==(matrWidth m) )   of

    (Mt []  , _    ) ->  error "matrInv (Mt []) "
    (_      , False) ->  error "matrInv:  matrix is not square"
    (Mt rows, True ) ->
      let  
        zr = zero (head (head rows))
      in
        (case  (matrElem (/= zr) m, mode=="", mode=="s")  of
         
          (_ ,  False, False) ->
                           error "matrInv:  mode == \"\" | \"s\" "
          ([],  _    , _    ) ->  Mt []           --zero m 
          ([x], _    , _    ) ->
            if  (euclidean zr)/=Yes  then
                               error( "matrInv:  only Euclidean"
                                      ++ " case can handle so far"
                                    )
            else
              let  (s,t,_) =  (case  mode  of
                                    "s"-> (s,t,'+')
                                    _  -> toStairMatr "" m (Mt [])
                              )
                   (Mt rows_s) =  s
              in
                if  all (==zr) (last rows_s)  then  Mt []
                                               -- last row is zero
                else
                  let  (s',t',_) =  toStairMatr "u" s t
                                                  -- reduce uppers
                  in   
                    if  not (isDiagMatr s')  then  Mt []
                    else   
                      let  (Mt rs', Mt rt') = (s',t') 
                           diag            = mainMatrDiag s'
                           (succ,t)        = divideByDiag diag rt'
                      in
                        if  succ  then  Mt t   else  Mt []
        )
  )
    where

    divideByDiag  []   []   =  (True,[])
    divideByDiag  diag rows = 
      case  
        inv_l (head diag)
      of  
        []   ->  (False,rows)
        [ix] ->  
          (case  divideByDiag (tail diag) (tail rows)  of

            (False, _    ) ->  (False,rows)
            (True , rows') -> 
                       ( True,  (map (mul ix) (head rows)):rows' )
          )




------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------


test_toStairMatr ::  SyzygySolvableRing a => Matrix a -> String

test_toStairMatr  m =
  let
    (Mt rows) = m
    zr        = zero (head (head rows))
  in 
    case   matrElem (/= zr) m 
    of
      []  -> error "test_toStairMatr:  non-zero matrix needed"
      [x] ->
        let  (s,t,_) =  toStairMatr "" m (Mt [])
             t_by_m  =  matrMul t m
             s_str   =  w s ""
             eq_str  = 
                    if  t_by_m==s  then  "\n\nT x M = S   O.K."
                    else                 "\n\nERROR:  T x M /= S "
        in
           "\nStaircase form  S =\n\n" ++ (s_str++eq_str) ++"\n\n"



test_matrInv ::  SyzygySolvableRing a =>  Matrix a -> String

test_matrInv  m =  case   matrInv "" m   of

  (Mt []     ) ->  "\nNon-invertible matrix"
  (Mt im_rows) ->
    let 
      im     =  Mt im_rows
      [x]    =  matrElem (const True) im 
      zr     =  zero x
      [y]    =  matrElem (/= zr) im 
      unMatr =  scalMatr im_rows (unity y) zr
      m_im   =  matrMul m im
      im_m   =  matrMul im m
      im_str =  w im ""
      eq_str = 
          if  im_m==unMatr && m_im==unMatr
                then "\n\nim*m == m*im == unity matrix  O.K. \n\n"
          else   "\n\nERROR: im*m  or  m*im  /= unity matrix \n\n"

    in  
      "\nThe Inverse matrix  im  for  m  is \n\n"++(im_str++eq_str)

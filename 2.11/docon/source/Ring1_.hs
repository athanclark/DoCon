--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.09
--
--  Copyright  Serge Mechveliani,    2005
--------------------------------------------------------------------
--------------------------------------------------------------------




module Ring1_   

  -- Several auxiliary functions related to Ring
  --
  -- All needed from here is  reexported by  RingModule.hs, Z.

  (quotEuc, remEuc, multiplicity, isPowerOfNonInv,
   gxBasisInEuc, moduloBasisInEuc, syzygyGensInEuc, 
   moduloBasis_test, gxBasis_test, syzygyGens_test, gcd_test
   -- ,instances for Integer:  LinSolvRing, EuclideanRing
  )

where
import qualified Data.Map as Map (empty, lookup, insert) 

import Maybe (isJust, fromJust)
import List  (transpose       )

import DPrelude (PropValue(..), Z, showsWithDom)
import Categs    
       (CategoryName(..), Domain1(..), EucRingTerm(..),
        LinSolvRingTerm(..), Property_EucRing(..), 
        Property_LinSolvRing(..)
       )
import SetGroup (MulSemigroup(..), zeroS, unity, isZero, divides)
import Ring0_
import Ring_   (eucGCDE                       )
import VecMatr (matrRows, isZeroMt, rowMatrMul)
import LinAlg  (solveLinear_euc               )







--------------------------------------------------------------------
quotEuc, remEuc :: EuclideanRing a => Char -> a -> a -> a

quotEuc mode x = fst . divRem mode x
remEuc  mode x = snd . divRem mode x

{-# specialize quotEuc :: Char -> Z -> Z -> Z #-}
{-# specialize remEuc  :: Char -> Z -> Z -> Z #-}

--------------------------------------------------------------------
multiplicity :: CommutativeRing a =>  a -> a -> (Z,a)
                                   -- x    y     m q
  -- Multiplicity of  x  in  y  in factorial ring 
  --                                  - correct when (Factorial,Yes)
  -- q = y/(x^m),  
  -- x, y  non-zero,  x  should Not be invertible.

multiplicity x y 

  | isZero x || isZero y || (isJust $ inv_m x) =
            error $
               ("multiplicity x y,"++) $ showsWithDom x "x" "" $
               ("y = "++) $ shows y $ 
               "\n\nnon-zero  x,y  required and in-invertible  x \n"

  | otherwise = if  not $ divides x y  then (0, y) else  mlt x y 0   
      where
      mlt x y m = maybe (m, y) (\ q -> mlt x q (m+1)) $ divide_m y x

{-# specialize multiplicity :: Z -> Z -> (Z,Z) #-}

--------------------------------------------------------------------
isPowerOfNonInv :: CommutativeRing a =>  a -> a -> Bool
                                      -- x    y   
  -- "y is a power of x"  in factorial ring 
  --                                  - correct when (Factorial,Yes)
  -- x  should Not be invertible.

isPowerOfNonInv x y = case (isZero x, isZero y, multiplicity x y) of

   (iszX, iszY, m) -> (iszX && iszY) || 
                    ((not iszX) && (not iszY) && (snd m == unity x))

--------------------------------------------------------------------
gxBasisInEuc :: EuclideanRing a => [a] -> ([a], [[a]])

  -- Specialization of  gxBasis  for an Euclidean ring.
  -- It is applied, for example, for Z.

gxBasisInEuc xs = case xs of

         []  -> ([], []) 
         x:_ -> let {z = zeroS x;  (d, qs) = eucGCDE xs}
                in
                if  all (== z) xs  then ([], [])  else  ([d], [qs])


{- old ***************************************************
  (x:_) ->
    let  { zr = zeroS x;  un = unity x }
    in
      if  all (== zr) xs  then  ([], Mt []) 
      else
        (case  xs   of
           [x]   -> ([x], Mt [Vec [un]])
           [x,y] -> let  (d,u,v) = eucGCDE x y  in
                                             ([d], Mt [Vec [u,v]])
           _     ->
             let  (mt, Mt rowsT, _) = toStairMatr_euc ""
                                    (transp (Mt [Vec xs])) (Mt [])
                              -- t*transp[x1..xn] = transp[d,0..0]
                  (Vec qs) = head rowsT
                                   -- q1*x1+..+qn*xn = d = gcD(xs)
                  d        = matrHead mt
             in   ([d], Mt [Vec qs])
        )
***************************************************
-}





--------------------------------------------------------------------
moduloBasisInEuc :: 
                   EuclideanRing a => String -> [a] -> a -> (a, [a])

  -- Specialization of  moduloBasis  for an Euclidean ring.
  -- It is applied, for example, for Z.

moduloBasisInEuc _ xs y = case xs of

  []  -> (y, [])
  x:_ -> 
    let 
      {z = zeroS x; (d, qs) = eucGCDE xs; (q', r) = divRem 'c' y d}
    in
    if  all (== z) xs  then (y, map (const z) xs)
    else                    (r, map (* q')    qs)


{- old *************************************************
 case  xs  of [d] -> let  (q,r) = divRem 'c' y d  in  (r,[q])
              _   -> (case  gxBasisInEuc xs
            of  ([d], Mt [Vec qs]) -> let  (q',r) = divRem 'c' y d
                                      in  (r, map (* q') qs)
                _                  ->
            error ("gxBasisInEuc  should yield ([d], Mt [qs]) \n")
        )    
     *************************************************
-}




--------------------------------------------------------------------
syzygyGensInEuc :: EuclideanRing a => String -> [a] -> [[a]]

  -- Specialization of  syzygyGens  for an Euclidean ring.
  -- It is applied, for example, for Z.

syzygyGensInEuc mode xs = case xs of

  []     -> error ("syzygyGens " ++ mode ++ " []\n")
  (x:ys) -> let {z = zeroS x; u = unity x}
            in
            case (x == z, ys) 
            of
            (True, []) -> [[u]]
            (_   , []) -> []
            _          -> snd $ solveLinear_euc [xs] [z]

--------------------------------------------------------------------
moduloBasis_test :: LinSolvRing a => String -> [a] -> a -> String
moduloBasis_test                     mode      xs     y = 
  let
    (r, qs) = moduloBasis mode xs y
    [y1]    = rowMatrMul qs $ transpose [xs]

    mess1  = "\n(r,qs) = moduloBasis mode xs y   \n"

    mess2  = if  y == (y1+r)  then  "y = r + qs*xs  O.K.\n"
             else                   "ERROR:  y /= r + qs*xs \n"

    (r', _) = moduloBasis mode xs r

    mess3 = case (elem 'c' mode, r == r') of

      (False, _    ) -> ""
      (_    , False) -> 
              "ERROR:  \'c\' mode applied, but  r  is not canonic\n"
      _              ->
              "OK:  \'c\' mode applied, and  r  is a fixed point\n"
  in
  mess1 ++ mess2++ mess3




gxBasis_test :: 
              LinSolvRing a => [a] -> ([Bool], ([a], [[a]]), String)
                            -- xs               gs   mt
  -- find  gs = gxBasis,  gx' = gxBasis gs, 
  -- transformation matrix  mt  for xs->gs,
  -- test the  xs reduction by gs,  gs by gs',  gs' by gs

gxBasis_test  []       = error "gxBasis_test [] \n"
gxBasis_test  xs@(x:_) = 
  let
    d              = upLinSolvRing x Map.empty
    zr             = zeroS x
    (gs, mt)       = gxBasis xs
    (xsCol, gsCol) = (transpose [xs], transpose [gs])
    (xsM, gsM)     = (Mt xsCol d, Mt gsCol d)
    Mt xs'Col _    = (Mt mt d) * xsM
    xs_remainders  = map (fst . moduloBasis "" gs) xs
    (gs', _)       = gxBasis gs
    gs_by_gs'      = map (fst . moduloBasis "" gs') gs
    gs'_by_gs      = map (fst . moduloBasis "" gs ) gs'

    mess1 = if xs'Col == gsCol then  
                      " mt*(transp xsCol) == (transp gsCol)  O.K.\n"
            else    "ERROR:  mt*(transp xsCol) /= (transp gsCol) \n"
    
    mess2 = if all (== zr) xs_remainders  then
                               "gs  reduces  xs  to zeroes  O.K. \n"
            else      "ERROR: gs does NOT reduce all  xs  to zero\n"

    mess3 = if all (== zr) gs_by_gs' 
                                then  "gs' reduce gs to zero O.K.\n"
            else          "ERROR:  gs' does NOT reduce gs to zero\n"
    mess4 = if  all (==zr) gs'_by_gs 
                                then  "gs reduce gs' to zero O.K.\n"
            else          "ERROR:  gs does NOT reduce gs' to zero\n"
    msg =
       "Testing   (gs,mt) = gxBasis xs;  (gs',_) = gxBasis gs; \n\n"
       ++
       "          xs_remainders =  " ++
                            "map (fst .moduloBasis \"\" gs) xs \n\n"
       ++ 
       "xs = \n" ++ (show xsM) ++"\n\n"++
       "gs = \n" ++ (show gsM) ++"\n\n"++ 
       mess1 ++ mess2++ mess3 ++ mess4  
  in
  ([all (== zr) xs_remainders, 
    all (== zr) gs_by_gs' &&  all (== zr) gs'_by_gs,
    xs'Col == gsCol
   ],
   (gs, mt),
   msg
  )
    



syzygyGens_test :: LinSolvRing a => String -> [a] -> String
syzygyGens_test                     mode      xs@(x:_) = 
  let
    d          = upLinSolvRing x Map.empty
    xsCol      = transpose [xs]
    xsM        = Mt xsCol d
    rels       = syzygyGens mode xs
    productCol = (Mt rels d)*xsM

    mess = if  isZeroMt $ matrRows productCol  then  
                                " rels*xsCol == zeroColumn  O.K.\n"
           else                 " ERROR: rels*xsCol /= zeroColumn\n"

    rels' = if mode == "" then Mt rels d   
            else               Mt (syzygyGens "" xs) d     
  in
  "Testing   rels  = syzygyGens mode xs   \n"    ++
  "          rels' = syzygyGens \"\" xs   \n\n" 
  ++
  "xs    = \n" ++ (show xsM  ) ++ "\n\n" ++
  "rels  = \n" ++ (show rels ) ++ "\n\n" ++  
  "rels' = \n" ++ (show rels') ++ "\n\n" ++ mess


--------------------------------------------------------------------
gcd_test :: GCDRing a => a -> a -> a -> ([Bool], [a])
                      -- d    x    y     boos    [x',y',g]

  -- Test the properties of  g = gcd x' y',  x' = d*x, y' = d*y :
  -- boos = [g divides x', g divides y',
  --         gcd (x'/g) (y'/g)  is invertible
  --        ]
gcd_test d x y = 
  let 
    (zr, un, rR) = (zeroS d, unity d, snd $ baseGCDRing d Map.empty)

    msg = ("gcd_test d x y,"++) . showsWithDom d "d" "R" . 
          ("x = "++) . shows x . ("\ny = "++) . shows y . ("\n\n"++)
  in
  if  isGCDRing rR /= Yes  then
              error $ msg "(WithGCD, Yes)  needed for the ring  R\n"
  else
  if elem zr [d, x, y] then  error $ msg "Non-zero  d,x,y  needed\n"
  else      
  let (x', y') = (d*x, d*y)
      g        = gcD [x', y']
      (qx, qy) = (divide_m x' g, divide_m y' g)
      [q1, q2] = map fromJust [qx, qy]
      qg       = canAssoc $ gcD [q1, q2]
  in
  ([isJust qx, isJust qy, qg == un], [x', y', g])


--------------------------------------------------------------------
--------------------------------------------------------------------
instance LinSolvRing Integer  
  where
  moduloBasis = moduloBasisInEuc 
  gxBasis     = gxBasisInEuc
  syzygyGens  = syzygyGensInEuc

  baseLinSolvRing _ dm = case Map.lookup LinSolvRing dm of

    Just (D1LinSolvR t) -> (dm, t)
    _                   -> 
                       (Map.insert LinSolvRing (D1LinSolvR t) dm, t)
      where                      
      t = LinSolvRingTerm 
          {linSolvRingProps =
            [(ModuloBasisDetaching, Yes), (ModuloBasisCanonic, Yes),
             (WithSyzygyGens      , Yes), (IsGxRing          , Yes)
            ]
          }


instance EuclideanRing Integer  
  where
  eucNorm 0 = error "eucNorm (0::Z) \n"
  eucNorm n = abs n

  divRem mode x y = case (x, y) of

             -- for  mode /= 'm'  (divRem mode)  is the canonic-
             -- remainder division with the non-negative remainder
 
    (_, 0) -> error $ ("divRem "++) $ shows x " 0   in Z \n"
    (0, _) -> (0, 0)
    _      -> 
       case divMod x y   -- here  signum r == signum y
       of
       (q, 0) -> (q, 0)
       (q, r) -> case (mode == 'm', r > 0) of              

          (False, True ) -> (q, r)
          (False, False) -> (q+1, r-y)
          (True,  True ) -> if (y-r) < r then (q+1, r-y) else (q, r)
          _              ->  
                      if  (r-y) >= (-r)  then (q+1, r-y) else (q, r)


  baseEucRing _ dm =  case Map.lookup EuclideanRing dm of

    Just (D1EucR t) -> (dm, t)
    _               -> (Map.insert EuclideanRing (D1EucR t) dm, t)
      where
      t = EucRingTerm 
          {eucRingProps =
               [(Euclidean,Yes), (DivRemCan, Yes), (DivRemMin, Yes)] 
          }

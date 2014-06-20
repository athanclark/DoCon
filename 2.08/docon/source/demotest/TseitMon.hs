--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.07
--
--  Copyright  Serge Mechveliani,    2003
--------------------------------------------------------------------
--------------------------------------------------------------------




module TseitMon 
where
import DExport
import FAAGBas_ 

-- Tseitin's monoid:  K<a,b,c,d,e> / BiIdeal(fs), 
-- fs =
--      [a*c - c*a,    a*d - d*a,    b*c - c*b,     b*d - d*b,
--       e*c*a - a*e,  e*d*b - b*e,  a*b*a*c - a*b*a*c*e 
--      ]

type K = Fraction Z 
tt = 
  let
    q1    = 1:/1 :: K
    dK    = upField q1 emptyFM
    n     = 5 :: Z
    ivars = [(1,"a"),(2,"b"),(3,"c"),(4,"d"),(5,"e")]
    tostr i     = lookup i ivars
    fromstr str = lookup str [(xs,i) | (i,xs) <- ivars]

    p1  = cToFAA ord vd dK q1  :: FAA K
    vd  = (Just n, (tostr, fromstr))
    cp  = freeMWeightLexComp (const 1)
    ord = (("deglex", n), cp)

    [a,b,c,d,e] = varPs q1 p1

    fs = [a*c - c*a,    a*d - d*a,    b*c - c*b,     b*d - d*b,
          e*c*a - a*e,  e*d*b - b*e,  c*a*b*a*e - c*a*b*a 
         ]
               -- It is in normal form.
               -- If we choose another pp ordering, with  a,b < c,  
               -- then in the last equality  c  moves over  a and b.
    ----------------------------------------------------------------
    spol f g = (s, ct f m1, ct f m2)  where (s,m1,m2) = faaSPol f g 
                                                  -- s = f*m1 - m2*g
    biNF fs      = tuple33 . faaNF "rc" fs
    reduceAll fs = 
        filter (not . isZero) [fst $ biNF (delete f fs) f | f <- fs]

    testnfBi fs g = let ((_,_,rq), checks) = faaNF_test "rc" fs g
                    in  (rq, checks) 
    ----------------------------------------------------------------
  in
  [(f, g, spol f g, fst $ biNF fs (tuple31 $ spol f g)) | 
                                                    f <- fs, g <- fs
  ]



{- -----------------------------------------------------------------
faaNF_test "rc" fs (a*b*c*d*e)

biNF fs (a*b*c*d*e) 
  =
  (cdabe, [[((1),(bde))], [((c),(be))], [((a),(de))],
               [((ca),(e))],   [],            [],            []]
  )

[(f, g, spol f g, fst $ biNF fs (tuple31 $ spol f g)) | 
                                                    f <- fs, g <- fs
] = 
[
((ac-ca),(ac-ca),((0),(1),(1)),(0)),
((ac-ca),(ad-da),((acda-ca^2d),(ad),(ac)),(0)),
((ac-ca),(bc-cb),((ac^2b-cabc),(bc),(ac)),(0)),
((ac-ca),(bd-db),((acdb-cabd),(bd),(ac)),(0)),
((ac-ca),(eca-ae),((-caeca + acae),(eca),(ac)),(0)),
((ac-ca),(edb-be),((-caedb + acbe),(edb),(ac)),(0)),

((ac-ca),(cabae-caba),((-ca^2bae + acaba),(abae),(a)),
                                          (-ca^2bae + ca^2ba)),

((ad-da),(ac-ca),((adca-da^2c),(ac),(ad)),(0)),
((ad-da),(ad-da),((0),(1),(1)),(0)),
((ad-da),(bc-cb),((adcb-dabc),(bc),(ad)),(0)),
((ad-da),(bd-db),((ad^2b-dabd),(bd),(ad)),(0)),
((ad-da),(eca-ae),((-daeca + adae),(eca),(ad)),(0)),
((ad-da),(edb-be),((-daedb + adbe),(edb),(ad)),(0)),

((ad-da),(cabae-caba),((-dacabae + adcaba),(cabae),(ad)),
                                           (-dca^2bae + dca^2ba)),
                                                                 ?
((bc-cb),(ac-ca),((bc^2a-cbac),(ac),(bc)),(0)),
((bc-cb),(ad-da),((bcda-cbad),(ad),(bc)),(0)),
((bc-cb),(bc-cb),((0),(1),(1)),(0)),
((bc-cb),(bd-db),((bcdb-cb^2d),(bd),(bc)),(0)),
((bc-cb),(eca-ae),((-cbeca + bcae),(eca),(bc)),(0)),
((bc-cb),(edb-be),((-cbedb + bcbe),(edb),(bc)),(0)),
((bc-cb),(cabae-caba),((-cbabae + bcaba),(abae),(b)),
                                            (-cbabae + cbaba)),
((bd-db),(ac-ca),((bdca-dbac),(ac),(bd)),(0)),
((bd-db),(ad-da),((bd^2a-dbad),(ad),(bd)),(0)),
((bd-db),(bc-cb),((bdcb-db^2c),(bc),(bd)),(0)),
((bd-db),(bd-db),((0),(1),(1)),(0)),
((bd-db),(eca-ae),((-dbeca + bdae),(eca),(bd)),(0)),
((bd-db),(edb-be),((-dbedb + bdbe),(edb),(bd)),(0)),
((bd-db),(cabae-caba),((-dbcabae + bdcaba),(cabae),(bd)),
                                           (-dcbabae + dcbaba)),
((eca-ae),(ac-ca),((ec^2a-aec),(c),(ec)),(ec^2a-aec)),
((eca-ae),(ad-da),((ecda-aed),(d),(ec)),(ecda-aed)),
((eca-ae),(bc-cb),((ecacb-aebc),(bc),(eca)),(ec^2ab-aecb)),
((eca-ae),(bd-db),((ecadb-aebd),(bd),(eca)),(ecdab-abe)),
((eca-ae),(eca-ae),((0),(1),(1)),(0)),
((eca-ae),(edb-be),((-ae^2db + ecabe),(edb),(eca)),(0)),
((eca-ae),(cabae-caba),((-aebae + ecaba),(bae),(e)),(-aebae + aeba)),
((edb-be),(ac-ca),((edbca-beac),(ac),(edb)),(edcba-bae)),
((edb-be),(ad-da),((edbda-bead),(ad),(edb)),(ed^2ba-beda)),
((edb-be),(bc-cb),((edcb-bec),(c),(ed)),(edcb-bec)),
((edb-be),(bd-db),((ed^2b-bed),(d),(ed)),(ed^2b-bed)),
((edb-be),(eca-ae),((-be^2ca + edbae),(eca),(edb)),(0)),
((edb-be),(edb-be),((0),(1),(1)),(0)),
((edb-be),(cabae-caba),((-becabae + edbcaba),(cabae),(edb)),(edcbaba-baebae)),
((cabae-caba),(ac-ca),((cabaeca-caba^2c),(ac),(cabae)),(caba^2e-c^2aba^2)),
((cabae-caba),(ad-da),((cabaeda-caba^2d),(ad),(cabae)),(0)),
((cabae-caba),(bc-cb),((cabaecb-cababc),(bc),(cabae)),(0)),
((cabae-caba),(bd-db),((cabaedb-cababd),(bd),(cabae)),(cababe-cdabab)),
((cabae-caba),(eca-ae),((caba^2e-cabaca),(ca),(caba)),(caba^2e-c^2aba^2)),
((cabae-caba),(edb-be),((cababe-cabadb),(db),(caba)),(cababe-cdabab)),
((cabae-caba),(cabae-caba),((0),(1),(1)),(0))]

-------------------------------------------------------------------
-}








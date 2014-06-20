--------------------------------------------------------------------
--------------------------------------------------------------------
--  The Algebraic Domain Constructor  DoCon,   version 2.08
--
--  Copyright  Serge Mechveliani,    2004
--------------------------------------------------------------------
--------------------------------------------------------------------




module FAATest
where
import DExport

type K = Fraction Z 

ringCommut :: Ring a => a -> a -> a  
ringCommut              a    b = a*b - b*a

tt = 
  let
    q1    = 1:/1 :: K
    dK    = upField q1 emptyFM
    n     = 6 :: Z
    ivars = [(1,"t12"),(2,"t13"),(3,"t14"), (4,"t23"),(5,"t24"),
             (6,"t34")
            ]
    tostr i     = lookup i ivars
    fromstr str = lookup str [(xs,i) | (i,xs) <- ivars]

    p1  = cToFAA ord vd dK q1  :: FAA K
    vd  = (Just n, (tostr, fromstr))
    cp  = freeMWeightLexComp (const 1)
    ord = (("deglex", n), cp)

    t i j = smParse p1 ('t':(shows i $ show j))

    comm i j k l = ringCommut (t i j) (t k l) 

    rels4 i j k l = if j /= k then [comm i j k l]
                    else           [(comm i j k l)-(comm j l i l),
                                    (comm i j k l)-(comm i l i j)
                                   ]

    f = (t 1 2)^2*(t 1 3)^2*(t 1 4)^2
    g =                     (t 1 4)

    frompp x      = ct p1 (q1,x)
    (mq1,mq2,mq3) = divide_m2 (faaLPP f) (faaLPP g)
  in
  (f, g,  fmap frompp mq1, fmap frompp mq2,
          fmap (\ (x,y) -> (frompp x, frompp y)) mq3
  )

--  [((i,j,k,l), rels4 i j k l) |  
--   i <- [1..3], j <- [(i+1) .. 4], k <- [1..3], l <- [(k+1) .. 4]  ]


{-
[((1,2,1,2),[(0)]),
((1,2,1,3),[(t12*t13 - t13*t12)]),
((1,2,1,4),[(t12*t14 - t14*t12)]),
((1,2,2,3),[(t12*t23 + t13*t23 - t23*t12 - t23*t13),
            (t12*t13 + t12*t23 -t13*t12 - t23*t12)]
),
((1,2,2,4),[(t12*t24 + t14*t24 - t24*t12 - t24*t14),
            (t12*t14 + t12*t24 - t14*t12 - t24*t12)]
),
((1,2,3,4),[(t12*t34 - t34*t12)]),
((1,3,1,2),[(-1*t12*t13 + t13*t12)]),
((1,3,1,3),[(0)]),((1,3,1,4),[(t13*t14 - t14*t13)]),((1,3,2,3),[(t13*t23 - t23*t13)]),((1,3,2,4),[(t13*t24 - t24*t13)]),((1,3,3,4),[(t13*t34 + t14*t34 - t34*t13 - t34*t14),(t13*t14 + t13*t34 - t14*t13 - t34*t13)]),((1,4,1,2),[(-1*t12*t14 + t14*t12)]),((1,4,1,3),[(-1*t13*t14 + t14*t13)]),((1,4,1,4),[(0)]),((1,4,2,3),[(t14*t23 - t23*t14)]),((1,4,2,4),[(t14*t24 - t24*t14)]),((1,4,3,4),[(t14*t34 - t34*t14)]),((2,3,1,2),[(-1*t12*t23 + t23*t12)]),((2,3,1,3),[(-1*t13*t23 + t23*t13)]),((2,3,1,4),[(-1*t14*t23 + t23*t14)]),((2,3,2,3),[(0)]),((2,3,2,4),[(t23*t24 - t24*t23)]),((2,3,3,4),[(t23*t34 + t24*t34 - t34*t23 -
t34*t24),(t23*t24 + t23*t34 - t24*t23 - t34*t23)]),((2,4,1,2),[(-1*t12*t24 + t24*t12)]),((2,4,1,3),[(-1*t13*t24 + t24*t13)]),((2,4,1,4),[(-1*t14*t24 + t24*t14)]),((2,4,2,3),[(-1*t23*t24 + t24*t23)]),((2,4,2,4),[(0)]),((2,4,3,4),[(t24*t34 -
t34*t24)]),((3,4,1,2),[(-1*t12*t34 + t34*t12)]),((3,4,1,3),[(-1*t13*t34 + t34*t13)]),((3,4,1,4),[(-1*t14*t34 + t34*t14)]),((3,4,2,3),[(-1*t23*t34 + t34*t23)]),((3,4,2,4),[(-1*t24*t34 + t34*t24)]),((3,4,3,4),[(0)])]

-}

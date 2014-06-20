------------------------------------------------------------------
------------------------------------------------------------------
-- The Algebraic Domain Constructor  DoCon,   version 0.01

-- Copyright  Sergey D.Mechveliani,  1993-1995             
------------------------------------------------------------------
------------------------------------------------------------------


meshvel@botik.ru




This is the current  -  on October 30, 1995  -

state of the DoCon project.


******************************************************************
The project is in its beginning.  NO GUARRANTEES.
******************************************************************


The program is written in  Haskell  (1.2  - so far).

Currently, it runs (compiles) under 

             Glasgow Haskell  ghc-0.26-linux

             ( ftp.dcs.glasgow.ac.uk )

The OS was  linux-1.2...

I think, it should work under any standard Haskell-1.2 compiler
(and any operating system).

-----------------------------------------------------------------


INSTALLATION.

As you are reading this text, you had already managed to 
unarchivate the thing:

                  tar  xvfz  docon-0.01.tar.gz
        
If your working directory was          foo/   
then you obtain by this                foo/docon/
with several subdirectories in it.

foo/docon/README.txt   is this file.
foo/docon/doc/*        contains the documentation 
                       (only introduction so far).
foo/docon/docon/*      contains the sources.

The source scripts contain a lot of useful commentaries.


1. Command        cd  foo/docon/docon

2. Edit the line of  Makefile  containing  "mkdependHS" 
   substring according to the location of your Haskell.
   (This is for  ghc  system, I do not know what it will be,
   say, for the Chalmers one).

3. Command        make run 

This compiles everything and prepares the executable file  
"run".

and  .o  file for each  .hs  one.  This may take a lot of time.

run  performs the computation programmed in the module  Main.hs.

To do another computation, you should edit accordingly  Main.hs
and command 
                      make run

(this time it compiles only one module), and then again run run. 

This is the batch mode.  The dialogue mode I leave for the future.

Main.hs  contains the tests presenting the recent abilities of the
system.

I hope that   pro-filing + some future tuning +  -O2 option 
may produce much faster program.
So far, we do not think of optimizations.

------------------------------------------------------------------


Sergey D.Mechveliani

meshvel@botik.ru
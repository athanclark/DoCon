{-# OPTIONS -fno-warn-duplicate-exports #-}
module DExport

  -- All the export of  DoCon + part of GHC exploited by DoCon.
  --
  -- Set the line  import DExport
  -- 
  -- if you are lazy to find more precisely which modules your 
  -- program needs 

  (module DPrelude,    module Categs,     module SetGroup,  
   module RingModule,  module Z,          module DPair,  
   module Fraction,    module Permut,     module VecMatr,  
   module Pol,         module Residue,    module LinAlg,  
   module GBasis,      module Partition,  module AlgSymmF,

   module Data.FiniteMap, module Complex,

   module Prelude, module List,  module Ratio, module Random
  )
where

import Data.FiniteMap
import Complex

import List    hiding (minimum, maximum, sort, sortBy)
import Prelude hiding (minimum, maximum,             )
import Ratio 
import Random 

import DPrelude
import Categs
import SetGroup
import RingModule
import Z
import DPair
import Fraction
import VecMatr
import LinAlg
import Permut
import Pol
import Residue
import GBasis
import Partition
import AlgSymmF



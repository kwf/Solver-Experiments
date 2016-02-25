{-# LANGUAGE QuasiQuotes #-}

module Examples where

import SimpleSolver

-- EXAMPLE INPUTS

-- This loops the solver if addToWorkList is wrong
-- Note: Prepend New Work to the Work List
ab_bc_ca :: [Equality]
ab_bc_ca = [c| x ~ y, y ~ z, z ~ x |]

-- This loops the solver if we process FunCans first
-- Note: Ordered Processing of Flattening Results
f_int_bool :: [Equality]
f_int_bool = [c| F(Int) ~ Bool |]



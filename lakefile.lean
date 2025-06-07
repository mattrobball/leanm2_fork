import Lake
open Lake DSL

package «lean-m2» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

require scilean from git
  "https://github.com/lecopivo/SciLean.git" @ "blas"


@[default_target]
lean_lib LeanM2 where

@[default_target]
lean_lib Examples where

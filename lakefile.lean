import Lake
open Lake DSL

package «lean-m2» {
  -- add any package configuration options here
}

require scilean from git
  "https://github.com/lecopivo/SciLean.git" @ "master"

@[default_target]
lean_lib LeanM2 where

@[default_target]
lean_lib Examples where

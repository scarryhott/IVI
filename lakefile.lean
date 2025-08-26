import Lake
open Lake DSL

package "ivi" where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib "IVI" where
  -- add library configuration options here

@[default_target]
lean_exe "ivi" where
  root := `Main
  supportInterpreter := true

import Lake
open Lake DSL

package "ivi" where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «IVI» {
  -- add any library configuration options here
}

lean_lib «Classical» {
  -- Classical Bombieri-Lagarias equivalence
}

lean_lib "IVI_Bridge_Minimal" where
  -- Minimal compilable implementation of canonical bridge identity

lean_lib "IVI_Core_Clean" where
  -- Core clean IVI implementation

@[default_target]
lean_exe "ivi" where
  root := `Main
  supportInterpreter := true

import Lake
open Lake DSL

package "ivi" where
  -- add configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

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

-- Expose top-level modules so `Main` can import them
lean_lib "IVI_Simple" where

lean_lib "IVI_Foundation" where

lean_lib "IVI_Adelic_Geometry" where

lean_lib "IVI_Concrete_Blueprint" where

lean_lib "IVI_MetaVectorization" where

lean_lib "IVI_Integration_Master" where

lean_lib "IVI_Pattern_Bridge" where

lean_lib "IVI_Pattern_Examples" where

/-! Route B lemmas library as a separate build target. -/
lean_lib "IVI_RouteB_Lemmas" where
  -- Focus build on `IVI_RouteB_Lemmas.lean` and its deps

lean_lib "IVI_RouteB_Direct_RH" where
  -- Direct combination of Route B hypotheses implying RH

lean_lib "IVI_Internal_RH" where
  -- Internal wrapper around Route B to expose a clean entrypoint

lean_lib "IVI_RouteB_Internal_Instantiate" where
  -- Demo instantiation of the internal Route B wrapper

@[default_target]
lean_exe "ivi" where
  root := `Main
  supportInterpreter := true

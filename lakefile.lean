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
  srcDir := "Classical"
}

lean_lib «IVI.Lemmas» {
  srcDir := "IVI/Lemmas"
}

lean_lib «IVI.Operators» {
  srcDir := "IVI/Operators"
}

lean_lib «IVI.FactorialBridge» {
  srcDir := "IVI/FactorialBridge"
}

lean_lib "IVI_Simple" where
  -- IVI Simple formalization library

lean_lib "IVI_Entropy_Reduction_Clean" where
  -- Clean entropy reduction proofs

lean_lib "IVI_Convergence_Clean" where
  -- Clean convergence theorem proofs

lean_lib "IVI_Entropy_Minimal" where
  -- Minimal verifiable entropy reduction proofs

lean_lib "IVI_Entropy_Working" where
  -- Working entropy reduction proofs connected to IVI.Core

lean_lib "IVI_Entropy_Final" where
  -- Final compilable entropy reduction proofs

lean_lib "IVI_Factorial_Sieve_Bridge" where
  -- Factorial sieve bridge to RH proof

@[default_target]
lean_exe "ivi" where
  root := `Main
  supportInterpreter := true

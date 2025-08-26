import IVI.IVI_Automaton

open IVI_Automaton

def main : IO Unit := do
  -- Example usage of the IVI automaton
  let idx := Idx.a
  IO.println s!"Example index: {idx}"
  
  -- Compute and print the IVI score for the example automaton
  let iviScore := IVI_of_idx
  IO.println s!"IVI score for the example automaton: {iviScore}"

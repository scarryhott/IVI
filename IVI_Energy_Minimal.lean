/-
IVI_Energy_Minimal.lean

Predicate vs numeric energy for “approximation arbitrarily close”:
  • IVI_EnergyZero S x₀ : Prop  ≃  x₀ ∈ closure S
  • IVI_energyEnnreal S x₀ : ℝ≥0∞ := Metric.infEdist x₀ S
  • IVI_energyReal   S x₀ : ℝ     := (Metric.infEdist x₀ S).toReal

Main equivalences:
  IVI_EnergyZero S x₀
  ↔ x₀ ∈ closure S
  ↔ IVI_energyEnnreal S x₀ = 0
  (and, when S is nonempty) ↔ IVI_energyReal S x₀ = 0
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Instances.Real

open Set Metric

section Energy

variable {E : Type*} [PseudoMetricSpace E]

/-- “Energy zero” as approximation arbitrarily close (ε–δ formulation). -/
def IVI_EnergyZero (S : Set E) (x₀ : E) : Prop :=
  ∀ ε > 0, ∃ f ∈ S, dist x₀ f < ε

/-- Numeric energy as infimum (extended) distance. -/
def IVI_energyEnnreal (S : Set E) (x₀ : E) : ℝ≥0∞ :=
  Metric.infEdist x₀ S

/-- Numeric energy as a real via `toReal`. Note: this maps `∞` to `0`. -/
def IVI_energyReal (S : Set E) (x₀ : E) : ℝ :=
  (IVI_energyEnnreal S x₀).toReal

/-- The ε–δ predicate is exactly “in the closure”. -/
lemma IVI_EnergyZero_iff_mem_closure {S : Set E} {x₀ : E} :
    IVI_EnergyZero S x₀ ↔ x₀ ∈ closure S := by
  classical
  constructor
  · intro h
    have : ∀ ε > 0, ∃ y ∈ S, dist y x₀ < ε := by
      intro ε hε
      rcases h ε hε with ⟨f, hfS, hf⟩
      simpa [dist_comm] using hf
    simpa [mem_closure_iff] using this
  · intro hx ε hε
    have : ∃ y ∈ S, dist y x₀ < ε := by
      simpa [mem_closure_iff] using hx
    rcases this with ⟨y, hyS, hy⟩
    exact ⟨y, hyS, by simpa [dist_comm] using hy⟩

/-- `x₀ ∈ closure S` iff the infimum extended distance is zero. -/
lemma mem_closure_iff_energyEnnreal_zero {S : Set E} {x₀ : E} :
    x₀ ∈ closure S ↔ IVI_energyEnnreal S x₀ = 0 := by
  simpa [IVI_energyEnnreal] using
    (mem_closure_iff_infEdist_zero : x₀ ∈ closure S ↔ infEdist x₀ S = 0)

/-- Predicate ↔ numeric energy (ℝ≥0∞). -/
lemma energyEnnreal_zero_iff_IVI_EnergyZero {S : Set E} {x₀ : E} :
    IVI_energyEnnreal S x₀ = 0 ↔ IVI_EnergyZero S x₀ := by
  constructor
  · intro h0
    have : x₀ ∈ closure S := (mem_closure_iff_energyEnnreal_zero).mpr h0
    exact (IVI_EnergyZero_iff_mem_closure).mpr this
  · intro hEz
    have : x₀ ∈ closure S := (IVI_EnergyZero_iff_mem_closure).mp hEz
    exact (mem_closure_iff_energyEnnreal_zero).mp this

/-- Helper: If `S` is nonempty then `infEdist x₀ S < ∞`. -/
lemma energyEnnreal_ne_top_of_nonempty {S : Set E} {x₀ : E}
    (hS : S.Nonempty) : IVI_energyEnnreal S x₀ ≠ ∞ := by
  rcases hS with ⟨y, hyS⟩
  -- `infEdist x S ≤ edist x y`, and `edist x y` is finite in a (pseudo)metric space
  have hle : IVI_energyEnnreal S x₀ ≤ edist x₀ y := by
    simpa [IVI_energyEnnreal] using infEdist_le_iff.mpr ⟨y, hyS, le_rfl⟩
  -- hence it's not ∞
  refine ne_of_lt ?_
  have : edist x₀ y < ∞ := by
    -- `edist` is finite in pseudo metric spaces
    simpa using (edist_ne_top x₀ y)
  exact lt_of_le_of_lt hle this

/-- Predicate ↔ numeric energy (ℝ), assuming the set is nonempty (rules out `∞`). -/
lemma energyReal_zero_iff_IVI_EnergyZero_of_nonempty {S : Set E} {x₀ : E}
    (hS : S.Nonempty) : IVI_energyReal S x₀ = 0 ↔ IVI_EnergyZero S x₀ := by
  have h₀ : IVI_energyEnnreal S x₀ = 0 ↔ IVI_EnergyZero S x₀ :=
    energyEnnreal_zero_iff_IVI_EnergyZero
  constructor
  · intro h
    -- `toReal = 0` and not `∞` ⇒ value is `0` in ℝ≥0∞
    have hfin : IVI_energyEnnreal S x₀ ≠ ∞ := energyEnnreal_ne_top_of_nonempty (x₀ := x₀) hS
    have : IVI_energyEnnreal S x₀ = 0 := by
      -- `ENNReal.toReal_eq_zero` gives: toReal x = 0 ↔ x = 0 ∨ x = ∞
      -- exclude `∞` using `hfin`.
      have := (ENNReal.toReal_eq_zero).1 (by simpa [IVI_energyReal] using h)
      exact this.resolve_right hfin
    exact h₀.mp this
  · intro hE
    -- if predicate holds, ennreal energy = 0; hence toReal = 0
    have : IVI_energyEnnreal S x₀ = 0 := h₀.mpr hE
    simpa [IVI_energyReal, this]

/-- Monotonicity (ℝ≥0∞): enlarging the set can only decrease energy. -/
lemma energyEnnreal_mono {S T : Set E} {x₀ : E} (hST : S ⊆ T) :
    IVI_energyEnnreal T x₀ ≤ IVI_energyEnnreal S x₀ := by
  simpa [IVI_energyEnnreal] using (infEdist_mono (x := x₀) hST)

/-- Nonnegativity (ℝ≥0∞). -/
lemma energyEnnreal_nonneg {S : Set E} {x₀ : E} :
    (0 : ℝ≥0∞) ≤ IVI_energyEnnreal S x₀ := by
  exact bot_le

/-- Nonnegativity (ℝ). -/
lemma energyReal_nonneg {S : Set E} {x₀ : E} :
    0 ≤ IVI_energyReal S x₀ := by
  simpa [IVI_energyReal] using ENNReal.toReal_nonneg

/-- Real-energy monotonicity, assuming nonempty sets to avoid `∞`. -/
lemma energyReal_mono_of_nonempty {S T : Set E} {x₀ : E}
    (hST : S ⊆ T) (hS : S.Nonempty) :
    IVI_energyReal T x₀ ≤ IVI_energyReal S x₀ := by
  have hT : T.Nonempty := hS.mono hST
  have hTfin : IVI_energyEnnreal T x₀ ≠ ∞ := energyEnnreal_ne_top_of_nonempty (x₀ := x₀) hT
  have hSfin : IVI_energyEnnreal S x₀ ≠ ∞ := energyEnnreal_ne_top_of_nonempty (x₀ := x₀) hS
  have hmono := energyEnnreal_mono (x₀ := x₀) hST
  exact ENNReal.toReal_mono hTfin hSfin hmono

end Energy


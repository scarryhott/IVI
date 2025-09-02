/-
  Harder direction (BN ⇒ IVI-energy=0 for linear invariances), abstract form.

  Works over any normed space H over 𝕜 = ℝ or ℂ.
  You instantiate:
    • H   := your Hilbert space (e.g. L^2(0,1))
    • V   := the submodule (span of your BN/IVI generators)
    • x0  := the target vector (the constant-1 function)
    • L   := a continuous linear functional encoding the IVI invariance
    • g∈V with L g ≠ 0 (a witness direction to correct L)

  Result: for every ε>0 you can hit the affine slice {f∈V | L f = L x0}
  within ε of x0. Hence x0 ∈ closure(slice) and the "energy" infimum is 0.
-/

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module
import Mathlib.Topology.Algebra.Module.Basic

open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [IsROrC 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The IVI affine slice for a linear invariance `L`, through the point `x0`. -/
def affineSlice (V : Submodule 𝕜 H) (L : ContinuousLinearMap 𝕜 H 𝕜) (x0 : H) : Set H :=
  { f : H | f ∈ (V : Set H) ∧ L f = L x0 }

/--
BN-side approximation hypothesis, metric form:
`x0 ∈ closure (V : Set H)` is equivalent to
`∀ ε>0, ∃ v∈V, ‖x0 - v‖ < ε` in a metric space.

We take this as an input lemma to keep dependencies light.
-/
def BNApprox (V : Submodule 𝕜 H) (x0 : H) : Prop :=
  ∀ {ε : ℝ}, ε > 0 → ∃ v : H, v ∈ (V : Set H) ∧ ‖x0 - v‖ < ε

/--
**Harder direction (abstract, linear-invariance version).**

Assume:
  * `BNApprox V x0`: the BN closure condition (metric form).
  * `g ∈ V` with `L g ≠ 0`.

Then for every `ε>0`, there exists `f ∈ V` with `L f = L x0` and `‖x0 - f‖ < ε`.

This shows `x0 ∈ closure (affineSlice V L x0)`, hence the IVI "energy" on that slice is 0.
-/
theorem approx_in_affineSlice_of_BN
    (V : Submodule 𝕜 H)
    (L : ContinuousLinearMap 𝕜 H 𝕜)
    {x0 g : H}
    (hBN : BNApprox (𝕜:=𝕜) V x0)
    (hgV : g ∈ (V : Set H))
    (hLg : L g ≠ 0) :
    ∀ {ε : ℝ}, ε > 0 → ∃ f : H, f ∈ affineSlice V L x0 ∧ ‖x0 - f‖ < ε := by
  classical
  -- Constants for the error bound:
  -- We will ensure ‖x0 - v‖ < ε / K so that ‖x0 - f‖ ≤ ε.
  let denom : ℝ := ‖L g‖
  have hdenom : 0 < denom := by
    -- since L g ≠ 0 in 𝕜, its norm is strictly positive
    have : ‖(L g)‖ ≠ 0 := by
      simpa [IsROrC.norm_eq_abs] using congrArg IsROrC.abs hLg
    exact lt_of_le_of_ne' (by exact norm_nonneg _) this

  -- Operator norm of L (‖L‖), used in the bound |α| ≤ ‖L‖ ‖x0 - v‖ / ‖L g‖
  let K : ℝ := 1 + (‖L‖ * ‖g‖) / denom
  have hKpos : 0 < K := by
    have : 0 ≤ (‖L‖ * ‖g‖) / denom := by
      have : 0 ≤ ‖L‖ * ‖g‖ := by
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      exact div_nonneg this (le_of_lt hdenom)
    have : 1 ≤ K := by
      have : 0 ≤ (‖L‖ * ‖g‖) / denom := by
        have : 0 ≤ ‖L‖ * ‖g‖ := by
          exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
        exact div_nonneg this (le_of_lt hdenom)
      simpa [K] using add_le_add_left this 1
    exact lt_of_le_of_lt (show (0:ℝ) < 1 by decide) (lt_of_le_of_ne this (by simp [K]))

  intro ε hε
  -- Choose v∈V with ‖x0 - v‖ < ε / K by the BN approximation.
  have hδ : ε / K > 0 := by
    exact div_pos hε hKpos
  obtain ⟨v, hvV, hv⟩ := hBN hδ

  -- Define α := (L x0 - L v) / (L g) and f := v + α • g.
  -- This corrects L so that L f = L x0 while staying in V.
  let α : 𝕜 := (L x0 - L v) / (L g)
  have f_in_V : v + α • g ∈ (V : Set H) := by
    -- V is a submodule: closed under + and •
    have hvV' : v ∈ V := by simpa using hvV
    have hgV' : g ∈ V := by simpa using hgV
    -- use submodule closure properties
    exact
      (V.add_mem hvV' (V.smul_mem (α) hgV')).elim
  -- L f = L (v + α • g) = L v + α * L g = L x0
  have Lf_eq : L (v + α • g) = L x0 := by
    simp [map_add, map_smul, α, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg,
      IsROrC.div_eq_inv_mul, inv_mul_cancel₀ hLg]

  -- Now bound the distance: ‖x0 - f‖ ≤ ‖x0 - v‖ + |α| ‖g‖
  -- and |α| ≤ ‖L‖ ‖x0 - v‖ / ‖L g‖
  have alpha_bound :
      ‖α‖ ≤ (‖L‖ * ‖x0 - v‖) / denom := by
    -- |α| = |L(x0) - L(v)| / |L(g)| ≤ ‖L‖‖x0 - v‖ / ‖L g‖
    have : ‖L x0 - L v‖ ≤ ‖L‖ * ‖x0 - v‖ := by
      -- use operator norm inequality
      have := L.opNorm_bound (x0 - v)
      -- opNorm_bound: ‖L z‖ ≤ ‖L‖ ‖z‖; rewrite
      simpa [map_sub] using this
    have : ‖(L x0 - L v)‖ / denom ≤ (‖L‖ * ‖x0 - v‖) / denom := by
      exact div_le_div_of_le_of_nonneg this (le_of_lt hdenom)
    -- convert ‖α‖ = ‖(L x0 - L v) / (L g)‖ to the real-norm inequality above
    have hα : ‖α‖ = ‖L x0 - L v‖ / denom := by
      -- over IsROrC, ‖a / b‖ = ‖a‖ / ‖b‖
      simp [α, norm_div]
    simpa [hα]

  -- Triangle bound to finish
  refine ⟨v + α • g, ?_, ?_⟩
  · -- membership in the affine slice
    refine And.intro f_in_V ?_
    simpa [Lf_eq]
  ·
    -- ‖x0 - (v + α • g)‖ ≤ ‖x0 - v‖ + ‖α‖‖g‖ ≤ ‖x0 - v‖ + (‖L‖‖x0 - v‖/‖L g‖)‖g‖
    have := calc
      ‖x0 - (v + α • g)‖
          = ‖(x0 - v) - α • g‖ := by abel_nf
      _ ≤ ‖x0 - v‖ + ‖α • g‖ := norm_sub_le _ _
      _ ≤ ‖x0 - v‖ + ‖α‖ * ‖g‖ := by
            simpa [norm_smul]
      _ ≤ ‖x0 - v‖ + ((‖L‖ * ‖x0 - v‖) / denom) * ‖g‖ := by
            gcongr
            exact alpha_bound
      _ = ‖x0 - v‖ * (1 + (‖L‖ * ‖g‖) / denom) := by
            ring_nf [mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div, add_comm, add_left_comm, add_assoc]
      _ < (ε / K) * K := by
            have hv' : ‖x0 - v‖ < ε / K := hv
            have : (1 + (‖L‖ * ‖g‖) / denom) = K := rfl
            simpa [this] using (mul_lt_mul_of_pos_right hv' hKpos)
      _ = ε := by
            field_simp [K, ne_of_gt hKpos]
    exact this

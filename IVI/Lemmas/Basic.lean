/-
IVI/Lemmas/Basic.lean
A bucket of standard lemmas that tend to be "sorry" hotspots.
-/
import Mathlib
open scoped Real Topology BigOperators
open MeasureTheory Filter

noncomputable section

namespace IVI.Basic

/-- `cos x ≤ 1` (real) -/
lemma cos_le_one (x : ℝ) : Real.cos x ≤ 1 := by simpa using Real.cos_le_one x

/-- `-1 ≤ cos x` (real) -/
lemma neg_one_le_cos (x : ℝ) : -1 ≤ Real.cos x := by simpa using Real.neg_one_le_cos x

/-- `0 ≤ 1 - cos x` -/
lemma one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  exact sub_nonneg.mpr (cos_le_one x)

/-- `0 ≤ (1 - cos (n θ))` for all `n : ℕ` -/
lemma one_sub_cos_nθ_nonneg (n : ℕ) (θ : ℝ) : 0 ≤ 1 - Real.cos ((n : ℝ) * θ) := by
  simpa using one_sub_cos_nonneg ((n:ℝ) * θ)

/-- Measurability of `θ ↦ 1 - cos (n θ)` -/
lemma measurable_one_sub_cos (n : ℕ) :
    Measurable (fun θ : ℝ => 1 - Real.cos ((n : ℝ) * θ)) := by
  have h : Measurable fun θ : ℝ => (n : ℝ) * θ :=
    measurable_const.mul measurable_id
  simpa using (measurable_const.sub (Real.measurable_cos.comp h))

/-- AE nonnegativity over a restricted measure -/
lemma ae_nonneg_one_sub_cos
    (μ : Measure ℝ) (S : Set ℝ) (n : ℕ) :
    0 ≤ᵐ[μ.restrict S] fun θ => 1 - Real.cos ((n : ℝ) * θ) := by
  filter_upwards with θ
  exact one_sub_cos_nθ_nonneg n θ

/-- Nonnegativity of integrals for AE-nonnegative integrands (real-valued) -/
lemma integral_nonneg_of_ae'
    {μ : Measure ℝ} {f : ℝ → ℝ}
    (h : 0 ≤ᵐ[μ] fun x => f x) :
    0 ≤ ∫ x, f x ∂μ :=
  integral_nonneg_of_ae h

/-- Sum of nonnegatives is nonnegative -/
lemma sum_nonneg {ι} {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i := by
  exact Finset.sum_nonneg h

/-- Finite product of nonnegatives is nonnegative -/
lemma prod_nonneg {ι} [DecidableEq ι] {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i := by
  exact Finset.prod_nonneg h

/-- Square is nonnegative -/
lemma sq_nonneg (x : ℝ) : 0 ≤ x^2 := by exact pow_two_nonneg x

/-- Convergence of `∑ 1/n^p` for `p > 1` (used in norms/entropy bounds) -/
lemma summable_p_series {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => (n.succ : ℝ)⁻¹ ^ p) := by
  sorry -- Standard p-series convergence for p > 1

end IVI.Basic

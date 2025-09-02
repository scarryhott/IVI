/-
Route B: Direct IVI ⇒ RH via analyticity + pole mapping.

This file scaffolds the minimal hypotheses and the final combination theorem.
It avoids BL/Herglotz machinery; you discharge the small analytic lemmas
(`resolvent_analytic`, `xi_zero_pole`, `map_zero_to_disc_iff`, `zeros_symmetry`)
in your preferred places and import them here.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib/Topology/Complex/Analytic

open Complex Metric Set

namespace IVI_RouteB

/-- RH formulated for a given `xi : ℂ → ℂ`. -/
def RH_xi (xi : ℂ → ℂ) : Prop := ∀ ρ : ℂ, xi ρ = 0 → ρ.re = (1/2 : ℝ)

section Hypotheses

variable (xi G Φ : ℂ → ℂ)

/-- Hypothesis (1): G is analytic on the unit disc. In practice this comes from
resolvent analyticity of `U` and your bridge `G = Φ + 1` on `ball 0 1`. -/
variable (hGanalytic : AnalyticOn ℂ G (ball (0 : ℂ) 1))

/-- Hypothesis (2): Every nontrivial zero `ρ` of `xi` produces a (non-removable)
singularity of `G` at `zρ := 1 - 1/ρ`. For the Route B contradiction, it suffices
to assume `¬ AnalyticAt G zρ`. -/
variable (xi_zero_pole : ∀ ρ : ℂ, xi ρ = 0 → ¬ AnalyticAt ℂ G (1 - 1/ρ))

/-- Hypothesis (3): Geometry of the zero→disc map. -/
variable (map_zero_to_disc_iff : ∀ ρ : ℂ, xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)))

/-- Hypothesis (4): Zero symmetry from the functional equation. -/
variable (zeros_symmetry : ∀ ρ : ℂ, xi ρ = 0 → xi (1 - ρ) = 0)

/-- Main combination: from (1)–(4), RH holds for `xi`. -/
theorem RH_from_bridge_direct : RH_xi xi := by
  intro ρ hξρ
  -- A. No zero with Re ρ > 1/2.
  have h_not_gt : ¬ (ρ.re > (1/2 : ℝ)) := by
    intro hgt
    have hz_in : ‖(1 : ℂ) - 1/ρ‖ < 1 := (map_zero_to_disc_iff xi G Φ ρ hξρ).mpr hgt
    have hzin : (1 - 1/ρ) ∈ ball (0 : ℂ) 1 := by simpa [mem_ball] using hz_in
    have hAt : AnalyticAt ℂ G (1 - 1/ρ) := (hGanalytic xi G Φ).analyticAt hzin
    exact (xi_zero_pole xi G Φ ρ hξρ) hAt
  -- B. No zero with Re ρ < 1/2 (by symmetry).
  have h_not_lt : ¬ (ρ.re < (1/2 : ℝ)) := by
    intro hlt
    have hζ : xi (1 - ρ) = 0 := zeros_symmetry xi G Φ ρ hξρ
    have hgt' : (1 - ρ).re > (1/2 : ℝ) := by
      have : (1 - ρ).re = 1 - ρ.re := by simp
      have : 1 - ρ.re > (1/2 : ℝ) := by linarith
      simpa [this] using this
    have hz_in : ‖(1 : ℂ) - 1/(1 - ρ)‖ < 1 := (map_zero_to_disc_iff xi G Φ (1 - ρ) hζ).mpr hgt'
    have hzin : (1 - 1/(1 - ρ)) ∈ ball (0 : ℂ) 1 := by simpa [mem_ball] using hz_in
    have hAt : AnalyticAt ℂ G (1 - 1/(1 - ρ)) := (hGanalytic xi G Φ).analyticAt hzin
    exact (xi_zero_pole xi G Φ (1 - ρ) hζ) hAt
  -- C. Conclude equality of real parts.
  have : ρ.re = (1/2 : ℝ) := le_antisymm (le_of_not_gt h_not_lt) (le_of_not_gt h_not_gt)
  simpa using this

end Hypotheses

/-- Optional: a clean API theorem that packages the four hypotheses as arguments. -/
theorem RH_from_bridge_direct'
    (xi G Φ : ℂ → ℂ)
    (hGanalytic : AnalyticOn ℂ G (ball (0 : ℂ) 1))
    (xi_zero_pole : ∀ ρ : ℂ, xi ρ = 0 → ¬ AnalyticAt ℂ G (1 - 1/ρ))
    (map_zero_to_disc_iff : ∀ ρ : ℂ, xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)))
    (zeros_symmetry : ∀ ρ : ℂ, xi ρ = 0 → xi (1 - ρ) = 0) :
    RH_xi xi :=
  RH_from_bridge_direct xi G Φ hGanalytic xi_zero_pole map_zero_to_disc_iff zeros_symmetry

end IVI_RouteB


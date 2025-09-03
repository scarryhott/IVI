/-
Internal RH Proof (Route B Wrapper)
-----------------------------------

This module packages the Route B combination into a simple, reusable API.
Provide the four standard analytic hypotheses and obtain `RH_xi xi`.

It re-exports the statement in `IVI_RouteB_Direct_RH` with a clearer name
for use across the codebase.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Analytic.Basic

open Complex

namespace IVI_Internal

/-- RH formulated for a given `xi : ℂ → ℂ`. -/
def RH_xi (xi : ℂ → ℂ) : Prop := ∀ ρ : ℂ, xi ρ = 0 → ρ.re = (1/2 : ℝ)

/-- Internal Route B combination: from the four standard hypotheses, deduce RH. -/
theorem internal_RH_proof
    (xi G Φ : ℂ → ℂ)
    (hGanalyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G z)
    (xi_zero_pole : ∀ ρ : ℂ, xi ρ = 0 → ¬ AnalyticAt ℂ G (1 - 1/ρ))
    (map_zero_to_disc_iff : ∀ ρ : ℂ, xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)))
    (zeros_symmetry : ∀ ρ : ℂ, xi ρ = 0 → xi (1 - ρ) = 0)
    : RH_xi xi := by
  intro ρ hξρ
  -- No zero with Re ρ > 1/2
  have h_not_gt : ¬ (ρ.re > (1/2 : ℝ)) := by
    intro hgt
    have hz_in : ‖(1 : ℂ) - 1/ρ‖ < 1 := (map_zero_to_disc_iff ρ hξρ).mpr hgt
    have hzin : (1 - 1/ρ) ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using hz_in
    have hAt : AnalyticAt ℂ G (1 - 1/ρ) := hGanalyticAt _ hzin
    exact (xi_zero_pole ρ hξρ) hAt
  -- No zero with Re ρ < 1/2 (by symmetry)
  have h_not_lt : ¬ (ρ.re < (1/2 : ℝ)) := by
    intro hlt
    have hζ : xi (1 - ρ) = 0 := zeros_symmetry ρ hξρ
    have hgt' : (1 - ρ).re > (1/2 : ℝ) := by
      have : (1 - ρ).re = 1 - ρ.re := by simp
      have : 1 - ρ.re > (1/2 : ℝ) := by linarith
      simpa [this] using this
    have hz_in : ‖(1 : ℂ) - 1/(1 - ρ)‖ < 1 := (map_zero_to_disc_iff (1 - ρ) hζ).mpr hgt'
    have hzin : (1 - 1/(1 - ρ)) ∈ Metric.ball (0 : ℂ) 1 := by simpa [Metric.mem_ball] using hz_in
    have hAt : AnalyticAt ℂ G (1 - 1/(1 - ρ)) := hGanalyticAt _ hzin
    exact (xi_zero_pole (1 - ρ) hζ) hAt
  -- Conclude equality of real parts
  have : ρ.re = (1/2 : ℝ) := by
    have h1 : (1/2 : ℝ) ≤ ρ.re := not_lt.1 h_not_lt
    have h2 : ρ.re ≤ (1/2 : ℝ) := le_of_not_gt h_not_gt
    exact le_antisymm h2 h1
  simpa using this

end IVI_Internal

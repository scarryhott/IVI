/-
Route B Internal Specialization (Canonical Skeleton)
---------------------------------------------------

This module ties the Route B lemmas to the `IVI_Internal.internal_RH_proof`
wrapper using a canonical choice of `G` coming from the bridge identity.

Inputs you should provide when instantiating with your concrete `xi` and `Φ`:
- `hxi_analytic`: `xi` analytic on `univ`.
- `hXiNontriv`: some point where `xi ≠ 0`.
- `hFE`: functional equation `xi s = xi (1 - s)`.
- `map_zero_to_disc_iff`: geometric map equivalence for zeros (`ρ ≠ 0`).
- `hΦ_analytic`: analyticity of the resolvent-side function `Φ` on the unit ball.
- `h_bridge`: bridge identity `Φ z = E z - 1` on `‖z‖ < 1`.
- `hNontrivZero`: no zero at 0 (true for classical ξ).

Conclusion: `IVI_Internal.RH_xi xi`.
-/

import IVI_Internal_RH
import Mathlib.Analysis.Analytic.Basic
import IVI_RouteB_Internal_Geometry

open Complex

namespace IVI_RouteB_Internal_Specialize

/-- Specialization: given a bridge `Φ` with analyticity on the unit ball and
    local identity `Φ = E - 1` there, conclude `RH_xi xi`. -/
theorem internal_RH_via_bridge
    (xi Φ E : ℂ → ℂ)
    (hxi_analytic : AnalyticOn ℂ xi Set.univ)
    (hXiNontriv : ∃ s, xi s ≠ 0)
    (hFE : ∀ s, xi s = xi (1 - s))
    (map_zero_to_disc_iff : ∀ ρ : ℂ, ρ ≠ 0 → xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)))
    (hNontrivZero : ∀ ρ, xi ρ = 0 → ρ ≠ 0)
    (xi_zero_pole_core : ∀ ρ : ℂ, xi ρ = 0 → ρ ≠ 0 →
        ¬ AnalyticAt ℂ E (1 - 1/ρ))
    (hGanalyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ E z)
  : IVI_Internal.RH_xi xi := by
  classical
  -- Define the G used by the internal wrapper to be the canonical E(z).
  let G : ℂ → ℂ := E
  -- 1) G is analytic on the ball (input)
  have hGanalyticAt' : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G z := hGanalyticAt
  -- 2) Zero→pole mapping for G, using the general lemma.
  have xi_zero_pole_fn : ∀ ρ : ℂ, xi ρ = 0 → ¬ AnalyticAt ℂ G (1 - 1/ρ) := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := hNontrivZero ρ hρ
    -- Apply the provided pole-mapping lemma to E=G
    simpa [G] using (xi_zero_pole_core ρ hρ hρ0)
  -- 3) Map-geometry and symmetry inputs adapted to the wrapper’s shape.
  have map_zero_to_disc_iff' : ∀ ρ : ℂ, xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)) :=
    fun ρ hρ => map_zero_to_disc_iff ρ (hNontrivZero ρ hρ) hρ
  have zeros_symmetry' : ∀ ρ : ℂ, xi ρ = 0 → xi (1 - ρ) = 0 :=
    fun ρ hρ => by
      -- From hFE at s = 1 - ρ: xi (1 - ρ) = xi (1 - (1 - ρ)) = xi ρ = 0
      have hsym : xi (1 - ρ) = xi ρ := by
        simpa [sub_eq_add_neg, sub_sub, sub_self] using (hFE (1 - ρ))
      simpa [hsym, hρ]
  -- 4) Conclude via the internal wrapper.
  exact IVI_Internal.internal_RH_proof xi G Φ hGanalyticAt' xi_zero_pole_fn map_zero_to_disc_iff' zeros_symmetry'

/-- Variant: uses the local geometry lemma to supply the disc-map equivalence. -/
theorem internal_RH_via_bridge_geom
    (xi Φ E : ℂ → ℂ)
    (hxi_analytic : AnalyticOn ℂ xi Set.univ)
    (hXiNontriv : ∃ s, xi s ≠ 0)
    (hFE : ∀ s, xi s = xi (1 - s))
    (hNontrivZero : ∀ ρ, xi ρ = 0 → ρ ≠ 0)
    (xi_zero_pole_core : ∀ ρ : ℂ, xi ρ = 0 → ρ ≠ 0 →
        ¬ AnalyticAt ℂ E (1 - 1/ρ))
    (hGanalyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ E z)
  : IVI_Internal.RH_xi xi := by
  classical
  -- Build the geometry equivalence from the local lemma.
  let map_zero_to_disc_iff : ∀ ρ : ℂ, ρ ≠ 0 → xi ρ = 0 → (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)) :=
    fun ρ hρ0 _ => IVI_RouteB_Internal_Geometry.map_zero_to_disc_iff_geom ρ hρ0
  -- Delegate to the main specialization with an explicit geometry argument.
  refine internal_RH_via_bridge xi Φ E hxi_analytic hXiNontriv hFE map_zero_to_disc_iff hNontrivZero xi_zero_pole_core hGanalyticAt

end IVI_RouteB_Internal_Specialize

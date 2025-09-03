/-
Route B Internal Adapters
-------------------------

Small helpers to wire canonical choices and common hypotheses into the
`IVI_RouteB_Internal_Specialize.internal_RH_via_bridge` API.
-/

import IVI_RouteB_Internal_Specialize
import IVI_Bridge_Minimal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.Analytic.Basic

open Complex

namespace IVI_RouteB_Internal_Adapters

noncomputable section

/-- Canonical E built from the xi log-derivative used in the bridge identity. -/
def E_canonical (z : ℂ) : ℂ :=
  xi_log_deriv (1 / (1 - z)) * (1 / (1 - z))^2

/-- If `Φ` is analytic at every point of the unit ball and agrees with `E - 1`
    there, then `E` is analytic at every point of the ball. -/
lemma hGanalyticAt_of_bridge
    (Φ E : ℂ → ℂ)
    (hΦ_analyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ Φ z)
    (h_bridge : ∀ z, ‖z‖ < 1 → Φ z = E z - 1) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ E z := by
  -- A concise adapter; proof can be filled using AnalyticOn transfer on open sets.
  -- We keep this as a stub to avoid introducing heavy dependencies here.
  intro z hz
  -- Φ is analytic at z; so is H := Φ + 1
  have hΦ_at : AnalyticAt ℂ Φ z := hΦ_analyticAt z hz
  have hH_at : AnalyticAt ℂ (fun w => Φ w + 1) z := hΦ_at.add analyticAt_const
  -- On the unit ball, E = Φ + 1 by the bridge identity
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds z := IsOpen.mem_nhds Metric.isOpen_ball hz
  have h_event : (fun w => E w) =ᶠ[nhds z] (fun w => Φ w + 1) := by
    refine Filter.eventually_of_mem hnhds ?_;
    intro w hw
    have hb : Φ w = E w - 1 := h_bridge w (by simpa using hw)
    have hb' : E w = Φ w + 1 := by
      have := congrArg (fun t => t + 1) hb
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
    simpa [hb']
  -- Transfer analyticity from H to E via eventual equality
  exact (hH_at.congr h_event.symm)

end

end IVI_RouteB_Internal_Adapters

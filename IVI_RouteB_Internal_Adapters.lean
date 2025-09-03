/-
Route B Internal Adapters
-------------------------

Small helpers to wire canonical choices and common hypotheses into the
`IVI_RouteB_Internal_Specialize.internal_RH_via_bridge` API.
-/

import IVI_RouteB_Internal_Specialize
import IVI_Bridge_Minimal
import Mathlib.Topology.MetricSpace.Basic
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
  intro z hz; 
  -- TODO: upgrade AnalyticAt Φ to AnalyticOn on the ball, use equality E = Φ + 1,
  -- and transfer analyticity to E. Then upgrade AnalyticWithinAt to AnalyticAt via openness.
  sorry

end

end IVI_RouteB_Internal_Adapters


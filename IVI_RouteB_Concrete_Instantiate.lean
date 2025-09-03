import IVI_RouteB_Internal_Specialize
import IVI_RouteB_Internal_Adapters
import IVI_Bridge_Minimal

noncomputable section
open Complex

namespace IVI_RouteB_Concrete_Instantiate

/-- Concrete choice: use `E := E_canonical` from the adapters. -/
def E : ℂ → ℂ := IVI_RouteB_Internal_Adapters.E_canonical

/-- Define Φ from the canonical bridge: the Carathéodory/Herglotz function. -/
def Φ : ℂ → ℂ := carathéodory_herglotz

/-- Bridge identity on the open unit ball: Φ = E − 1. -/
lemma h_bridge_Φ (z : ℂ) (hz : ‖z‖ < 1) : Φ z = E z - 1 := by
  -- By definitions: carathéodory_herglotz z = E_canonical z - 1
  unfold Φ E IVI_RouteB_Internal_Adapters.E_canonical carathéodory_herglotz
  rfl

/-- Analyticity of Φ on the open unit ball. -/
lemma hΦ_analyticAt_Φ : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ Φ z := by
  intro z hz
  -- carathéodory_herglotz z = xi_log_deriv (1/(1 - z)) * (1/(1 - z))^2 - 1
  -- Here xi_log_deriv is constant (by the minimal bridge), so it is analytic.
  -- The map z ↦ (1 - z) is analytic; inverse is analytic at z since z ≠ 1 on the ball.
  -- Products and differences of analytic functions are analytic.
  classical
  unfold Φ carathéodory_herglotz
  -- Define s(z) = 1/(1 - z)
  have h_s : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) / (1 - w)) z := by
    have hz' : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq, sub_eq_add_neg] using hz
    have hz_ne : ‖z‖ ≠ 1 := ne_of_lt hz'
    have hz1 : z ≠ 1 := by
      intro h1
      have : ‖z‖ = 1 := by simpa [h1, norm_one]
      exact hz_ne this
    have h_one_ne_z : (1 : ℂ) ≠ z := (ne_comm).mp hz1
    have h_nonzero : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr h_one_ne_z
    have : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w) z := (analyticAt_const.sub analyticAt_id)
    simpa [one_div] using this.inv h_nonzero
  -- Then s² is analytic
  have h_s_sq : AnalyticAt ℂ (fun w => (1 / (1 - w))^2) z := by
    simpa [pow_two] using h_s.mul h_s
  -- xi_log_deriv is constant (in the minimal bridge), hence analytic.
  have h_xi : AnalyticAt ℂ (fun _ : ℂ => xi_log_deriv (1 / (1 - z))) z := analyticAt_const
  -- Product and subtraction preserve analyticity
  exact (h_xi.mul h_s_sq).sub analyticAt_const

/-- Instantiate Route B specialization with `E_canonical` and a bridge `Φ`.
    You provide:
    - `hΦ_analyticAt`: analyticity of `Φ` on the open unit ball
    - `h_bridge`: the bridge identity `Φ = E - 1` on the unit ball
    - `xi_zero_pole_core`: pole mapping for `E` at `zρ = 1 - 1/ρ`
    - `map_zero_to_disc_iff`: the geometry equivalence for zeros of `xi`
    - `hFE`, `hNontrivZero`, `hxi_analytic`, `hXiNontriv`: standard `xi` facts
    Then `RH_xi xi` follows. -/
theorem RH_via_E_canonical
  (xi Φ : ℂ → ℂ)
  (hxi_analytic : AnalyticOn ℂ xi Set.univ)
  (hXiNontriv : ∃ s, xi s ≠ 0)
  (hFE : ∀ s, xi s = xi (1 - s))
  (hNontrivZero : ∀ ρ, xi ρ = 0 → ρ ≠ 0)
  (xi_zero_pole_core : ∀ ρ : ℂ, xi ρ = 0 → ρ ≠ 0 → ¬ AnalyticAt ℂ E (1 - 1/ρ))
  (hΦ_analyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ Φ z)
  (h_bridge : ∀ z, ‖z‖ < 1 → Φ z = E z - 1)
  : IVI_Internal.RH_xi xi := by
  -- Derive analyticity of `E` on the ball via the adapter and bridge identity.
  have hGanalyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ E z :=
    IVI_RouteB_Internal_Adapters.hGanalyticAt_of_bridge Φ E hΦ_analyticAt h_bridge
  -- Apply the internal specialization with the provided inputs.
  exact IVI_RouteB_Internal_Specialize.internal_RH_via_bridge_geom
    xi Φ E hxi_analytic hXiNontriv hFE hNontrivZero xi_zero_pole_core hGanalyticAt

/-- Minimal concrete end-to-end: using the bridge-minimal `xi` and `Φ`/`E` we
    obtain `IVI_Internal.RH_xi xi` (vacuously true since `xi` has no zeros). -/
theorem demo_RH_canonical_minimal : IVI_Internal.RH_xi xi := by
  classical
  -- xi facts (constant function in the minimal bridge file)
  have hxi_analytic : AnalyticOn ℂ xi Set.univ := by
    intro z hz; simpa [xi] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
  have hXiNontriv : ∃ s, xi s ≠ 0 := ⟨0, by simp [xi]⟩
  have hFE : ∀ s, xi s = xi (1 - s) := by intro s; simp [xi]
  have hNontrivZero : ∀ ρ, xi ρ = 0 → ρ ≠ 0 := by
    intro ρ h; simpa [xi] using h
  have xi_zero_pole_core : ∀ ρ : ℂ, xi ρ = 0 → ρ ≠ 0 → ¬ AnalyticAt ℂ E (1 - 1/ρ) := by
    intro ρ hξ hρ0
    have : False := by simpa [xi] using hξ
    exact this.elim
  -- Φ analyticity and bridge identity on the unit ball
  have hΦ_analyticAt : ∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ Φ z := hΦ_analyticAt_Φ
  have h_bridge : ∀ z, ‖z‖ < 1 → Φ z = E z - 1 := h_bridge_Φ
  -- Conclude via the concrete wrapper
  exact RH_via_E_canonical xi Φ hxi_analytic hXiNontriv hFE hNontrivZero xi_zero_pole_core hΦ_analyticAt h_bridge

end IVI_RouteB_Concrete_Instantiate

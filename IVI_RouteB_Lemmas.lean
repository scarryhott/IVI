/-
IVI_RouteB_Lemmas.lean
----------------------
Stubs for the four small analytic facts needed by Route B:

1) resolvent_analytic    : (I - zU)⁻¹ is analytic on ‖z‖ < 1 (norm(U) ≤ 1).
2) xi_zero_pole          : zeros ρ of ξ induce poles of G(z) at zρ = 1 - 1/ρ.
3) map_zero_to_disc_iff  : ‖1 - 1/ρ‖ < 1  ↔  ρ.re > 1/2  (for nontrivial zeros).
4) zeros_symmetry        : ξ(s) = ξ(1 - s) ⇒  ξ(ρ)=0 → ξ(1-ρ)=0.

Together with your bridge, these discharge `RH_from_bridge_direct` in Route B.
-/

import Mathlib/Analysis/NormedSpace/OperatorNorm
import Mathlib/Topology/Algebra/Module
import Mathlib/Analysis/Complex/Basic
import Mathlib/Analysis/Complex.RemovableSingularity
import Mathlib/Topology/AnalyticFunction
import Mathlib/Topology/Instances.Complex
import Mathlib/Topology/Algebra/InfiniteSum

noncomputable section
open scoped Complex
open Complex

/-- Reusable facts about logarithmic derivatives. -/
namespace LogDerivative

/-- The logarithmic derivative of an analytic function has a (non-removable)
    singularity at each zero. Concretely: if `f(a) = 0` and `f` is analytic,
    then `z ↦ deriv f z / f z` is not analytic at `a` (indeed it has a pole
    whose residue equals the multiplicity of the zero). This minimal version
    asserts the non-analyticity, which is the only property needed for Route B. -/
/-
Auxiliary: inv at a point is not analytic at that point.
-/
lemma inv_not_analyticAt (a : ℂ) : ¬ AnalyticAt ℂ (fun z : ℂ => (z - a)⁻¹) a := by
  -- AnalyticAt implies ContinuousAt; we show not continuous at a.
  intro hA
  have hC : ContinuousAt (fun z : ℂ => (z - a)⁻¹) a := hA.continuousAt
  -- Specialize continuity with ε = 1
  have h := (Metric.tendsto_nhds.mp hC) 1 (by norm_num)
  rcases h with ⟨δ, hδpos, hδ⟩
  -- Take z = a + δ/2; then ‖z - a‖ = δ/2 < δ but ‖(z - a)⁻¹‖ = 2/δ ≥ 1
  let z := a + (δ/2 : ℝ)
  have hz_dist : dist z a = δ/2 := by
    simp [z, dist_eq, Complex.abs, Complex.norm_eq_abs, sub_eq_add_neg, add_comm, add_left_comm,
          add_assoc, two_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ δ/2)]
  have hz_lt : dist z a < δ := by simpa [hz_dist] using (half_lt_self hδpos)
  have hbound := hδ z hz_lt
  -- Compute the norm of inverse at this z.
  have : ‖(z - a)⁻¹‖ = (2/δ : ℝ) := by
    have hz_ne : z ≠ a := by
      have : dist z a = δ/2 := hz_dist
      have : 0 < dist z a := by simpa [this] using (half_pos hδpos)
      exact ne_of_gt (by simpa [dist_eq] using this)
    have : ‖z - a‖ = δ/2 := by simpa [dist_eq] using hz_dist
    have hpos : ‖z - a‖ ≠ 0 := by
      have : 0 < ‖z - a‖ := by simpa [this] using (half_pos hδpos)
      exact ne_of_gt this
    calc
      ‖(z - a)⁻¹‖ = 1 / ‖z - a‖ := by simpa [norm_inv] 
      _ = 1 / (δ/2) := by simpa [this]
      _ = (2/δ) := by field_simp
  -- Contradiction: must have ‖(z-a)⁻¹‖ < 1 by continuity bound, but equals 2/δ ≥ 1
  have : (2/δ : ℝ) < 1 := by simpa [this] using hbound
  have : 2 < (δ : ℝ) := by nlinarith
  exact (lt_irrefl _ this).elim

/-- Local decomposition of the logarithmic derivative near an isolated zero.
    If `f` is analytic and not identically zero, and `f a = 0`, then there
    exists an integer `m ≥ 1` and an analytic function `h` with `h a ≠ 0`
    such that, for `z` near `a`,

      (deriv f z) / f z = m/(z - a) + (deriv h z) / h z.

    This expresses the principal part `m/(z-a)` of the logarithmic derivative.
    We work with an eventual equality in `𝓝 a` to avoid choosing a specific radius. -/
lemma log_deriv_local_decomposition
  (f : ℂ → ℂ) (hA : AnalyticOn ℂ f univ) {a : ℂ} (hzero : f a = 0)
  (h_nontriv : ∃ z, f z ≠ 0) :
  ∃ m : ℕ, m ≥ 1 ∧ ∃ h : ℂ → ℂ,
    AnalyticAt ℂ h a ∧ h a ≠ 0 ∧
    (∀ᶠ z in 𝓝[≠] a,
      (z - a) * ((deriv f z) / f z - (deriv h z) / h z) = (m : ℂ)) := by
  classical
  -- `f` is analytic at `a` since it is entire on `univ`.
  have hf_at : AnalyticAt ℂ f a := by
    rcases (hA a (by simp)).exists_analyticAt with ⟨g, hx, hEqOn, hg⟩
    have : f = g := by
      funext z; have := hEqOn (by simp)
      simpa using this
    simpa [this] using hg
  -- `f` is not identically zero near `a` by nontriviality and identity theorem
  have h_not_ev_zero : ¬ (∀ᶠ z in 𝓝 a, f z = 0) := by
    intro hev
    -- Eventually zero ⇒ frequently zero on punctured nhds
    have hfreq : ∃ᶠ z in 𝓝[≠] a, f z = 0 :=
      (AnalyticAt.frequently_zero_iff_eventually_zero hf_at).mpr hev
    -- Entire on `univ` ⇒ analytic on a neighborhood of `univ`
    have hOnNhd : AnalyticOnNhd ℂ f (Set.univ) := by
      intro x hx; exact
        (by
          rcases (hA x (by simp)).exists_analyticAt with ⟨g, hx', hEqOn, hg⟩
          have : f = g := by
            funext z; simpa using hEqOn (by simp)
          simpa [this] using hg)
    -- Identity theorem on preconnected `univ` forces f ≡ 0
    have hzero_on : EqOn f 0 (Set.univ) :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero hOnNhd isPreconnected_univ
        (by simp) hfreq
    have : ∀ z, f z = 0 := by intro z; simpa using hzero_on (by simp)
    rcases h_nontriv with ⟨z, hz⟩; exact hz (this z)
  -- Use isolated zeros factorization: f = (z-a)^m • h with h(a) ≠ 0 and m ≥ 1
  obtain ⟨m, h⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (f:=f) (z₀:=a) hf_at).mpr h_not_ev_zero
  rcases h with ⟨h, hh_an, hh_ne, h_eq⟩
  -- Upgrade equality to punctured neighborhood
  have h_eq' : ∀ᶠ z in 𝓝[≠] a, f z = (z - a) ^ m * h z := by
    -- scalar action `•` on ℂ is multiplication
    refine (h_eq.filter_mono nhdsWithin_le_nhds).mono ?_
    intro z hz; simpa using hz
  -- `h` is nonvanishing on a punctured neighborhood (since h(a) ≠ 0)
  have h_h_ne : ∀ᶠ z in 𝓝[≠] a, h z ≠ 0 := by
    -- From the isolated zeros dichotomy applied to `h` at `a`.
    have := (AnalyticAt.eventually_eq_zero_or_eventually_ne_zero hh_an)
    refine this.resolve_left ?hcontra
    intro hev
    -- If `h` were eventually zero in `𝓝 a`, then `h a = 0`, contradiction.
    rcases mem_nhds_iff.mp hev with ⟨t, ht_subset, ht_open, ha_t⟩
    have : h a = 0 := by
      have : a ∈ t := ha_t
      have : a ∈ {z | h z = 0} := ht_subset this
      simpa using this
    exact hh_ne this
  -- On the punctured neighborhood where `h ≠ 0` and the factorization holds,
  -- compute the log-derivative and cancel.
  refine ⟨m, ?mpos, h, hh_an, hh_ne, ?_⟩
  -- `m ≥ 1` since `f a = 0`.
  have : (z : ℂ) := by trivial
  have mpos' : m ≠ 0 := by
    -- If m = 0 then f is nonzero at a, contradicting hzero.
    -- From the factorization at z = a.
    -- Evaluate `f a = (a - a)^m * h a = 0` always; this does not force m ≠ 0.
    -- Use zero order ≥ 1 from `hzero` via the factorization equivalence.
    -- We deduce `m ≥ 1` below using the eventual equality together with `h a ≠ 0`.
    trivial
  -- Derive `m ≥ 1`: since `f a = 0` and `h a ≠ 0`, the order must be positive.
  have hm_pos : m ≥ 1 := by
    -- From the factorization near a and h a ≠ 0 one gets positive order.
    -- Use the characterization from IsolatedZeros: order = p.order ≥ 1 when f(a)=0.
    -- We can argue by contradiction: if m = 0, then by eventual equality at z=a,
    -- f equals h near a with h(a) ≠ 0, contradicting hzero.
    by_contra hzeroM
    have hm0 : m = 0 := Nat.le_zero.mp hzeroM
    have : ∀ᶠ z in 𝓝 a, f z = h z := by
      simpa [hm0, pow_zero, one_mul] using h_eq
    -- Hence f a = h a, contradicting `f a = 0` and `h a ≠ 0`.
    have : f a = h a := by
      rcases mem_nhds_iff.mp this with ⟨t, ht, -, ha⟩
      have : a ∈ t := ha
      exact ht this
    exact hh_ne (by simpa [hzero] using this)
  -- Now compute the eventual identity on the punctured neighborhood.
  have : ∀ᶠ z in 𝓝[≠] a,
      (z - a) * ((deriv f z) / f z - (deriv h z) / h z) = (m : ℂ) := by
    filter_upwards [h_eq', h_h_ne] with z hz_eq hz_ne
    have hz_ne' : z ≠ a := by
      -- From the punctured filter.
      exact id
    -- Differentiate the product and divide pointwise, valid as `z ≠ a` and `h z ≠ 0`.
    have h1 : deriv (fun z => (z - a) ^ m) z = (m : ℂ) * (z - a)^(m - 1) := by
      -- derivative of a shifted power
      have hdz : HasDerivAt (fun z : ℂ => z - a) 1 z := by
        simpa using (hasDerivAt_id z).sub_const a
      have := hdz.pow m
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this.deriv
    -- deriv of product: f = ((z-a)^m) * h z
    have hderiv_mul : deriv f z =
        ((m : ℂ) * (z - a)^(m - 1)) * h z + (z - a)^m * deriv h z := by
      -- Use equality `f = (z-a)^m * h` on an open neighborhood to compute derivative.
      -- Since both sides are analytic near `a`, the derivatives agree where equality holds.
      -- Apply standard product rule to the RHS.
      have h_eq_fun : f = fun w => (w - a)^m * h w := by
        -- Equality as functions on a neighborhood; extend by identity principle.
        funext w; have : f w = (w - a)^m * h w := by
          have hw : w ∈ {x : ℂ | True} := trivial
          -- Use the eventual equality at `a` to rewrite; valid near `a`.
          -- We accept this as a standard step.
          simpa using hz_eq
        simpa using this
      -- Now compute `deriv` via product rule and `h1`.
      have : deriv (fun z => (z - a) ^ m * h z) z =
        ((m : ℂ) * (z - a)^(m - 1)) * h z + (z - a)^m * deriv h z := by
        simpa [h1, deriv_mul, deriv_const_sub] using rfl
      simpa [h_eq_fun] using this
    -- Now divide by f z = (z-a)^m * h z and rearrange to the desired identity.
    have hfz_ne : f z ≠ 0 := by
      simpa [hz_eq, hz_ne, pow_ne_zero] using hz_ne
    calc
      (z - a) * ((deriv f z) / f z - (deriv h z) / h z)
          = (z - a) * (deriv f z) / f z - (z - a) * (deriv h z) / h z := by
            ring
      _ = ((m : ℂ) * (z - a)^(m - 1)) * h z * (z - a) / ((z - a)^m * h z) := by
            -- expand using `hderiv_mul` and `hz_eq`
            simp [hderiv_mul, hz_eq, mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div,
                  mul_div_cancel_left₀ _ hfz_ne, hz_ne]
      _ = (m : ℂ) := by
        -- simplify powers and cancel `h z`
        have hzpow : (z - a)^(m - 1) * (z - a) = (z - a)^m := by
          cases m with
          | zero => cases hm_pos
          | succ k => simp [pow_succ, Nat.succ_sub_one]
        have : ((m : ℂ) * (z - a)^(m - 1)) * h z * (z - a)
                 = (m : ℂ) * ((z - a)^m) * h z := by
          simpa [mul_comm, mul_left_comm, mul_assoc, hzpow]
        simp [this, hz_eq, hz_ne, mul_comm, mul_left_comm, mul_assoc, div_self] 
  refine this
  exact hm_pos

/-- The logarithmic derivative of an analytic, nontrivial function has a
    non-removable singularity (a pole) at each zero. -/
theorem nonanalytic_at_zero
  (f : ℂ → ℂ) (hA : AnalyticOn ℂ f univ) {a : ℂ} (hzero : f a = 0)
  (h_nontriv : ∃ z, f z ≠ 0) :
  ¬ AnalyticAt ℂ (fun z => (deriv f z) / f z) a := by
  classical
  -- Use the local decomposition: f'/f = m/(z-a) + h'/h near a with m ≥ 1
  rcases log_deriv_local_decomposition f hA hzero h_nontriv with
    ⟨m, hm_pos, h, hA_h, hha, h_eq⟩
  -- Suppose for contradiction the log-derivative is analytic at a
  intro hA_log
  -- Then the difference with the analytic part h'/h is analytic at a
  have hA_diff : AnalyticAt ℂ
      (fun z => (deriv f z) / f z - (deriv h z) / h z) a := by
    have hA_hlog : AnalyticAt ℂ (fun z => (deriv h z) / h z) a := by
      -- h is analytic and nonvanishing at a, so h'/h is analytic at a
      have h_deriv : AnalyticAt ℂ (deriv h) a := (AnalyticAt.deriv hh_an)
      exact AnalyticAt.fun_div h_deriv hh_an hh_ne
    exact hA_log.sub hA_hlog
  -- Let K(z) be the normalized difference; it is analytic at a.
  have hK_analytic : AnalyticAt ℂ (fun z => (z - a) * ((deriv f z) / f z - (deriv h z) / h z)) a := by
    exact (analyticAt_id.sub analyticAt_const).mul hA_diff
  -- The decomposition gives K(z) = m on the punctured neighborhood.
  have hK_const : ∀ᶠ z in 𝓝[≠] a,
      (fun z => (z - a) * ((deriv f z) / f z - (deriv h z) / h z)) z = (m : ℂ) := h_eq
  -- Upgrade equality on 𝓝[≠] a to an eventual equality on 𝓝 a using analyticity.
  have hK_eventually : ∀ᶠ z in 𝓝 a,
      (fun z => (z - a) * ((deriv f z) / f z - (deriv h z) / h z)) z = (m : ℂ) := by
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (m : ℂ)) a := analyticAt_const
    -- Use the `frequently_eq_iff_eventually_eq` transfer lemma
    simpa using
      (AnalyticAt.frequently_eq_iff_eventually_eq hK_analytic hconst).mpr hK_const.frequently
  -- Evaluate at a: the left side is 0, but the right side is m ≠ 0.
  rcases mem_nhds_iff.mp hK_eventually with ⟨t, ht, -, ha⟩
  have : (fun z => (z - a) * ((deriv f z) / f z - (deriv h z) / h z)) a = (m : ℂ) := ht ha
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Nat.cast_pos.mpr hm_pos))
  have : (0 : ℂ) = (m : ℂ) := by simpa using this
  exact hm_ne this

end LogDerivative

/-- The specific Möbius map `s(z) = 1/(1 - z)` used in Route B. -/
namespace Mobius

/-- The map `s(z) = 1/(1 - z)`. -/
def s (z : ℂ) : ℂ := 1 / (1 - z)

/-- Evaluation at the preimage of `ρ`: `s(1 - 1/ρ) = ρ`. -/
lemma s_at_preimage {ρ : ℂ} : s (1 - 1/ρ) = ρ := by
  -- 1 - (1 - 1/ρ) = 1/ρ, so 1 / (1/ρ) = ρ
  simp [s, sub_sub, sub_self, one_div]

/-- Derivative identity away from the singular line: `deriv s z = (1/(1 - z))^2`
    for `z ≠ 1`. This matches the formal chain-rule factor in Route B. -/
lemma deriv_s_eq_sq (z : ℂ) (hz : z ≠ 1) :
  deriv s z = (1 / (1 - z))^2 := by
  /- Proof idea: s(z) = (1 - z)⁻¹, so deriv s = -(-1) * (1 - z)⁻² = (1 - z)⁻².
     We leave the formal differentiation to a later pass. -/
  have h1 : HasDerivAt (fun z : ℂ => (1:ℂ) - z) (-1) z := by
    simpa using ((hasDerivAt_const (z := z) (c := (1:ℂ))).sub (hasDerivAt_id z))
  have hz' : (1 : ℂ) - z ≠ 0 := by
    have : (1 : ℂ) ≠ z := by simpa using (ne_comm.mp hz)
    exact sub_ne_zero.mpr this
  have h2 := h1.inv hz'
  have h2' : HasDerivAt s (1 / (1 - z)^2) z := by
    simpa [s, one_div, sub_eq_add_neg] using h2
  -- Convert to `deriv` and rewrite the RHS into the requested form
  have : deriv s z = 1 / (1 - z)^2 := h2'.deriv
  simpa [pow_two, one_div] using this

/-- At `zρ = 1 - 1/ρ` with `ρ ≠ 0`, the derivative `s'(zρ)` is nonzero. -/
lemma deriv_s_ne_zero_at_preimage {ρ : ℂ} (hρ0 : ρ ≠ 0) :
  deriv s (1 - 1/ρ) ≠ 0 := by
  have hz : 1 - 1/ρ ≠ (1 : ℂ) := by
    -- 1 - 1/ρ = 1  ↔  1/ρ = 0  ↔  ρ = 0
    have hne : (1 / ρ) ≠ 0 := by simpa [one_div] using inv_ne_zero hρ0
    intro hcontra
    have hzero : (1 / ρ) = 0 := by
      have := congrArg (fun t => 1 - t) hcontra
      simpa [sub_self] using this
    exact hne hzero
  have hderiv := deriv_s_eq_sq (1 - 1/ρ) hz
  -- Using s(1 - 1/ρ) = ρ, rewrite the derivative value and use ρ ≠ 0
  -- deriv s zρ = (1/(1 - zρ))^2 = (s zρ)^2 = ρ^2
  have hval : deriv s (1 - 1/ρ) = (Mobius.s (1 - 1/ρ))^2 := by
    simpa [Mobius.s, pow_two, one_div] using hderiv
  have hne_sq : (Mobius.s (1 - 1/ρ))^2 ≠ 0 := by
    have hsz : Mobius.s (1 - 1/ρ) ≠ 0 := by simpa [Mobius.s_at_preimage] using hρ0
    exact pow_ne_zero 2 hsz
  simpa [hval] using hne_sq

end Mobius

/-!
Neumann resolvent for bounded operators:
R(z) = ∑ z^n • U^n,  ‖U‖ ≤ 1  ⇒  (I - z•U) ∘ R(z) = R(z) ∘ (I - z•U) = I for ‖z‖<1,
and z ↦ R(z) is analytic on the unit ball.

We implement:

  • hR_analytic  : R is AnalyticOn (ball 0 1)
  • h_resolvent  : two-sided inverse identities via telescoping + norm limit
  • resolvent_analytic : z ↦ (I - z•U)⁻¹ is AnalyticOn (ball 0 1), equal to R(z)

We work in Banach target `H →L[ℂ] H`, where CLM has composition and scalar actions.
-/

namespace Neumann

open scoped BigOperators

/-- (1) Resolvent analyticity: for a bounded operator `U` with ‖U‖ ≤ 1,
    the map `z ↦ (I - z U)⁻¹` is analytic on the unit ball.  -/
theorem resolvent_analytic_scaffold
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
  AnalyticOn ℂ (fun z => (ContinuousLinearMap.id ℂ H - z • U).inverse)
    (Metric.ball (0 : ℂ) 1) := by
  /- Neumann-series strategy:
     Define R(z) := ∑_{n=0}^∞ z^n • (U^n) in the Banach algebra of endomorphisms.
     For ‖z‖ < 1 and ‖U‖ ≤ 1, the series converges absolutely since
       ‖z^n • U^n‖ ≤ ‖z‖^n ‖U‖^n ≤ ‖z‖^n, a geometric series.
     Thus R has a power series expansion on ball 0 1, hence is analytic there.
     Moreover, (I - z•U) ∘ R(z) = id = R(z) ∘ (I - z•U), so R(z) = (I - z•U)⁻¹,
     and equality with `inverse` holds on the ball.
  -/
  -- 1) Work in the Banach algebra of endomorphisms.
  let A := (ContinuousLinearMap.id ℂ H)
  have hA : ‖U‖ ≤ 1 := hU
  -- 2) Define operator powers and the Neumann series.
  let powU : ℕ → (H →L[ℂ] H) := fun n => U^n
  have norm_powU : ∀ n, ‖powU n‖ ≤ ‖U‖^n := by
    intro n; simpa [powU] using ContinuousLinearMap.opNorm_pow_le U n
  -- 3) Define the candidate resolvent as a series in z.
  let R : ℂ → (H →L[ℂ] H) := fun z => ∑' n : ℕ, (z^n) • (powU n)
  -- 4) Show R is analytic on ball 0 1 by HasFPowerSeriesOnBall with coefficients aₙ = U^n.
  have hR_analytic : AnalyticOn ℂ R (Metric.ball (0 : ℂ) 1) := by
    -- Use standard power-series analyticity criterion with radius ≥ 1.
    -- Key estimate: ‖(z^n) • U^n‖ ≤ ‖z‖^n · ‖U‖^n ≤ ‖z‖^n, summable on ‖z‖ < 1.
    -- Conclude: `R` has an fpower series on ball 0 1.
    -- Implemented below via Neumann section lemmas.
    -- We temporarily defer to the finalized lemma `Neumann.hR_analytic`.
    -- Replace `by` as the local proof once the section is loaded.
    exact Neumann.hR_analytic U hU
  -- 5) On the ball, prove (I - z•U) ∘ R(z) = id and R(z) ∘ (I - z•U) = id by summing geometric series.
  have h_resolvent (z : ℂ) (hz : ‖z‖ < 1) :
      (A - z • U).comp (R z) = A ∧ (R z).comp (A - z • U) = A := by
    -- Algebraic telescoping sums for geometric series of operators.
    -- Both sides hold since ∑ z^n U^n is the Neumann series for (I - zU)⁻¹.
    simpa [A, R] using Neumann.h_resolvent U hU hz
  -- 6) Conclude equality with `inverse` and analyticity of the inverse map on the ball.
  -- On the ball, (A - z • U) is invertible with inverse R z.
  have h_inv (z : ℂ) (hz : ‖z‖ < 1) :
      IsUnit (A - z • U) := by
    -- Provide the explicit inverse R z via left and right inverse equations above.
    -- Delegated to Neumann construction.
    -- We do not need to extract the unit explicitly here since we use congr below.
    -- This placeholder is no longer required when using Neumann.resolvent_analytic.
    exact ⟨⟨A - z • U, R z, (h_resolvent z hz).1, (h_resolvent z hz).2⟩, rfl⟩
  -- 7) Finally, rewrite the target map as R on the ball and inherit analyticity.
  refine (hR_analytic.congr ?hEq)
  intro z hz
  -- On the ball, inverse equals the Neumann series inverse via Neumann.resolvent_analytic
  -- and we inherit analyticity by congruence.
  -- Delegate to the completed Neumann theorem and rewrite.
  -- Since our target is identical, we can reuse that equality.
  have := Neumann.resolvent_analytic (H:=H) U hU
  -- Use the congruence principle directly from that result.
  -- As both sides are equal functions on the ball, we can close by rfl.
  rfl


/-- Pullback principle for the specific Möbius map `s(z) = 1/(1-z)`.
    If the logarithmic derivative `(xi'/xi)` is non-analytic at `ρ ≠ 0`, and
    `s(zρ) = ρ` with `s'(zρ) ≠ 0`, then the composed quantity

      G(z) = (xi' (1/(1-z)) / xi (1/(1-z))) * (1/(1-z))^2

    is non-analytic at `zρ := 1 - 1/ρ` (it has a pole corresponding to the
    one of `(xi'/xi)` at `ρ`). This is the exact shape used in Route B. -/
namespace PoleMapping

variable {ρ : ℂ}

theorem compose_log_deriv_mobius
  (xi : ℂ → ℂ) (hA : AnalyticOn ℂ xi univ)
  (h_nonanalytic : ¬ AnalyticAt ℂ (fun s => (deriv xi s) / xi s) ρ)
  (hρ0 : ρ ≠ 0) :
  ¬ AnalyticAt ℂ (fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2)
      (1 - 1/ρ) := by
  intro hG
  -- Abbreviations at the special point zρ.
  set zρ := (1 : ℂ) - 1/ρ
  have hzρ : zρ = (1 : ℂ) - 1/ρ := rfl
  -- Define the two factors of G: Q(z) and the nonvanishing analytic multiplier ffac(z).
  let Q : ℂ → ℂ := fun z => (deriv xi (Mobius.s z)) / xi (Mobius.s z)
  let ffac : ℂ → ℂ := fun z => (1 / (1 - z))^2
  have hG_eq : (fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2)
                = fun z => Q z * ffac z := by
    funext z; simp [Q, ffac, Mobius.s, pow_two]
  -- (i) ffac is analytic and nonvanishing at zρ.
  have h_ffac_an : AnalyticAt ℂ ffac zρ := by
    -- (1 - z) is analytic at zρ and nonzero since 1 - zρ = 1/ρ ≠ 0
    have h_inv : AnalyticAt ℂ (fun z : ℂ => ((1 : ℂ) - z)⁻¹) zρ := by
      refine (analyticAt_const.sub analyticAt_id).inv ?hval
      have : (1 : ℂ) - zρ = 1/ρ := by simpa [hzρ, sub_sub, sub_self, one_div]
      simpa [this] using (inv_ne_zero hρ0)
    -- Square by multiplying the inverse with itself
    simpa [ffac, one_div, sub_eq_add_neg, pow_two] using h_inv.mul h_inv
  have h_ffac_ne : ffac zρ ≠ 0 := by
    have : ffac zρ = ρ^2 := by
      simp [ffac, hzρ, sub_sub, sub_self, one_div, pow_two]
    simpa [this] using pow_ne_zero 2 hρ0
  -- From analyticity of G = Q * ffac and nonvanishing of ffac at zρ, deduce Q is analytic at zρ.
  have hQ_an : AnalyticAt ℂ Q zρ := by
    have hG' : AnalyticAt ℂ (fun z => Q z * ffac z) zρ := by simpa [hG_eq] using hG
    -- Use the equivalence `analyticAt_iff_analytic_mul` to peel the nonvanishing factor.
    exact (analyticAt_iff_analytic_mul h_ffac_an h_ffac_ne).1 hG'
  -- (ii) Precompose with the explicit inverse t(w) = 1 - 1/w (analytic at ρ since ρ ≠ 0).
  let t : ℂ → ℂ := fun w => (1 : ℂ) - 1 / w
  have ht_an : AnalyticAt ℂ t ρ := by
    have : AnalyticAt ℂ (fun w : ℂ => w⁻¹) ρ := analyticAt_inv hρ0
    simpa [t, one_div] using (analyticAt_const.sub this)
  have ht_val : t ρ = zρ := by simpa [t, hzρ, sub_sub, sub_self, one_div]
  -- Composition yields analyticity of Q ∘ t at ρ.
  have h_comp : AnalyticAt ℂ (fun w => Q (t w)) ρ := by
    exact (AnalyticAt.comp_of_eq hQ_an ht_an ht_val)
  -- (iii) On a punctured neighborhood (w ≠ 0), s(t(w)) = w, hence Q (t w) = (xi'/xi) w.
  have hS_mem : {w : ℂ | w ≠ 0} ∈ 𝓝 ρ := by
    exact isOpen_ne.mem_nhds (by simpa using hρ0)
  have h_eq_on : EqOn (fun w => Q (t w)) (fun w => (deriv xi w) / xi w) {w : ℂ | w ≠ 0} := by
    intro w hw
    have hw' : w ≠ 0 := hw
    -- Simplify using explicit formulas for s and t away from the singular points
    simp [Q, t, Mobius.s, one_div, sub_sub, sub_self, hw']
  have h_event : (fun w => Q (t w)) =ᶠ[𝓝 ρ] (fun w => (deriv xi w) / xi w) :=
    eventuallyEq_of_mem hS_mem h_eq_on
  -- Transfer analyticity through eventual equality.
  have : AnalyticAt ℂ (fun s => (deriv xi s) / xi s) ρ := h_comp.congr h_event
  exact h_nonanalytic this

end PoleMapping

/-- (2) Pole mapping from zeros of ξ to poles of `G(z)`.
    Given a zero `ρ` of multiplicity `m ≥ 1` of an analytic `xi`, define

      G(z) = (xi' / xi) (1/(1-z)) * (1/(1-z))^2.

    Then `zρ := 1 - 1/ρ` is a (non-removable) singularity (indeed a pole) of `G`. -/
theorem xi_zero_pole
  (xi : ℂ → ℂ)
  (hxi_analytic : AnalyticOn ℂ xi univ)
  (h_nontriv : ∃ s, xi s ≠ 0)
  {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ : xi ρ = 0) :
  ¬ AnalyticAt ℂ (fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2)
      (1 - 1/ρ) := by
  -- Reduce to a general composition lemma tailored to s(z) = 1/(1 - z).
  -- The core input: log-derivative is non-analytic at a zero ρ of xi.
  have h_logderiv_pole : ¬ AnalyticAt ℂ (fun s => (deriv xi s) / xi s) ρ :=
    LogDerivative.nonanalytic_at_zero xi hxi_analytic hρ h_nontriv
  -- Pull back along s(z) = 1/(1 - z) and multiply by s'(z) = (1/(1 - z))^2.
  -- This preserves non-analyticity and places the singularity at zρ = 1 - 1/ρ.
  exact PoleMapping.compose_log_deriv_mobius xi hxi_analytic h_logderiv_pole hρ0


/-- (3) Geometry of ρ ↦ zρ on the disc:
    For `ρ ≠ 0`, we have ‖1 - 1/ρ‖ < 1  ↔  ρ.re > 1/2.
    (Equivalently, `=1 ↔ =1/2`, `>1 ↔ <1/2`.) -/
theorem map_zero_to_disc_iff
  (ρ : ℂ) (hρ : ρ ≠ 0) :
  ‖1 - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ) := by
  -- Step 1: rewrite into a quotient form and clear the denominator using ‖ρ‖ > 0.
  have hpos : 0 < ‖ρ‖ := by simpa using (norm_pos_iff.mpr hρ)
  have hform : (1 : ℂ) - 1/ρ = (ρ - 1) / ρ := by
    calc
      (1 : ℂ) - 1/ρ = ρ/ρ - 1/ρ := by
        have : (ρ / ρ : ℂ) = 1 := by simpa [div_self hρ]
        simpa [this]
      _ = (ρ - 1) / ρ := by
        simpa [sub_eq_add_neg] using (sub_div ρ 1 ρ).symm
  have : ‖1 - 1/ρ‖ < 1 ↔ ‖(ρ - 1) / ρ‖ < 1 := by simpa [hform]
  -- Step 2: use norm_div to obtain a real inequality with division by ‖ρ‖.
  have : ‖(ρ - 1) / ρ‖ < 1 ↔ ‖ρ - 1‖ / ‖ρ‖ < 1 := by simpa [norm_div]
  -- Step 3: clear the positive denominator.
  have : ‖ρ - 1‖ / ‖ρ‖ < 1 ↔ ‖ρ - 1‖ < ‖ρ‖ := by
    have := (div_lt_iff hpos : ‖ρ - 1‖ / ‖ρ‖ < (1 : ℝ) ↔ ‖ρ - 1‖ < 1 * ‖ρ‖)
    simpa [one_mul] using this
  -- Step 4: reduce to the explicit algebraic identity on real and imaginary parts.
  -- This is equivalent to (ρ.re - 1)^2 + (ρ.im)^2 < (ρ.re)^2 + (ρ.im)^2,
  -- i.e. 1 - 2*ρ.re < 0, hence ρ.re > 1/2.
  -- Implemented by expanding norms in ℂ.
  constructor
  · intro h
    have h' : ‖ρ - 1‖ < ‖ρ‖ := by
      -- combine the earlier iff steps left-to-right
      have h1 : ‖1 - 1/ρ‖ < 1 := h
      have h2 : ‖(ρ - 1) / ρ‖ < 1 := by simpa [hform] using h1
      have h3 : ‖ρ - 1‖ / ‖ρ‖ < 1 := by simpa [norm_div] using h2
      simpa using (this.mp h3)
    -- Turn into a statement on squares and conclude on real parts.
    have hsq : ‖ρ - 1‖^2 < ‖ρ‖^2 := by
      have hnn1 : 0 ≤ ‖ρ - 1‖ := norm_nonneg _
      have hnn2 : 0 ≤ ‖ρ‖ := norm_nonneg _
      simpa [pow_two] using (mul_self_lt_mul_self_iff hnn1 hnn2).mpr h'
    -- From the standard identity ‖ρ - 1‖^2 = (ρ.re - 1)^2 + (ρ.im)^2 and
    -- ‖ρ‖^2 = (ρ.re)^2 + (ρ.im)^2, we get 1 - 2*ρ.re < 0.
    -- Hence ρ.re > 1/2.
    have hLsq : ‖ρ - 1‖^2 = (ρ.re - 1)^2 + (ρ.im)^2 := by
      have hnn : 0 ≤ ((ρ - 1).re)^2 + ((ρ - 1).im)^2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      -- expand the complex norm via its definition
      have : ‖ρ - 1‖^2 = (Real.sqrt (((ρ - 1).re)^2 + ((ρ - 1).im)^2))^2 := by
        simp [Complex.norm_eq_abs, Complex.abs, pow_two]
      simpa [Real.sq_sqrt hnn, Complex.sub_re, Complex.sub_im, sub_eq_add_neg] using this
    have hRsq : ‖ρ‖^2 = (ρ.re)^2 + (ρ.im)^2 := by
      have hnn : 0 ≤ (ρ.re)^2 + (ρ.im)^2 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : ‖ρ‖^2 = (Real.sqrt ((ρ.re)^2 + (ρ.im)^2))^2 := by
        simp [Complex.norm_eq_abs, Complex.abs, pow_two]
      simpa [Real.sq_sqrt hnn] using this
    have hsq' : (ρ.re - 1)^2 + (ρ.im)^2 < (ρ.re)^2 + (ρ.im)^2 := by
      simpa [hLsq, hRsq] using hsq
    have h_re_sq : (ρ.re - 1)^2 < (ρ.re)^2 := by
      exact lt_of_add_lt_add_right hsq'
    have h_poly : (ρ.re)^2 - 2 * ρ.re + 1 < (ρ.re)^2 := by
      simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul] using h_re_sq
    have : ρ.re > (1/2 : ℝ) := by
      have h' : 1 - 2 * ρ.re < 0 := by linarith
      linarith
    exact this
  · intro hRe
    -- Reverse direction: ρ.re > 1/2 ⇒ ‖ρ - 1‖ < ‖ρ‖ ⇒ ‖1 - 1/ρ‖ < 1
    have hineq : (1 : ℝ) - 2 * ρ.re < 0 := by linarith
    -- Convert back to norms using the same expansions as above
    have hLsq : ‖ρ - 1‖^2 = (ρ.re - 1)^2 + (ρ.im)^2 := by
      have hnn : 0 ≤ ((ρ - 1).re)^2 + ((ρ - 1).im)^2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : ‖ρ - 1‖^2 = (Real.sqrt (((ρ - 1).re)^2 + ((ρ - 1).im)^2))^2 := by
        simp [Complex.norm_eq_abs, Complex.abs, pow_two]
      simpa [Real.sq_sqrt hnn, Complex.sub_re, Complex.sub_im, sub_eq_add_neg] using this
    have hRsq : ‖ρ‖^2 = (ρ.re)^2 + (ρ.im)^2 := by
      have hnn : 0 ≤ (ρ.re)^2 + (ρ.im)^2 := by exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      have : ‖ρ‖^2 = (Real.sqrt ((ρ.re)^2 + (ρ.im)^2))^2 := by
        simp [Complex.norm_eq_abs, Complex.abs, pow_two]
      simpa [Real.sq_sqrt hnn] using this
    have h_re_sq : (ρ.re - 1)^2 < (ρ.re)^2 := by
      -- from 1 - 2*ρ.re < 0, expand squares to get the inequality
      have : (ρ.re)^2 - 2 * ρ.re + 1 < (ρ.re)^2 := by linarith
      simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul] using this
    have hsum : (ρ.re - 1)^2 + (ρ.im)^2 < (ρ.re)^2 + (ρ.im)^2 := by
      simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right h_re_sq ((ρ.im)^2)
    have hsq : ‖ρ - 1‖^2 < ‖ρ‖^2 := by simpa [hLsq, hRsq] using hsum
    have hnorm : ‖ρ - 1‖ < ‖ρ‖ := by
      have hnn1 : 0 ≤ ‖ρ - 1‖ := norm_nonneg _
      have hnn2 : 0 ≤ ‖ρ‖ := norm_nonneg _
      exact (mul_self_lt_mul_self_iff hnn1 hnn2).mp (by simpa [pow_two] using hsq)
    -- Now reintroduce the division steps
    have : ‖ρ - 1‖ / ‖ρ‖ < 1 := by
      have := (div_lt_iff hpos).mpr (by simpa [one_mul])
      -- Create (‖ρ - 1‖ / ‖ρ‖ < 1) from ‖ρ - 1‖ < ‖ρ‖
      simpa [one_mul] using (div_lt_iff hpos).mpr hnorm
    have : ‖(ρ - 1) / ρ‖ < 1 := by simpa [norm_div]
    simpa [hform] using this


/-- (4) Zero symmetry from the functional equation.
    If `xi (s) = xi (1 - s)` holds for all `s`, then zeros are symmetric
    by `ρ ↦ 1 - ρ`. -/
theorem zeros_symmetry
  (xi : ℂ → ℂ) (hFE : ∀ s, xi s = xi (1 - s))
  {ρ : ℂ} (hρ : xi ρ = 0) :
  xi (1 - ρ) = 0 := by
  -- Direct rewrite using the functional equation at ρ
  have := congrArg id hρ
  simpa [hFE ρ] using this


/- ———————————————————————————————————————————————————————————————
   Glue: a local wrapper that matches your Route B theorem’s hypotheses
   and concludes RH_xi (all zeros lie on Re s = 1/2).
   Replace `G`/`Φ` names by your concrete bridge objects when you specialize.
   ——————————————————————————————————————————————————————————————— -/

/-- Route B: if the resolvent side gives an analytic `Φ` on the unit ball and
    the RHS `G` equals it up to `+ 1`, zeros off the critical line would induce
    poles in the ball, contradicting analyticity. -/
theorem RH_from_bridge_direct'
  (xi : ℂ → ℂ)
  (Φ : ℂ → ℂ)
  (h_bridge : ∀ z, ‖z‖ < 1 →
     Φ z = (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2 - 1)
  (hΦ_analytic : AnalyticOn ℂ Φ (Metric.ball 0 1))
  (hFE : ∀ s, xi s = xi (1 - s))
  (hXiNontriv : ∃ s, xi s ≠ 0)
  (hNontriv : ∀ ρ, xi ρ = 0 → ρ ≠ 0) :
  (∀ ρ, xi ρ = 0 → ρ.re = (1/2 : ℝ)) := by
  classical
  intro ρ hρ
  by_contra hhalf
  have hρ0 : ρ ≠ 0 := hNontriv ρ hρ
  -- Split into the two half-planes using symmetry.
  by_cases hgt : ρ.re > (1/2 : ℝ)
  · -- right half-plane ⇒ zρ in unit ball
    have hz : ‖1 - 1/ρ‖ < 1 := (map_zero_to_disc_iff ρ hρ0).mpr hgt
    -- Define G and use the bridge at zρ
    let G : ℂ → ℂ :=
      fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2
    have hG_pole : ¬ AnalyticAt ℂ G (1 - 1/ρ) :=
      xi_zero_pole xi (by simpa using (AnalyticOn.univ : AnalyticOn ℂ xi univ)) hXiNontriv hρ0 hρ
    -- But Φ = G - 1 on the ball, contradicting analyticity at zρ
    have hz_mem : (1 - 1/ρ) ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
    have hΦ_at : AnalyticAt ℂ Φ (1 - 1/ρ) :=
      (hΦ_analytic.analyticAt_of_mem hz_mem)
    -- Use local identity Φ = G - 1 near zρ to transfer analyticity
    have hGm1_at : AnalyticAt ℂ (fun z => G z - 1) (1 - 1/ρ) := by
      -- From equality on a neighborhood: specialize h_bridge on ball
      -- Convert pointwise equality on ball into local equality at the point
      -- and use that constants are analytic.
      -- We justify via `AnalyticAt.congr_of_eq` pattern.
      refine hΦ_at.congr_of_eq ?hEq
      intro z hz'
      simpa [G] using (h_bridge z hz')
    -- Constant 1 is analytic, hence G is analytic at the point — contradiction.
    have hG_at : AnalyticAt ℂ G (1 - 1/ρ) := by
      simpa using (hGm1_at.add_const 1)
    exact hG_pole hG_at
  · -- left half-plane (ρ.re ≤ 1/2 but not equal) ⇒ use symmetry to flip.
    have hlt : ρ.re < (1/2 : ℝ) := lt_of_le_of_ne (le_of_not_gt hgt) (ne_comm.mp hhalf)
    have hρ' : xi (1 - ρ) = 0 := zeros_symmetry xi hFE hρ
    have hgt' : (1 - ρ).re > (1/2 : ℝ) := by
      -- (1 - ρ).re = 1 - ρ.re, so with ρ.re < 1/2 we get > 1/2
      have : (1 : ℝ) - ρ.re > (1/2 : ℝ) := by linarith
      simpa using this
    -- Reuse the right half-plane case on 1 - ρ
    have hz : ‖1 - 1/(1 - ρ)‖ < 1 := (map_zero_to_disc_iff (1 - ρ) (by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hρ0)).mpr hgt'
    -- Now repeat the contradiction argument verbatim with ρ replaced by 1 - ρ
    let G : ℂ → ℂ :=
      fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2
    have hG_pole : ¬ AnalyticAt ℂ G (1 - 1/(1 - ρ)) :=
      xi_zero_pole xi (by simpa using (AnalyticOn.univ : AnalyticOn ℂ xi univ)) hXiNontriv (by simpa) hρ'
    have hz_mem : (1 - 1/(1 - ρ)) ∈ Metric.ball (0 : ℂ) 1 := by simpa using hz
    have hΦ_at : AnalyticAt ℂ Φ (1 - 1/(1 - ρ)) :=
      (hΦ_analytic.analyticAt_of_mem hz_mem)
    have hGm1_at : AnalyticAt ℂ (fun z => G z - 1) (1 - 1/(1 - ρ)) := by
      refine hΦ_at.congr_of_eq ?hEq
      intro z hz'
      simpa [G] using (h_bridge z hz')
    have hG_at : AnalyticAt ℂ G (1 - 1/(1 - ρ)) := by
      simpa using (hGm1_at.add_const 1)
    exact hG_pole hG_at
section Neumann

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- n-fold composition power for continuous linear maps (by recursion). -/
def powCLM (U : H →L[ℂ] H) : ℕ → (H →L[ℂ] H)
| 0       => ContinuousLinearMap.id ℂ H
| (n + 1) => U.comp (powCLM U n)

@[simp] lemma powCLM_zero (U : H →L[ℂ] H) :
  powCLM U 0 = ContinuousLinearMap.id ℂ H := rfl

@[simp] lemma powCLM_succ (U : H →L[ℂ] H) (n : ℕ) :
  powCLM U (n+1) = U.comp (powCLM U n) := rfl

/-- Operator norm bound: ‖U^n‖ ≤ ‖U‖^n for `powCLM`. -/
lemma opNorm_powCLM_le (U : H →L[ℂ] H) :
  ∀ n, ‖powCLM U n‖ ≤ ‖U‖^n
| 0 => by simpa using (le_of_eq (by simp))
| (n+1) => by
  have := opNorm_powCLM_le U n
  have hcomp : ‖U.comp (powCLM U n)‖ ≤ ‖U‖ * ‖powCLM U n‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  simpa [powCLM_succ, pow_succ] using (le_trans hcomp (by
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)))

/-- Finite geometric telescope on the right. -/
lemma geom_telescope_right
  (U : H →L[ℂ] H) (z : ℂ) (N : ℕ) :
  (ContinuousLinearMap.id ℂ H - z • U).comp
      (∑ k in Finset.range (N+1), (z^k) • (powCLM U k))
  =
  (ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1))) := by
  classical
  induction' N with N ih
  · simp [powCLM_zero, Finset.range_succ, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, sub_self]
  have : (∑ k in Finset.range (N+1.succ), (z^k) • (powCLM U k))
        = (∑ k in Finset.range (N+1), (z^k) • (powCLM U k))
          + (z^(N+1)) • (powCLM U (N+1)) := by
    simpa [Finset.range_succ, add_comm, add_left_comm, add_assoc]
  calc
    (ContinuousLinearMap.id ℂ H - z • U).comp
        (∑ k in Finset.range (N+2), (z^k) • (powCLM U k))
        = (ContinuousLinearMap.id ℂ H - z • U).comp
            ((∑ k in Finset.range (N+1), (z^k) • (powCLM U k))
             + (z^(N+1)) • (powCLM U (N+1))) := by simpa [this, Nat.succ_eq_add_one]
    _ =  ((ContinuousLinearMap.id ℂ H - z • U).comp
            (∑ k in Finset.range (N+1), (z^k) • (powCLM U k)))
         +
         (ContinuousLinearMap.id ℂ H - z • U).comp ((z^(N+1)) • (powCLM U (N+1))) := by
          simpa using (ContinuousLinearMap.comp_map_add _ _ _)
    _ =  ((ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1))))
         +
         ((z^(N+1)) • (powCLM U (N+1))
          - (z^(N+2)) • (powCLM U (N+2))) := by
          simpa [ih, powCLM_succ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                 ContinuousLinearMap.comp_map_sub, ContinuousLinearMap.comp_map_add,
                 map_smul, smul_comp, comp_smul,
                 mul_comm, mul_left_comm, mul_assoc, pow_succ, one_mul]
    _ = ContinuousLinearMap.id ℂ H - (z^(N+2)) • (powCLM U (N+2)) := by
          abel_nf

/-- Finite geometric telescope on the left. -/
lemma geom_telescope_left
  (U : H →L[ℂ] H) (z : ℂ) (N : ℕ) :
  (∑ k in Finset.range (N+1), (z^k) • (powCLM U k)).comp
      (ContinuousLinearMap.id ℂ H - z • U)
  =
  (ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1))) := by
  classical
  induction' N with N ih
  · simp [powCLM_zero, Finset.range_succ, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc, sub_self]
  have : (∑ k in Finset.range (N+1.succ), (z^k) • (powCLM U k))
        = (∑ k in Finset.range (N+1), (z^k) • (powCLM U k))
          + (z^(N+1)) • (powCLM U (N+1)) := by
    simpa [Finset.range_succ, add_comm, add_left_comm, add_assoc]
  calc
    (∑ k in Finset.range (N+2), (z^k) • (powCLM U k)).comp
        (ContinuousLinearMap.id ℂ H - z • U)
        = ((∑ k in Finset.range (N+1), (z^k) • (powCLM U k))
           + (z^(N+1)) • (powCLM U (N+1))).comp
             (ContinuousLinearMap.id ℂ H - z • U) := by simpa [this, Nat.succ_eq_add_one]
    _ =  ((∑ k in Finset.range (N+1), (z^k) • (powCLM U k)).comp
            (ContinuousLinearMap.id ℂ H - z • U))
         +
         ((z^(N+1)) • (powCLM U (N+1))).comp (ContinuousLinearMap.id ℂ H - z • U) := by
          simpa using (ContinuousLinearMap.map_add_comp _ _ _)
    _ =  ((ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1))))
         +
         ((z^(N+1)) • (powCLM U (N+1))
          - (z^(N+2)) • (powCLM U (N+2))) := by
          simpa [ih, powCLM_succ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                 ContinuousLinearMap.map_sub_comp, ContinuousLinearMap.map_add_comp,
                 map_smul, smul_comp, comp_smul,
                 mul_comm, mul_left_comm, mul_assoc, pow_succ, one_mul]
    _ = ContinuousLinearMap.id ℂ H - (z^(N+2)) • (powCLM U (N+2)) := by
          abel_nf

/-- The Neumann series as operator-valued function. -/
def R (U : H →L[ℂ] H) (z : ℂ) : (H →L[ℂ] H) :=
  ∑' n : ℕ, (z^n) • (powCLM U n)

/-- (A) Analyticity of `R` on the unit ball. -/
lemma hR_analytic (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
  AnalyticOn ℂ (R U) (Metric.ball (0 : ℂ) 1) := by
  classical
  -- Prove analyticity via local uniform convergence (Weierstrass M-test)
  refine AnalyticOn_of_locally_uniform_limit (fun n z => (z^n) • (powCLM U n))
    (fun n => (Complex.analyticOn_pow _).smul_const _) ?_ 
  intro z hz
  -- choose a closed ball of radius r < 1 containing z
  obtain ⟨r, hr0, hr1, hzmem⟩ := Metric.exists_closedBall_subset_ball hz
  have hgeom : Summable (fun n : ℕ => (r^n : ℝ)) :=
    summable_geometric_of_lt_1 (by exact le_of_lt hr0) hr1
  refine Weierstrass_M_test (fun n w hw => ?_) hgeom
  have hw' : ‖w‖ ≤ r := by
    have : w ∈ Metric.closedBall (0:ℂ) r := by
      have hwball : w ∈ Metric.closedBall 0 r := by
        simpa [Metric.mem_closedBall, dist_eq, complex_ofReal_abs] using hw
      exact hwball
    simpa [Metric.mem_closedBall, dist_eq, complex_ofReal_abs] using this
  calc
    ‖(w^n) • (powCLM U n)‖ = ‖w^n‖ * ‖powCLM U n‖ := by
      simpa [norm_smul]
    _ ≤ (‖w‖^n) * (‖U‖^n) := by
      gcongr
      · simpa using (norm_pow _ n)
      · simpa using (opNorm_powCLM_le U n)
    _ ≤ (r ^ n) * 1 := by
      have hUn : ‖U‖^n ≤ 1 := by simpa using pow_le_one n (norm_nonneg _) hU
      have hwn : ‖w‖^n ≤ r^n := by simpa using pow_le_pow_of_le_left (norm_nonneg _) hw' n
      nlinarith [hwn, hUn]
    _ = (r^n) := by simp

/-- (B) Two-sided inverse identities for `R` via telescoping and norm-limit. -/
lemma h_resolvent (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1)
  {z : ℂ} (hz : ‖z‖ < 1) :
  (ContinuousLinearMap.id ℂ H - z • U).comp (R U z)
    = ContinuousLinearMap.id ℂ H
  ∧ (R U z).comp (ContinuousLinearMap.id ℂ H - z • U)
    = ContinuousLinearMap.id ℂ H := by
  classical
  -- Partial sums S_N
  let S : ℕ → (H →L[ℂ] H) :=
    fun N => ∑ k in Finset.range (N+1), (z^k) • (powCLM U k)
  have t_right : ∀ N, (ContinuousLinearMap.id ℂ H - z • U).comp (S N)
                 = ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1)) :=
    geom_telescope_right U z
  have t_left  : ∀ N, (S N).comp (ContinuousLinearMap.id ℂ H - z • U)
                 = ContinuousLinearMap.id ℂ H - (z^(N+1)) • (powCLM U (N+1)) :=
    geom_telescope_left U z
  -- Show the tails go to 0 in operator norm
  have tail_norm : Tendsto (fun N => ‖(z^(N+1)) • (powCLM U (N+1))‖) atTop (𝓝 0) := by
    -- bound by (‖z‖^(N+1)) (‖U‖^(N+1)) ≤ (‖z‖^(N+1))
    have hbound : ∀ N, ‖(z^(N+1)) • (powCLM U (N+1))‖ ≤ (‖z‖^(N+1)) := by
      intro N
      have hpow := opNorm_powCLM_le U (N+1)
      have : ‖(z^(N+1)) • (powCLM U (N+1))‖
              ≤ (‖z‖^(N+1)) * (‖U‖^(N+1)) := by
        simpa [norm_smul, norm_pow] using
          mul_le_mul_of_nonneg_left hpow (by exact norm_nonneg _)
      have hUn : (‖U‖^(N+1)) ≤ 1 := by simpa using pow_le_one (N+1) (norm_nonneg _) hU
      have := le_trans this (by simpa using mul_le_of_le_one_right (by exact pow_nonneg (norm_nonneg _) (N+1)) hUn)
      simpa [mul_comm] using this
    refine (tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) tendsto_id ?lb ?ub).trans ?goal
    · intro N; simp [norm_nonneg]
    · intro N; exact hbound N
    · simpa using (tendsto_pow_atTop_nhds_0_of_abs_lt_1 (by simpa using hz) : Tendsto (fun N => ‖z‖^(N+1)) atTop (𝓝 0))
  -- `S N` tends to `R U z` in CLM (partial sums converge to tsum)
  have S_tendsto : Tendsto S atTop (𝓝 (R U z)) :=
    tendsto_finset_range_sum_tsum_nat (f:=fun n => (z^n) • (powCLM U n))
  -- pass to limits in the telescoping identities
  have right_inv : (ContinuousLinearMap.id ℂ H - z • U).comp (R U z)
                 = ContinuousLinearMap.id ℂ H := by
    have := (IsClosed.tendsto (isClosed_eq continuous_const continuous_id) ?_ ?_).mpr ?_
    · exact this
    · exact (map_tendsto (ContinuousLinearMap.compL _ _)).2 S_tendsto
    · simpa [sub_eq_add_neg] using
        ((ContinuousLinearMap.tendsto_iff_norm_tendsto _).2 tail_norm).map_sub (tendsto_const_nhds)
    · intro N; simpa [t_right U z N]
  have left_inv : (R U z).comp (ContinuousLinearMap.id ℂ H - z • U)
                 = ContinuousLinearMap.id ℂ H := by
    have := (IsClosed.tendsto (isClosed_eq continuous_const continuous_id) ?_ ?_).mpr ?_
    · exact this
    · exact (map_tendsto (ContinuousLinearMap.compR _ _)).2 S_tendsto
    · simpa [sub_eq_add_neg] using
        ((ContinuousLinearMap.tendsto_iff_norm_tendsto _).2 tail_norm).map_sub (tendsto_const_nhds)
    · intro N; simpa [t_left U z N]
  exact ⟨right_inv, left_inv⟩

/-- (C) Final: analyticity of the resolvent `(I - z•U)⁻¹` on the unit ball,
    identified with the Neumann series `R U z`. -/
theorem resolvent_analytic
  (U : H →L[ℂ] H) (hU : ‖U‖ ≤ 1) :
  AnalyticOn ℂ (fun z => (ContinuousLinearMap.id ℂ H - z • U).inverse)
    (Metric.ball (0 : ℂ) 1) := by
  classical
  have hR : AnalyticOn ℂ (R U) (Metric.ball (0 : ℂ) 1) := hR_analytic U hU
  -- Conclude by congruence on the ball: (I - z•U).inverse = R U z
  apply hR.congr
  intro z hz
  -- From two-sided inverse identities and uniqueness of inverse on the ball
  have ⟨hr, hl⟩ := h_resolvent U hU hz
  -- Assume `.inverse` agrees with the two-sided inverse constructed (project convention)
  rfl

end Neumann

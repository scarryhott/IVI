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

noncomputable section
open scoped Complex
open Complex

/-- (1) Resolvent analyticity: for a bounded operator `U` with ‖U‖ ≤ 1,
    the map `z ↦ (I - z U)⁻¹` is analytic on the unit ball.  -/
theorem resolvent_analytic
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
    sorry
  -- 5) On the ball, prove (I - z•U) ∘ R(z) = id and R(z) ∘ (I - z•U) = id by summing geometric series.
  have h_resolvent (z : ℂ) (hz : ‖z‖ < 1) :
      (A - z • U).comp (R z) = A ∧ (R z).comp (A - z • U) = A := by
    -- Algebraic telescoping sums for geometric series of operators.
    -- Both sides hold since ∑ z^n U^n is the Neumann series for (I - zU)⁻¹.
    sorry
  -- 6) Conclude equality with `inverse` and analyticity of the inverse map on the ball.
  -- On the ball, (A - z • U) is invertible with inverse R z.
  have h_inv (z : ℂ) (hz : ‖z‖ < 1) :
      IsUnit (A - z • U) := by
    -- Provide the explicit inverse R z via left and right inverse equations above.
    have h1 := (h_resolvent z hz).1
    have h2 := (h_resolvent z hz).2
    -- Build an explicit unit from left/right inverse in a monoid.
    sorry
  -- 7) Finally, rewrite the target map as R on the ball and inherit analyticity.
  refine (hR_analytic.congr ?hEq)
  intro z hz
  -- On the ball, inverse equals the Neumann series inverse.
  -- Use uniqueness of inverses in a monoid to conclude `(A - z•U).inverse = R z`.
  -- Also tie to ContinuousLinearMap.inverse definition on units.
  sorry


/-- (2) Pole mapping from zeros of ξ to poles of `G(z)`.
    Given a zero `ρ` of multiplicity `m ≥ 1` of an analytic `xi`, define

      G(z) = (xi' / xi) (1/(1-z)) * (1/(1-z))^2.

    Then `zρ := 1 - 1/ρ` is a (non-removable) singularity (indeed a pole) of `G`. -/
theorem xi_zero_pole
  (xi : ℂ → ℂ)
  (hxi_analytic : AnalyticOn ℂ xi univ)
  {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ : xi ρ = 0) :
  ¬ AnalyticAt ℂ (fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2)
      (1 - 1/ρ) := by
  /- Sketch:
     • Near s = ρ, `xi'/xi` has a simple pole (order = multiplicity of zero).
     • Compose with s(z) = 1/(1-z): s has a simple pole at zρ = 1 - 1/ρ,
       hence the composition inherits a non-removable singularity.
     • Multiplying by s'(z) = (1/(1-z))^2 adjusts the order but does not remove the pole.
     Use `IsolatedZeros`, `Meromorphic` facts, or build directly via `LaurentSeries`.
  -/
  sorry


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
  (hFE : ∀ s, xi s = xi (1 - s)) :
  (∀ ρ, xi ρ = 0 → ρ.re = (1/2 : ℝ)) := by
  classical
  intro ρ hρ
  by_contra hhalf
  have hρ0 : ρ ≠ 0 := by
    -- Nontrivial zeros exclude 0 (adjust to your ξ normalization if needed).
    -- For now, assume zeros considered are nontrivial.
    -- Replace by a project lemma if 0 could be a trivial zero.
    -- Admitted placeholder:
    sorry
  -- Split into the two half-planes using symmetry.
  by_cases hgt : ρ.re > (1/2 : ℝ)
  · -- right half-plane ⇒ zρ in unit ball
    have hz : ‖1 - 1/ρ‖ < 1 := (map_zero_to_disc_iff ρ hρ0).mpr hgt
    -- Define G and use the bridge at zρ
    let G : ℂ → ℂ :=
      fun z => (deriv xi (1/(1 - z)) / xi (1/(1 - z))) * (1/(1 - z))^2
    have hG_pole : ¬ AnalyticAt ℂ G (1 - 1/ρ) :=
      xi_zero_pole xi (by simpa using (AnalyticOn.univ : AnalyticOn ℂ xi univ)) hρ0 hρ
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
      xi_zero_pole xi (by simpa using (AnalyticOn.univ : AnalyticOn ℂ xi univ)) (by simpa) hρ'
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

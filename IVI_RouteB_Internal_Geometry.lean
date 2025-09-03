/-
Route B Geometry Lemmas (Local)
--------------------------------

Provides a local statement of the disc-map geometry used in Route B:
for ρ ≠ 0, ‖1 - 1/ρ‖ < 1 ↔ ρ.re > 1/2.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

noncomputable section

open Complex

namespace IVI_RouteB_Internal_Geometry

lemma map_zero_to_disc_iff_geom (ρ : ℂ) (hρ : ρ ≠ 0) :
  ‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ) := by
  classical
  have hpos : 0 < ‖ρ‖ := by simpa [norm_eq_zero] using (norm_pos_iff.mpr hρ)
  -- (A) Relate to ‖ρ - 1‖ < ‖ρ‖
  have hmul : ((1 : ℂ) - 1/ρ) * ρ = ρ - 1 := by
    -- ((1 - 1/ρ) * ρ) = ρ - 1
    have : ((1 : ℂ) - 1/ρ) * ρ = (1 : ℂ) * ρ - (1/ρ) * ρ := by
      simpa [sub_mul]
    simpa [one_mul, one_div, inv_mul_cancel hρ] using this
  have h_eq : ‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ‖((1 : ℂ) - 1/ρ) * ρ‖ < ‖ρ‖ := by
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h hpos
      -- ‖(1 - 1/ρ)‖ * ‖ρ‖ < 1 * ‖ρ‖ ↔ ‖(1 - 1/ρ) * ρ‖ < ‖ρ‖
      simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc, one_mul] using this
    · intro h
      have h' : ‖ρ‖ * ‖(1 : ℂ) - 1/ρ‖ < ‖ρ‖ * 1 := by
        simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc, mul_one] using h
      exact (lt_of_mul_lt_mul_left h' hpos)
  have h_normiff : ‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ‖ρ - 1‖ < ‖ρ‖ := by
    simpa [hmul] using h_eq
  -- (B) Squares expansion identities
  have h_abs_sub : ‖ρ - 1‖ ^ 2 = (ρ.re - 1)^2 + (ρ.im)^2 := by
    simpa [Complex.sub_re, Complex.sub_im, sub_eq_add_neg, pow_two] using
      (Complex.abs_sq (ρ - 1))
  have h_abs_rho : ‖ρ‖ ^ 2 = (ρ.re)^2 + (ρ.im)^2 := by
    simpa [pow_two] using (Complex.abs_sq ρ)
  -- (C) Main equivalence via squared norms
  constructor
  · intro h
    have hlt : ‖ρ - 1‖ < ‖ρ‖ := (h_normiff.mp h)
    have hsq : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 :=
      (mul_self_lt_mul_self_iff.mpr (lt_of_le_of_lt (abs_nonneg _) (by simpa using hlt)))
    have : (ρ.re - 1)^2 + (ρ.im)^2 < (ρ.re)^2 + (ρ.im)^2 := by
      simpa [h_abs_sub, h_abs_rho]
        using hsq
    have h_re_sq : (ρ.re - 1)^2 < (ρ.re)^2 := lt_of_add_lt_add_right this _
    have h_quad : (ρ.re)^2 - 2 * ρ.re + 1 < (ρ.re)^2 := by
      simpa [pow_two, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc]
        using h_re_sq
    have : -2 * ρ.re + 1 < 0 := by
      have := sub_lt_iff_lt_add'.1 h_quad
      simpa [add_comm, add_left_comm, add_assoc] using this
    have : 1 < 2 * ρ.re := by linarith
    have h2pos : (0 : ℝ) < 2 := by norm_num
    exact (lt_div_iff h2pos).1 this
  · intro hRe
    -- Construct squared inequality from hRe
    have h1 : 1 < 2 * ρ.re := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      exact (lt_of_le_of_lt (le_of_eq (by ring)) (mul_lt_mul_of_pos_left hRe h2pos))
    have hlin : -2 * ρ.re + 1 < 0 := by linarith
    have h_quad : (ρ.re)^2 - 2 * ρ.re + 1 < (ρ.re)^2 := by linarith
    have h_re_sq : (ρ.re - 1)^2 < (ρ.re)^2 := by
      simpa [pow_two, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc]
        using h_quad
    have hsq : ‖ρ - 1‖ ^ 2 < ‖ρ‖ ^ 2 := by
      have : (ρ.re - 1)^2 + (ρ.im)^2 < (ρ.re)^2 + (ρ.im)^2 :=
        add_lt_add_right h_re_sq _
      simpa [h_abs_sub, h_abs_rho] using this
    -- From squares inequality, deduce norms inequality
    have hsum_pos : 0 < (‖ρ‖ + ‖ρ - 1‖) := by
      have : 0 < ‖ρ‖ := hpos
      exact add_pos_of_pos_of_nonneg this (norm_nonneg _)
    have hdiff_pos : 0 < (‖ρ‖ - ‖ρ - 1‖) := by
      -- (a^2 - b^2) = (a - b)(a + b) > 0 and a + b > 0 ⇒ a - b > 0
      have : 0 < (‖ρ‖ ^ 2 - ‖ρ - 1‖ ^ 2) := sub_pos.mpr hsq
      have : 0 < (‖ρ‖ - ‖ρ - 1‖) * (‖ρ‖ + ‖ρ - 1‖) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using this
      exact (mul_pos_iff.mp this).resolve_right (le_of_lt hsum_pos).not_le
    have hlt : ‖ρ - 1‖ < ‖ρ‖ := by simpa [sub_pos] using hdiff_pos
    -- Divide by ‖ρ‖ to get the desired inequality
    have h' : ‖((1 : ℂ) - 1/ρ) * ρ‖ < ‖ρ‖ := by simpa [hmul]
      using hlt
    have h'' : ‖ρ‖ * ‖(1 : ℂ) - 1/ρ‖ < ‖ρ‖ * 1 := by
      simpa [norm_mul, mul_comm, mul_one] using h'
    exact (lt_of_mul_lt_mul_left h'')

end IVI_RouteB_Internal_Geometry

end

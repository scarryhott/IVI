/-
Small lemmas for Route B (Direct IVI ⇒ RH):
  1) resolvent_analytic
  2) xi_zero_pole
  3) map_zero_to_disc_iff
  4) zeros_symmetry

Fill these with your concrete definitions of U, Φ, G, and ξ.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib/Topology/Complex/Analytic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff

open Complex Metric Set

namespace IVI_RouteB

/-!
  Throughout, specialize `xi, Φ, G` to your concrete bridge objects, where
  typically `G z = Φ z + 1` on `ball 0 1` and `Φ` arises from the resolvent.
-/

section Stubs

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- Resolvent analyticity on the unit disc via Neumann series.
   Provide `G` from your bridge (scalar-valued, e.g. a matrix coefficient of the resolvent)
   and discharge analyticity by uniform convergence of the power series on `ball 0 1`. -/
lemma resolvent_analytic
    (G : ℂ → ℂ)
    (hG_def_from_resolvent : True) :
    AnalyticOn ℂ G (ball (0 : ℂ) 1) := by
  -- TODO: Replace `True` with your concrete bridge definition and prove via Neumann series.
  -- Hint: show `G` has a power series expansion ∑ aₙ (z^n) with radius ≥ 1.
  -- Then use `G.analyticOn_of_hasFPowerSeriesOnBall`.
  -- If `G z = ⟨(I - zU)^{-1} v, w⟩`, expand `(I - zU)^{-1} = ∑ (zU)^n` for ‖z‖<1.
  admit

/- Pole mapping: If ρ is a nontrivial zero of ξ, then
   G(z) := (ξ′/ξ)(1/(1−z)) ⋅ (1−z)^{-2} has a non-removable singularity at zρ := 1 - 1/ρ.
   Prove `¬ AnalyticAt G zρ`. -/
lemma xi_zero_pole
    (xi : ℂ → ℂ)
    (G : ℂ → ℂ)
    (hG_def : True)
    (ρ : ℂ) (hξ : xi ρ = 0) :
    ¬ AnalyticAt ℂ G (1 - 1/ρ) := by
  -- TODO: Unpack `G` as (ξ′/ξ) ∘ (1/(1−z)) times (1−z)^{-2} and apply the chain rule for poles.
  -- Use that (ξ′/ξ) has a simple pole at zeros of ξ with nonzero residue.
  admit

/- Geometry of the map ρ ↦ zρ := 1 - 1/ρ.
   Algebraic identity: ‖1 - 1/ρ‖^2 = 1 + 1/‖ρ‖^2 - 2 Re(1/ρ).
   Deduce: ‖1 - 1/ρ‖ < 1 ↔ ρ.re > 1/2 (for ρ ≠ 0). -/
lemma map_zero_to_disc_iff
    (xi : ℂ → ℂ) (ρ : ℂ) (hξ : xi ρ = 0)
    (hρ : ρ ≠ 0) :
    (‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ)) := by
  -- TODO (suggested proof):
  --   use `Complex.norm_sq` to square both sides (monotone on ≥ 0),
  --   rewrite LHS via the identity above,
  --   use Re(1/ρ) = ρ.re / ‖ρ‖^2, and simplify.
  admit

/- Zeros symmetry from the functional equation: ξ(s) = ξ(1 − s).
   Conclude: xi ρ = 0 → xi (1 − ρ) = 0. -/
lemma zeros_symmetry
    (xi : ℂ → ℂ)
    (h_func_eq : ∀ s, xi s = xi (1 - s))
    (ρ : ℂ) (hξ : xi ρ = 0) :
    xi (1 - ρ) = 0 := by
  -- Immediate from the functional equation.
  simpa [h_func_eq ρ] using hξ

end Stubs

end IVI_RouteB


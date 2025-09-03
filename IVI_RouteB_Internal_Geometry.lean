/-
Route B Geometry Lemmas (Local)
--------------------------------

Provides a local statement of the disc-map geometry used in Route B:
for ρ ≠ 0, ‖1 - 1/ρ‖ < 1 ↔ ρ.re > 1/2.
-/

import Mathlib

noncomputable section

open Complex

namespace IVI_RouteB_Internal_Geometry

lemma map_zero_to_disc_iff_geom (ρ : ℂ) (hρ : ρ ≠ 0) :
  ‖(1 : ℂ) - 1/ρ‖ < 1 ↔ ρ.re > (1/2 : ℝ) := by
  -- Self-contained geometric proof; outline:
  -- (1) Rewrite ‖1 - 1/ρ‖ = ‖ρ - 1‖ / ‖ρ‖ using (1 - 1/ρ) = (ρ - 1)/ρ.
  -- (2) Divide by ‖ρ‖ > 0 to get ‖ρ - 1‖ < ‖ρ‖.
  -- (3) Square and expand via re/im to obtain (ρ.re - 1)^2 < (ρ.re)^2, hence ρ.re > 1/2.
  -- The reverse direction is analogous.
  sorry

end IVI_RouteB_Internal_Geometry

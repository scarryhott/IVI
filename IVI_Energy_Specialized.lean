import IVI_Energy_Minimal
import IVI_BN_AffineSlice

open Set Metric

section Specialized

universe u v

variable {𝕜 : Type u} [IsROrC 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Core equivalence specialized to the affine slice:
    EnergyZero on `affineSlice V L x₀` is equivalent to the BNApprox condition on `V`.
    Requires a witness `g ∈ V` with `L g ≠ 0` to correct along the slice. -/
theorem IVI_EnergyZero_affineSlice_iff_BNApprox
    (V : Submodule 𝕜 H)
    (L : ContinuousLinearMap 𝕜 H 𝕜)
    (x₀ g : H)
    (hgV : g ∈ (V : Set H))
    (hLg : L g ≠ 0) :
    IVI_EnergyZero (affineSlice V L x₀) x₀ ↔ BNApprox (𝕜:=𝕜) V x₀ := by
  classical
  constructor
  · -- Easy: slice ⊆ V
    intro hEZ ε hε
    obtain ⟨f, hf_slice, hdist⟩ := hEZ hε
    rcases hf_slice with ⟨hfV, _hLf⟩
    -- In a normed group, dist = ‖·‖
    simpa [dist_eq_norm] using And.intro hfV hdist
  · -- Hard: use the abstract approximation theorem on the slice
    intro hBN ε hε
    have h := approx_in_affineSlice_of_BN (𝕜:=𝕜) (H:=H) V L hBN hgV hLg (ε := ε) hε
    rcases h with ⟨f, hf_slice, hnorm⟩
    -- convert ‖x₀ - f‖ < ε to dist x₀ f < ε
    refine ⟨f, hf_slice, ?_⟩
    simpa [dist_eq_norm] using hnorm

/-- ℝ≥0∞-energy specialization on the affine slice. -/
theorem energyEnnreal_zero_iff_BNApprox_affineSlice
    (V : Submodule 𝕜 H)
    (L : ContinuousLinearMap 𝕜 H 𝕜)
    (x₀ g : H)
    (hgV : g ∈ (V : Set H))
    (hLg : L g ≠ 0) :
    IVI_energyEnnreal (affineSlice V L x₀) x₀ = 0 ↔ BNApprox (𝕜:=𝕜) V x₀ := by
  have h₁ := energyEnnreal_zero_iff_IVI_EnergyZero
              (S := affineSlice V L x₀) (x₀ := x₀)
  have h₂ := IVI_EnergyZero_affineSlice_iff_BNApprox (V:=V) (L:=L) (x₀:=x₀)
              (g:=g) hgV hLg
  exact h₁.trans h₂

/-- ℝ-energy specialization on the affine slice, assuming the slice is nonempty. -/
theorem energyReal_zero_iff_BNApprox_affineSlice_of_nonempty
    (V : Submodule 𝕜 H)
    (L : ContinuousLinearMap 𝕜 H 𝕜)
    (x₀ g : H)
    (hgV : g ∈ (V : Set H))
    (hLg : L g ≠ 0)
    (hNE : (affineSlice V L x₀).Nonempty) :
    IVI_energyReal (affineSlice V L x₀) x₀ = 0 ↔ BNApprox (𝕜:=𝕜) V x₀ := by
  have h₁ := energyReal_zero_iff_IVI_EnergyZero_of_nonempty
              (S := affineSlice V L x₀) (x₀ := x₀) hNE
  have h₂ := IVI_EnergyZero_affineSlice_iff_BNApprox (V:=V) (L:=L) (x₀:=x₀)
              (g:=g) hgV hLg
  exact h₁.trans h₂

/-- Handy corollary: in the affine-slice setting, real energy is always ≥ 0. -/
lemma energyReal_nonneg_affineSlice (V : Submodule 𝕜 H)
    (L : ContinuousLinearMap 𝕜 H 𝕜) (x₀ : H) :
    0 ≤ IVI_energyReal (affineSlice V L x₀) x₀ :=
  energyReal_nonneg (S := affineSlice V L x₀) (x₀ := x₀)

/-- Monotonicity for nested slices (if used):
    If `affineSlice V₁ L x₀ ⊆ affineSlice V₂ L x₀`, ℝ≥0∞ energy is monotone. -/
lemma energyEnnreal_mono_affineSlice
    {V₁ V₂ : Submodule 𝕜 H}
    (L : ContinuousLinearMap 𝕜 H 𝕜) (x₀ : H)
    (h : affineSlice V₁ L x₀ ⊆ affineSlice V₂ L x₀) :
    IVI_energyEnnreal (affineSlice V₂ L x₀) x₀
      ≤ IVI_energyEnnreal (affineSlice V₁ L x₀) x₀ :=
  energyEnnreal_mono (S := affineSlice V₁ L x₀) (T := affineSlice V₂ L x₀) (x₀ := x₀) h

end Specialized


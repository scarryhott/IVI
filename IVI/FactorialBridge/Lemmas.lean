/-
IVI/FactorialBridge/Lemmas.lean
Legendre/Kummer/Lucas style lemmas you can cite in factorial_to_community_resonance.
-/
import Mathlib
open scoped BigOperators

noncomputable section

namespace IVI.Factorial

/-- Legendre's formula (mathlib name: `padicValNat_factorial`) -/
lemma legendre_vp_factorial (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (Nat.factorial n) = ∑ k in Finset.Icc 1 (Nat.floor (Real.logb p n)),
      Nat.floor (n / p^k) := by
  -- In mathlib: `padicValNat_factorial` gives `∑ k, ⌊ n / p^k ⌋` over `k≥1`.
  -- You may need to rewrite the finite sum index to a set `{k | p^k ≤ n}`.
  simpa [Finset.Icc, Set.indicator] using padicValNat_factorial p n

/-- Simple Smarandache property (prime detection): S(n)=n for primes (except 4 caveat separately). -/
def smarandache (n : ℕ) : ℕ := Nat.find (fun t => n ∣ Nat.factorial t)

lemma smarandache_prime (p : ℕ) (hp : Nat.Prime p) :
    smarandache p = p := by
  -- With your S(n) definition, this is straightforward:
  -- show minimal t with p ∣ t! is t = p
  -- supply your existing lemma; placeholder proof outline:
  unfold smarandache
  have h1 : p ∣ Nat.factorial p := Nat.dvd_factorial (Nat.Prime.pos hp) (le_refl p)
  have h2 : ∀ t < p, ¬(p ∣ Nat.factorial t) := by
    intro t ht
    -- For t < p, factorial t doesn't contain p as a factor since p is prime
    exact Nat.Prime.not_dvd_factorial hp ht
  exact Nat.find_eq_iff.mpr ⟨h1, h2⟩

end IVI.Factorial

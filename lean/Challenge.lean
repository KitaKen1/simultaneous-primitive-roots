import Mathlib

/-!
# Unconditional variants of simultaneous primitive roots

Independent reference statements for the two proposed FC variants in
`FClikelean/SimultaneousPrimitiveRoots.lean`.
-/

namespace SimultaneousPrimitiveRootsChallenge

theorem simultaneous_primitive_roots_unconditional :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, a.Prime) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / (Real.log x) ^ 2) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

theorem positive_lower_density :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, 2 ≤ a) →
      (∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / Real.log x) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

end SimultaneousPrimitiveRootsChallenge

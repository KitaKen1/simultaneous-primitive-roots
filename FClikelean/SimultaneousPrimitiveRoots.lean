module

public import FormalConjecturesUtil

/-!
# Unconditional variants of simultaneous primitive roots

The conclusion of [OAI26, Theorem 1.1] without its four analytic hypotheses,
and a stronger variant for positive integer bases satisfying the square condition.
The conditional reference formalization is in `OpenAIConditional.lean`.

*References:*
- [OAI26] OpenAI, *Simultaneous primitive roots: a conditional
lower bound for prime bases* (2026), Theorem 1.1.
https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf
- [Ki26] Kenta Kitamura, *Positive Lower Density of Simultaneous Primitive Roots*
  (2026), accompanying Lean formalization.
  https://github.com/KitaKen1/simultaneous-primitive-roots
-/

@[expose] public section

namespace SimultaneousPrimitiveRootsChallenge

/-- The prime-base corollary of [Ki26], with the conclusion of [OAI26, Theorem 1.1]. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/simultaneous-primitive-roots/blob/c4775966844ff78f0488492ee2aef7bd1437c51d/lean/Solution.lean"]
theorem simultaneous_primitive_roots_unconditional :
    ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, a.Prime) →
      ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        c * (x / (Real.log x) ^ 2) ≤
          (Nat.card {p : ℕ // x < (p : ℝ) ∧ (p : ℝ) < 2 * x ∧ p.Prime ∧
            ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1} : ℝ) := by
  sorry

/-- The stronger Lean variant of [Ki26]: positive integer bases satisfying the square
condition, with no external analytic hypotheses and a $c x/\log x$ lower bound. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/simultaneous-primitive-roots/blob/c4775966844ff78f0488492ee2aef7bd1437c51d/lean/Solution.lean"]
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

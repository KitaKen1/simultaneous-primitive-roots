module

public import FormalConjecturesUtil

/-!
# The square obstruction for simultaneous primitive roots

A supplementary necessary condition for simultaneous primitive roots.

*Reference:* [Ki26] Kenta Kitamura, *Positive Lower Density of Simultaneous Primitive Roots*
(2026), accompanying Lean formalization.
https://github.com/KitaKen1/simultaneous-primitive-roots
-/

@[expose] public section

namespace SimultaneousPrimitiveRootsChallenge

/-- The square-condition obstruction of [Ki26]: no odd prime works when it fails. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/simultaneous-primitive-roots/blob/main/lean/Solution.lean"]
theorem square_condition_necessary :
    ∀ A : Finset ℕ,
      ¬ (∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)) →
      ∀ p : ℕ, 2 < p →
        ¬ (p.Prime ∧ ∀ a ∈ A, ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1) := by
  sorry

end SimultaneousPrimitiveRootsChallenge

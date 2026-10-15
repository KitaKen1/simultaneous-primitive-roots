module

public import SimultaneousPrimitiveRoots.Statement
public import Mathlib.Tactic

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- A deliberately coarse cutoff removes every exceptional perfect-power exponent. -/
theorem nat_not_perfect_power_of_exponent_ge {a q : ℕ} (ha : 2 ≤ a) (haq : a ≤ q) :
    ¬ ∃ b : ℕ, b ^ q = a := by
  rintro ⟨b, hb⟩
  have hq : q ≠ 0 := by omega
  have hb2 : 2 ≤ b := by
    by_contra hn
    have hcases : b = 0 ∨ b = 1 := by omega
    rcases hcases with rfl | rfl
    · simp [hq] at hb
      omega
    · simp at hb
      omega
  have hpower : 2 ^ q ≤ b ^ q := Nat.pow_le_pow_left hb2 q
  have hlarge := q.lt_two_pow_self
  omega

theorem no_large_perfect_power_exponents {A : Finset ℕ} {Y : ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hY : ∀ a ∈ A, a ≤ Y) :
    ∀ a ∈ A, ∀ q : ℕ, Y < q → ¬ ∃ b : ℕ, b ^ q = a := by
  intro a ha q hq
  exact nat_not_perfect_power_of_exponent_ge (hpos a ha) (by have := hY a ha; omega)

end SimultaneousPrimitiveRoots

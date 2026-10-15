module

public import SimultaneousPrimitiveRoots.Kummer
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial

theorem exists_small_positive_prime_order {a : ℕ} (ha : 2 ≤ a) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ a ∧ 0 < padicValNat ℓ a ∧ padicValNat ℓ a < a := by
  obtain ⟨ℓ, hprime, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  let : Fact ℓ.Prime := ⟨hprime⟩
  have hpos := one_le_padicValNat_of_dvd (by omega : a ≠ 0) hdvd
  have hbound : ℓ * padicValNat ℓ a ≤ a := by
    have hpow : ℓ ^ padicValNat ℓ a ≤ a := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    exact (Nat.mul_le_pow hprime.ne_one (padicValNat ℓ a)).trans hpow
  have htwo := hprime.two_le
  exact ⟨ℓ, hprime, hdvd, by omega, by nlinarith⟩

/-- Passing from natural to rational roots uses just one prime dividing a. -/
theorem rational_not_perfect_power_of_exponent_gt {a q : ℕ}
    (ha : 2 ≤ a) (haq : a < q) : ∀ b : ℚ, b ^ q ≠ (a : ℚ) := by
  obtain ⟨ℓ, hprime, _, hmpos, hma⟩ := exists_small_positive_prime_order ha
  let : Fact ℓ.Prime := ⟨hprime⟩
  intro b hb
  have horder := congrArg (padicValRat ℓ) hb
  rw [padicValRat.pow, padicValRat.of_nat] at horder
  have hdvd : (q : ℤ) ∣ (padicValNat ℓ a : ℤ) := ⟨padicValRat ℓ b, horder.symm⟩
  have hle := Nat.le_of_dvd hmpos (Int.natCast_dvd_natCast.mp hdvd)
  omega

theorem rational_prime_radical_irreducible {a q : ℕ}
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q) :
    Irreducible ((X : ℚ[X]) ^ q - C (a : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime hq (rational_not_perfect_power_of_exponent_gt ha haq)

end SimultaneousPrimitiveRoots

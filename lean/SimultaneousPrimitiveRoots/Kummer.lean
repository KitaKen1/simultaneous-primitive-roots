module

public import TauCeti.FieldTheory.Kummer.Extension

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial
open scoped IntermediateField WithZero

/-- For a fixed positive valuation order, every larger prime gives an irreducible
radical polynomial. This is the first degree step; cyclotomic base change remains separate. -/
theorem prime_radical_irreducible {F : Type*} [Field F]
    (v : Valuation F ℤᵐ⁰) {a : F} {m q : ℕ}
    (hord : v.ord a = (m : ℤ)) (hm : 0 < m) (hq : q.Prime) (hmq : m < q) :
    Irreducible (X ^ q - C a) := by
  apply v.X_pow_sub_C_irreducible_of_gcd_ord_eq_one hq.ne_zero
  rw [hord]
  simpa only [Int.gcd_natCast_natCast] using (Nat.coprime_of_lt_prime (by omega) hmq hq).gcd_eq_one

theorem prime_radical_degree {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : Valuation F ℤᵐ⁰) {a : F} {y : E} {m q : ℕ}
    (hord : v.ord a = (m : ℤ)) (hm : 0 < m) (hq : q.Prime) (hmq : m < q)
    (hgen : F⟮y⟯ = ⊤) (hroot : y ^ q = algebraMap F E a) :
    Module.finrank F E = q := by
  apply v.finrank_eq_of_pow_eq_of_gcd_ord_eq_one hgen hroot hq.ne_zero
  rw [hord]
  simpa only [Int.gcd_natCast_natCast] using (Nat.coprime_of_lt_prime (by omega) hmq hq).gcd_eq_one

end SimultaneousPrimitiveRoots

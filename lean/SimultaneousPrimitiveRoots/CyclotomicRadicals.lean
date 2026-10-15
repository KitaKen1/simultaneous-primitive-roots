module

public import SimultaneousPrimitiveRoots.RationalRadicals
public import SimultaneousPrimitiveRoots.NormBaseChange
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial
open scoped IntermediateField

theorem prime_cyclotomic_degree {q : ℕ} {E : Type*}
    [Field E] [Algebra ℚ E] [IsCyclotomicExtension {q} ℚ E]
    (hq : q.Prime) : Module.finrank ℚ E = q - 1 := by
  let : NeZero q := ⟨hq.ne_zero⟩
  rw [IsCyclotomicExtension.finrank E (Polynomial.cyclotomic.irreducible_rat hq.pos),
    Nat.totient_prime hq]

/-- Coprimality of q and q-1 replaces a ramification computation. -/
theorem cyclotomic_prime_radical_irreducible {a q : ℕ} {E : Type*}
    [Field E] [CharZero E] [Algebra ℚ E] [IsCyclotomicExtension {q} ℚ E]
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q) :
    Irreducible ((X : E[X]) ^ q - C (a : E)) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : FiniteDimensional ℚ E :=
    IsCyclotomicExtension.finiteDimensional ({q} : Set ℕ) ℚ E
  have hbase : Module.finrank ℚ E = q - 1 := prime_cyclotomic_degree hq
  have hcop : (Module.finrank ℚ E).Coprime q := by
    rw [hbase]
    exact (Nat.coprime_of_lt_prime (by omega) (by omega) hq).symm
  simpa only [map_natCast] using
    prime_radical_irreducible_after_coprime_base_change (F := ℚ) (E := E) hq hcop
      (rational_prime_radical_irreducible ha hq haq)

theorem cyclotomic_radical_relative_degree {a q : ℕ} {E L : Type*}
    [Field E] [CharZero E] [Algebra ℚ E] [IsCyclotomicExtension {q} ℚ E]
    [Field L] [Algebra E L] {y : L}
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q)
    (hgen : E⟮y⟯ = ⊤) (hroot : y ^ q = (a : L)) :
    Module.finrank E L = q := by
  apply radical_extension_degree_of_irreducible hq.ne_zero
    (cyclotomic_prime_radical_irreducible (E := E) ha hq haq) hgen
  simpa only [map_natCast] using hroot

theorem cyclotomic_radical_absolute_degree {a q : ℕ} {E L : Type*}
    [Field E] [CharZero E] [Algebra ℚ E] [IsCyclotomicExtension {q} ℚ E]
    [Field L] [Algebra ℚ L] [Algebra E L] [IsScalarTower ℚ E L] {y : L}
    (ha : 2 ≤ a) (hq : q.Prime) (haq : a < q)
    (hgen : E⟮y⟯ = ⊤) (hroot : y ^ q = (a : L)) :
    Module.finrank ℚ L = q * (q - 1) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : FiniteDimensional ℚ E :=
    IsCyclotomicExtension.finiteDimensional ({q} : Set ℕ) ℚ E
  have hrel := cyclotomic_radical_relative_degree ha hq haq hgen hroot
  let : FiniteDimensional E L := Module.finite_of_finrank_pos (by rw [hrel]; exact hq.pos)
  calc
    Module.finrank ℚ L = Module.finrank ℚ E * Module.finrank E L :=
      (Module.finrank_mul_finrank ℚ E L).symm
    _ = q * (q - 1) := by
      rw [hrel, prime_cyclotomic_degree hq]
      ring

end SimultaneousPrimitiveRoots

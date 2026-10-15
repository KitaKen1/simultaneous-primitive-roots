module

public import SimultaneousPrimitiveRoots.Kummer

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial
open scoped IntermediateField

/-- Norm descent avoids extending valuations to the larger field. -/
theorem not_power_after_coprime_base_change {F E : Type*} [Field F] [Field E]
    [Algebra F E] [FiniteDimensional F E] {a : F} {q : ℕ}
    (hdegree : (Module.finrank F E).Coprime q) (ha : ∀ b : F, b ^ q ≠ a) :
    ∀ b : E, b ^ q ≠ algebraMap F E a := by
  intro b hb
  have hnorm : (Algebra.norm F b) ^ q = a ^ Module.finrank F E := by
    rw [← map_pow, hb, Algebra.norm_algebraMap]
  obtain ⟨c, hc⟩ := (pow_mem_range_pow_of_coprime hdegree a).mp ⟨Algebra.norm F b, hnorm⟩
  exact ha c hc

theorem prime_radical_irreducible_after_coprime_base_change {F E : Type*}
    [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {a : F} {q : ℕ}
    (hq : q.Prime) (hdegree : (Module.finrank F E).Coprime q)
    (hirr : Irreducible ((X : F[X]) ^ q - C a)) :
    Irreducible ((X : E[X]) ^ q - C (algebraMap F E a)) := by
  apply X_pow_sub_C_irreducible_of_prime hq
  exact not_power_after_coprime_base_change hdegree
    ((X_pow_sub_C_irreducible_iff_of_prime hq).mp hirr)

theorem radical_extension_degree_of_irreducible {F E : Type*}
    [Field F] [Field E] [Algebra F E] {a : F} {y : E} {q : ℕ}
    (hq : q ≠ 0) (hirr : Irreducible ((X : F[X]) ^ q - C a))
    (hgen : F⟮y⟯ = ⊤) (hroot : y ^ q = algebraMap F E a) :
    Module.finrank F E = q := by
  have heval : aeval y ((X : F[X]) ^ q - C a) = 0 := by
    rw [map_sub, aeval_X_pow, aeval_C, hroot, sub_self]
  have hint : IsIntegral F y :=
    ⟨(X : F[X]) ^ q - C a, monic_X_pow_sub_C a hq, by rwa [← aeval_def]⟩
  have hmin : (X : F[X]) ^ q - C a = minpoly F y :=
    minpoly.eq_of_irreducible_of_monic hirr heval (monic_X_pow_sub_C a hq)
  rw [← IntermediateField.finrank_top', ← hgen, IntermediateField.adjoin.finrank hint,
    ← hmin, natDegree_X_pow_sub_C]

end SimultaneousPrimitiveRoots

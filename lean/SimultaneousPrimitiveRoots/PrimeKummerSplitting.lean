module

public import SimultaneousPrimitiveRoots.PrimeKummerField
public import Mathlib.FieldTheory.KummerExtension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial

instance primeKummerField_finiteDimensional (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    FiniteDimensional (CyclotomicField q ℚ) (PrimeKummerField a q) :=
  Module.finite_of_finrank_pos (by
    rw [primeKummerField_relative_degree ha.out hq.out haq.out]
    exact hq.out.pos)

instance primeKummerField_instNumberField (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] : NumberField (PrimeKummerField a q) :=
  NumberField.of_module_finite (CyclotomicField q ℚ) _

theorem primeKummerField_numberField (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] : NumberField (PrimeKummerField a q) :=
  inferInstance

theorem primeKummerField_relative_splitting (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    IsSplittingField (CyclotomicField q ℚ) (PrimeKummerField a q)
      (primeRadicalPolynomial a q) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  have hζ : (primitiveRoots q (CyclotomicField q ℚ)).Nonempty :=
    ⟨_, (mem_primitiveRoots hq.out.pos).mpr
      (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ))⟩
  exact isSplittingField_AdjoinRoot_X_pow_sub_C hζ
    (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out)

noncomputable def kummerSplittingPolynomial (a q : ℕ) : ℚ[X] :=
  cyclotomic q ℚ * (X ^ q - C (a : ℚ))

theorem primeKummerField_absolute_splitting (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    IsSplittingField ℚ (PrimeKummerField a q) (kummerSplittingPolynomial a q) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  let : IsSplittingField ℚ (CyclotomicField q ℚ) (cyclotomic q ℚ) := by
    change IsSplittingField ℚ (SplittingField (cyclotomic q ℚ)) (cyclotomic q ℚ)
    infer_instance
  let : IsSplittingField (CyclotomicField q ℚ) (PrimeKummerField a q)
      ((X ^ q - C (a : ℚ)).map (algebraMap ℚ (CyclotomicField q ℚ))) := by
    simpa [primeRadicalPolynomial] using
      primeKummerField_relative_splitting a q
  exact IsSplittingField.mul (K := CyclotomicField q ℚ) (L := PrimeKummerField a q) _ _
    (cyclotomic.irreducible_rat hq.out.pos).ne_zero
    (rational_prime_radical_irreducible ha.out hq.out haq.out).ne_zero

theorem primeKummerField_galois (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    IsGalois ℚ (PrimeKummerField a q) := by
  let : IsSplittingField ℚ (PrimeKummerField a q) (kummerSplittingPolynomial a q) :=
    primeKummerField_absolute_splitting a q
  let : Normal ℚ (PrimeKummerField a q) :=
    Normal.of_isSplittingField (kummerSplittingPolynomial a q)
  exact IsGalois.mk

end SimultaneousPrimitiveRoots

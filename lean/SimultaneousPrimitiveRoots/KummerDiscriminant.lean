module

public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Conductor
public import Mathlib.NumberTheory.KummerDedekind

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial NumberField Algebra

theorem primeKummerField_root_integral (a q : ℕ) (hq : 0 < q) :
    IsIntegral ℤ (AdjoinRoot.root (primeRadicalPolynomial a q)) := by
  apply IsIntegral.of_pow hq
  rw [primeKummerField_root_pow]
  exact isIntegral_natCast (R := ℤ) a

/-- The explicit relative power basis; it is not claimed to be an integral
basis of the whole ring of integers. -/
noncomputable def primeKummerPowerBasis (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    PowerBasis (CyclotomicField q ℚ) (PrimeKummerField a q) :=
  AdjoinRoot.powerBasis (cyclotomic_prime_radical_irreducible ha.out hq.out haq.out).ne_zero

theorem primeKummerPowerBasis_gen (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    (primeKummerPowerBasis a q).gen = AdjoinRoot.root (primeRadicalPolynomial a q) :=
  AdjoinRoot.powerBasis_gen _

theorem primeKummerPowerBasis_dim (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    (primeKummerPowerBasis a q).dim = q := by
  rw [primeKummerPowerBasis, AdjoinRoot.powerBasis_dim, primeRadicalPolynomial,
    natDegree_X_pow_sub_C]

theorem primeKummerPowerBasis_minpoly (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    minpoly (CyclotomicField q ℚ) (primeKummerPowerBasis a q).gen =
      primeRadicalPolynomial a q := by
  exact AdjoinRoot.minpoly_powerBasis_gen_of_monic (monic_X_pow_sub_C _ hq.out.ne_zero)

theorem primeKummerField_root_norm (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    norm (CyclotomicField q ℚ) (AdjoinRoot.root (primeRadicalPolynomial a q)) =
      (a : CyclotomicField q ℚ) := by
  have hodd : Odd q := hq.out.odd_of_ne_two (by have := ha.out; have := haq.out; omega)
  rw [← primeKummerPowerBasis_gen a q, PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    primeKummerPowerBasis_dim, primeKummerPowerBasis_minpoly]
  simp [primeRadicalPolynomial, hq.out.ne_zero.symm, hodd.neg_one_pow]

theorem primeKummer_derivative_norm (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    norm (CyclotomicField q ℚ)
      (aeval (primeKummerPowerBasis a q).gen
        (minpoly (CyclotomicField q ℚ) (primeKummerPowerBasis a q).gen).derivative) =
      (q : CyclotomicField q ℚ) ^ q * (a : CyclotomicField q ℚ) ^ (q - 1) := by
  rw [primeKummerPowerBasis_minpoly]
  change norm (CyclotomicField q ℚ)
    (aeval (primeKummerPowerBasis a q).gen
      ((X : (CyclotomicField q ℚ)[X]) ^ q - C (a : CyclotomicField q ℚ)).derivative) = _
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow]
  simp only [map_mul, map_natCast, map_pow, aeval_X]
  rw [Algebra.norm_natCast,
    primeKummerField_relative_degree ha.out hq.out haq.out,
    primeKummerPowerBasis_gen, primeKummerField_root_norm]

theorem primeKummer_relative_discriminant (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    discr (CyclotomicField q ℚ) (primeKummerPowerBasis a q).basis =
      (-1 : CyclotomicField q ℚ) ^ (q * (q - 1) / 2) *
        ((q : CyclotomicField q ℚ) ^ q * (a : CyclotomicField q ℚ) ^ (q - 1)) := by
  rw [discr_powerBasis_eq_norm,
    primeKummerField_relative_degree ha.out hq.out haq.out,
    primeKummer_derivative_norm]

/-- An explicit denominator for the relative order. Every integral element,
after multiplication by the power-basis discriminant, belongs to O_E[alpha].
This is a conductor witness, not yet the absolute field discriminant bound. -/
theorem primeKummer_discriminant_mul_mem_order (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    (z : 𝓞 (PrimeKummerField a q)) :
    ((-1 : PrimeKummerField a q) ^ (q * (q - 1) / 2) *
      ((q : PrimeKummerField a q) ^ q * (a : PrimeKummerField a q) ^ (q - 1))) *
        (z : PrimeKummerField a q) ∈
      Algebra.adjoin (𝓞 (CyclotomicField q ℚ))
        {AdjoinRoot.root (primeRadicalPolynomial a q)} := by
  have hgen : IsIntegral (𝓞 (CyclotomicField q ℚ)) (primeKummerPowerBasis a q).gen := by
    rw [primeKummerPowerBasis_gen]
    exact (primeKummerField_root_integral a q hq.out.pos).tower_top
  have hz : IsIntegral (𝓞 (CyclotomicField q ℚ)) (z : PrimeKummerField a q) :=
    (RingOfIntegers.isIntegral_coe z).tower_top
  have h := discr_mul_isIntegral_mem_adjoin (K := CyclotomicField q ℚ) hgen hz
  rw [primeKummer_relative_discriminant, primeKummerPowerBasis_gen] at h
  simpa only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast] using h

theorem primeKummer_denominator_mul_mem_order (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (z : 𝓞 (PrimeKummerField a q)) :
    (((q ^ q * a ^ (q - 1) : ℕ) : PrimeKummerField a q) * (z : PrimeKummerField a q)) ∈
      Algebra.adjoin (𝓞 (CyclotomicField q ℚ))
        {AdjoinRoot.root (primeRadicalPolynomial a q)} := by
  have h := primeKummer_discriminant_mul_mem_order a q z
  rcases Nat.even_or_odd (q * (q - 1) / 2) with heven | hodd
  · simpa only [heven.neg_one_pow, one_mul, Nat.cast_mul, Nat.cast_pow] using h
  · have hn := (Algebra.adjoin (𝓞 (CyclotomicField q ℚ))
      {AdjoinRoot.root (primeRadicalPolynomial a q)}).neg_mem h
    simpa only [hodd.neg_one_pow, neg_one_mul, neg_mul, neg_neg, one_mul,
      Nat.cast_mul, Nat.cast_pow] using hn

theorem primeKummer_denominator_coprime {a p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (ha : 2 ≤ a) (haq : a < q) (hqp : q ∣ p - 1) :
    p.Coprime (q ^ q * a ^ (q - 1)) := by
  have hqle : q ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hqp
  have hpnq : ¬ p ∣ q := Nat.not_dvd_of_pos_of_lt hq.pos (by omega)
  have hpna : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  exact ((hp.coprime_iff_not_dvd.mpr hpnq).pow_right q).mul_right
    ((hp.coprime_iff_not_dvd.mpr hpna).pow_right (q - 1))

noncomputable def primeKummerInteger (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    𝓞 (PrimeKummerField a q) :=
  ⟨AdjoinRoot.root (primeRadicalPolynomial a q), primeKummerField_root_integral a q hq.out.pos⟩

theorem primeKummer_denominator_mem_conductor (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    ((q ^ q * a ^ (q - 1) : ℕ) : 𝓞 (PrimeKummerField a q)) ∈
      conductor (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q) := by
  have h : ((q ^ q * a ^ (q - 1) : ℕ) : PrimeKummerField a q) ∈
      IsLocalization.coeSubmodule (PrimeKummerField a q)
        (conductor (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q)) := by
    apply mem_coeSubmodule_conductor.mpr
    intro z
    exact primeKummer_denominator_mul_mem_order a q z
  obtain ⟨z, hz, heq⟩ := (IsLocalization.mem_coeSubmodule _ _).mp h
  have heq' : z = ((q ^ q * a ^ (q - 1) : ℕ) : 𝓞 (PrimeKummerField a q)) :=
    RingOfIntegers.coe_injective (heq.trans (map_natCast _ _).symm)
  exact heq' ▸ hz

theorem primeKummer_conductor_coprime_of_contains_prime {a p q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    (hp : p.Prime) (hqp : q ∣ p - 1)
    (I : Ideal (𝓞 (CyclotomicField q ℚ))) (hI : (p : 𝓞 (CyclotomicField q ℚ)) ∈ I) :
    (conductor (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q)).comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) ⊔ I = ⊤ := by
  have hD : ((q ^ q * a ^ (q - 1) : ℕ) : 𝓞 (CyclotomicField q ℚ)) ∈
      (conductor (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q)).comap
        (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) := by
    rw [Ideal.mem_comap, map_natCast]
    exact primeKummer_denominator_mem_conductor a q
  have hc : IsCoprime ((q ^ q * a ^ (q - 1) : ℕ) : 𝓞 (CyclotomicField q ℚ))
      (p : 𝓞 (CyclotomicField q ℚ)) :=
    (primeKummer_denominator_coprime hp hq.out ha.out haq.out hqp).symm.cast
  apply top_unique
  rw [← Ideal.sup_eq_top_iff_isCoprime _ _ |>.mpr hc]
  exact sup_le_sup (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hD))
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hI))

theorem primeKummerInteger_relative_minpoly (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    minpoly (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q) =
      X ^ q - C (a : 𝓞 (CyclotomicField q ℚ)) := by
  rw [← minpoly.algebraMap_eq (B' := PrimeKummerField a q)
    RingOfIntegers.coe_injective (primeKummerInteger a q)]
  apply Polynomial.map_injective
    (algebraMap (𝓞 (CyclotomicField q ℚ)) (CyclotomicField q ℚ))
    (RingOfIntegers.coe_injective (K := CyclotomicField q ℚ))
  change Polynomial.map (algebraMap (𝓞 (CyclotomicField q ℚ)) (CyclotomicField q ℚ))
    (minpoly (𝓞 (CyclotomicField q ℚ)) (AdjoinRoot.root (primeRadicalPolynomial a q))) = _
  have hint : IsIntegral (𝓞 (CyclotomicField q ℚ))
      (AdjoinRoot.root (primeRadicalPolynomial a q)) :=
    (primeKummerField_root_integral a q hq.out.pos).tower_top
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' (R := 𝓞 (CyclotomicField q ℚ))
    (CyclotomicField q ℚ) hint]
  change minpoly (CyclotomicField q ℚ) (AdjoinRoot.root (primeRadicalPolynomial a q)) = _
  rw [← primeKummerPowerBasis_gen a q, primeKummerPowerBasis_minpoly]
  simp [primeRadicalPolynomial]

/-- The actual residue ring of O_K is modeled by the relative radical
polynomial at every base ideal containing a good rational prime. Identifying
the base residue field with F_p and counting primes in the tower comes next. -/
theorem primeKummer_residue_model {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (hp : p.Prime) (hqp : q ∣ p - 1)
    (I : Ideal (𝓞 (CyclotomicField q ℚ))) (hI : (p : 𝓞 (CyclotomicField q ℚ)) ∈ I) :
    Nonempty ((𝓞 (PrimeKummerField a q) ⧸
      I.map (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)))) ≃+*
        ((𝓞 (CyclotomicField q ℚ) ⧸ I)[X] ⧸ Ideal.span
          {((X : (𝓞 (CyclotomicField q ℚ))[X]) ^ q - C (a : 𝓞 (CyclotomicField q ℚ))).map
            (Ideal.Quotient.mk I)})) := by
  have hint : IsIntegral (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q) :=
    (RingOfIntegers.isIntegral (primeKummerInteger a q)).tower_top
  have e := KummerDedekind.quotMapEquivQuotQuotMap
    (primeKummer_conductor_coprime_of_contains_prime hp hqp I hI) hint
  rw [primeKummerInteger_relative_minpoly] at e
  exact ⟨e⟩

end SimultaneousPrimitiveRoots

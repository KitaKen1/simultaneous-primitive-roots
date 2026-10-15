module

public import SimultaneousPrimitiveRoots.KummerDiscriminant
public import SimultaneousPrimitiveRoots.CyclotomicPrimeSplitting
public import SimultaneousPrimitiveRoots.PolynomialFactorCount
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial NumberField Ideal UniqueFactorizationMonoid
open scoped IntermediateField

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

theorem cyclotomic_prime_inertia_degree_one {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero q]
    (P : Ideal (𝓞 (CyclotomicField q ℚ))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hqp : q ∣ p - 1) : P.inertiaDeg ℤ = 1 := by
  have hqlt : q < p := by
    have hp2 := hp.out.two_le
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p (CyclotomicField q ℚ) P
    (Nat.not_dvd_of_pos_of_lt hq.out.pos hqlt)]
  have hz : (p : ZMod q) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (p - 1) q).mpr hqp
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one, sub_eq_zero] at h
    exact h
  rw [hz, orderOf_one]

theorem cyclotomic_prime_unramified {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero q]
    (P : Ideal (𝓞 (CyclotomicField q ℚ))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hqp : q ∣ p - 1) : P.ramificationIdx ℤ = 1 := by
  have hqlt : q < p := by
    have hp2 := hp.out.two_le
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p (CyclotomicField q ℚ) P
    (Nat.not_dvd_of_pos_of_lt hq.out.pos hqlt)

/-- Every base prime in the completely split cyclotomic layer has residue
field F_p. The equivalence is obtained from inertia degree one. -/
theorem cyclotomic_prime_residue_equiv {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] [NeZero q]
    (P : Ideal (𝓞 (CyclotomicField q ℚ))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hqp : q ∣ p - 1) : Nonempty ((𝓞 (CyclotomicField q ℚ) ⧸ P) ≃+* ZMod p) := by
  let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  let := Ideal.Quotient.algebraOfLiesOver P (span {(p : ℤ)})
  have hd : Module.finrank (ℤ ⧸ span {(p : ℤ)}) (𝓞 (CyclotomicField q ℚ) ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal (span {(p : ℤ)}) P]
    exact cyclotomic_prime_inertia_degree_one P hqp
  exact ⟨(RingEquiv.ofBijective (algebraMap (ℤ ⧸ span {(p : ℤ)})
    (𝓞 (CyclotomicField q ℚ) ⧸ P))
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)).symm.trans
      (Int.quotientSpanNatEquivZMod p)⟩

theorem normalizedFactors_card_map_ringEquiv {F G : Type*} [Field F] [Field G]
    [DecidableEq F] [DecidableEq G]
    (e : F ≃+* G) (f : F[X]) :
    (normalizedFactors f).toFinset.card = (normalizedFactors (f.map e.toRingHom)).toFinset.card := by
  classical
  let ef := normalizedFactorsEquiv (f := Polynomial.mapEquiv e)
    (fun g => (Polynomial.map_normalize g e.toRingHom).symm) f
  let ef' : (normalizedFactors f).toFinset ≃ (normalizedFactors (f.map e.toRingHom)).toFinset :=
    (Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset)).trans
      (ef.trans (Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset.symm)))
  simpa only [Fintype.card_coe] using Fintype.card_congr ef'

/-- Count the actual primes in the relative radical extension by factoring
X^q-a over F_p. No absolute primitive integral generator is needed. -/
theorem primeKummer_relative_primes_count {a p q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    [hp : Fact p.Prime] [NeZero q]
    (P : Ideal (𝓞 (CyclotomicField q ℚ))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hqp : q ∣ p - 1) :
    (P.primesOver (𝓞 (PrimeKummerField a q))).ncard =
      (normalizedFactors (X ^ q - C (a : ZMod p))).toFinset.card := by
  classical
  let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (span {(p : ℤ)})
  have hpP : (p : 𝓞 (CyclotomicField q ℚ)) ∈ P := by
    rw [← map_natCast (algebraMap ℤ (𝓞 (CyclotomicField q ℚ))) p, ← Ideal.mem_under,
      ← Ideal.over_def P (span {(p : ℤ)})]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hP0 : P ≠ ⊥ := by
    intro h
    have hz : (p : 𝓞 (CyclotomicField q ℚ)) = 0 := by simpa [h] using hpP
    exact hp.out.ne_zero (by exact_mod_cast hz)
  have hint : IsIntegral (𝓞 (CyclotomicField q ℚ)) (primeKummerInteger a q) :=
    (RingOfIntegers.isIntegral (primeKummerInteger a q)).tower_top
  let ek := (Equiv.setCongr (by
    ext J
    exact Ideal.mem_primesOver_iff_mem_normalizedFactors _ hP0)).trans
      (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        (inferInstance : P.IsMaximal) hP0
        (primeKummer_conductor_coprime_of_contains_prime hp.out hqp P hpP) hint)
  have hc := Nat.card_congr ek
  rw [primeKummerInteger_relative_minpoly] at hc
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    map_natCast, Polynomial.map_natCast] at hc
  have hc' : (P.primesOver (𝓞 (PrimeKummerField a q))).ncard =
      (normalizedFactors (X ^ q - C (a : 𝓞 (CyclotomicField q ℚ) ⧸ P))).toFinset.card := by
    rw [← Nat.card_coe_set_eq]
    refine hc.trans ?_
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Multiset.mem_toFinset.symm)) |>.trans
      (Nat.card_eq_finsetCard _)
  obtain ⟨e⟩ := cyclotomic_prime_residue_equiv P hqp
  have he := normalizedFactors_card_map_ringEquiv e
    (X ^ q - C (a : 𝓞 (CyclotomicField q ℚ) ⧸ P))
  change (normalizedFactors (X ^ q - C (a : 𝓞 (CyclotomicField q ℚ) ⧸ P))).toFinset.card =
    (normalizedFactors ((X ^ q - C (a : 𝓞 (CyclotomicField q ℚ) ⧸ P)).map e.toRingHom)).toFinset.card at he
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    map_natCast, Polynomial.map_natCast] at he
  exact hc'.trans he

/-- The Galois tower multiplies the q-1 base primes by the number of distinct
irreducible radical factors over F_p. -/
theorem primeKummer_primes_count {a p q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    [hp : Fact p.Prime] (hqp : q ∣ p - 1) :
    ((span {(p : ℤ)}).primesOver (𝓞 (PrimeKummerField a q))).ncard =
      (q - 1) * (normalizedFactors (X ^ q - C (a : ZMod p))).toFinset.card := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  let : IsGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  obtain ⟨⟨P, hP, hPl⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver
    (S := 𝓞 (CyclotomicField q ℚ))
  let : P.IsPrime := hP
  let : P.LiesOver (span {(p : ℤ)}) := hPl
  have ht := Ideal.ncard_primesOver_mul_ncard_primesOver
    (p := (span {(p : ℤ)}))
    P Gal((CyclotomicField q ℚ)/ℚ) (𝓞 (PrimeKummerField a q)) Gal((PrimeKummerField a q)/ℚ)
  have hpq : p ≠ q := by
    have hp2 := hp.out.two_le
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  rw [(cyclotomic_prime_splitsCompletely_iff hp.out hq.out hpq).mpr hqp,
    prime_cyclotomic_degree hq.out, primeKummer_relative_primes_count P hqp] at ht
  exact ht.symm

/-- The power-residue test is now equivalent to complete splitting of the
actual number field, under q | p-1. -/
theorem primeKummer_prime_splitsCompletely_iff {a p q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    [hp : Fact p.Prime] (hqp : q ∣ p - 1) :
    ((span {(p : ℤ)}).primesOver (𝓞 (PrimeKummerField a q))).ncard =
      Module.finrank ℚ (PrimeKummerField a q) ↔
        (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  have hqlt : q < p := by
    have hp2 := hp.out.two_le
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
    omega
  have hpa : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt (by have := ha.out; omega)
    (by have := haq.out; omega)
  rw [primeKummer_primes_count hqp, primeKummerField_absolute_degree ha.out hq.out haq.out,
    Nat.mul_comm q (q - 1), Nat.mul_left_cancel_iff (by have := hq.out.two_le; omega : 0 < q - 1)]
  exact radical_normalizedFactors_card_eq_iff hq.out.pos hqp hpa

/-- Complete splitting forces both the ramification index and residue degree
to be one; this certifies the ideal-count interpretation used above. -/
theorem primeKummer_splitting_indices_eq_one {a p q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    [Fact p.Prime] (hqp : q ∣ p - 1)
    (hpow : (a : ZMod p) ^ ((p - 1) / q) = 1) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 (PrimeKummerField a q)) = 1 ∧
      (span {(p : ℤ)}).inertiaDegIn (𝓞 (PrimeKummerField a q)) = 1 := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 (PrimeKummerField a q)) Gal((PrimeKummerField a q)/ℚ)
  rw [(primeKummer_prime_splitsCompletely_iff hqp).mpr hpow,
    IsGaloisGroup.card_eq_finrank Gal((PrimeKummerField a q)/ℚ) ℚ (PrimeKummerField a q)] at hf
  have hn : 0 < Module.finrank ℚ (PrimeKummerField a q) := by
    rw [primeKummerField_absolute_degree ha.out hq.out haq.out]
    have hq2 := hq.out.two_le
    exact Nat.mul_pos hq.out.pos (by omega)
  have he : (span {(p : ℤ)}).ramificationIdxIn (𝓞 (PrimeKummerField a q)) *
      (span {(p : ℤ)}).inertiaDegIn (𝓞 (PrimeKummerField a q)) = 1 := by
    apply (Nat.mul_left_cancel_iff hn).mp
    simpa only [Nat.mul_one] using hf
  have hr : 0 < (span {(p : ℤ)}).ramificationIdxIn (𝓞 (PrimeKummerField a q)) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    simp only [hzero, Nat.zero_mul] at he
    omega
  have hi : 0 < (span {(p : ℤ)}).inertiaDegIn (𝓞 (PrimeKummerField a q)) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    simp only [hzero, Nat.mul_zero] at he
    omega
  constructor <;> nlinarith

end SimultaneousPrimitiveRoots

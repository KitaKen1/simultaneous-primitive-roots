module

public import SimultaneousPrimitiveRoots.FiniteFieldKummer
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-- Count actual prime ideals using the Kummer--Dedekind equivalence. The
conductor condition is retained; a splitting polynomial is not a minpoly. -/
theorem primesOver_card_eq_monicFactors {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ exponent θ) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = (monicFactorsMod θ p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp)]
  exact Nat.card_eq_finsetCard _

/-- The canonical integral primitive root of unity. -/
noncomputable def cyclotomicInteger (q : ℕ) [NeZero q] [Fact q.Prime] : 𝓞 (CyclotomicField q ℚ) :=
  (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).toInteger

theorem cyclotomicInteger_minpoly (q : ℕ) [NeZero q] [Fact q.Prime] :
    minpoly ℤ (cyclotomicInteger q) = cyclotomic q ℤ := by
  rw [← minpoly.algebraMap_eq (B' := CyclotomicField q ℚ)
    RingOfIntegers.coe_injective (cyclotomicInteger q)]
  exact (cyclotomic_eq_minpoly
    (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)) (NeZero.pos q)).symm

theorem cyclotomicInteger_exponent (q : ℕ) [NeZero q] [Fact q.Prime] :
    exponent (cyclotomicInteger q) = 1 := by
  apply exponent_eq_one_iff.mpr
  simpa only [IsPrimitiveRoot.integralPowerBasis_gen, cyclotomicInteger] using
    (IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).integralPowerBasis.adjoin_gen_eq_top

theorem cyclotomic_primesOver_card (q p : ℕ) [NeZero q] [Fact q.Prime] [Fact p.Prime] :
    (primesOver (span {(p : ℤ)}) (𝓞 (CyclotomicField q ℚ))).ncard =
      (normalizedFactors (cyclotomic q (ZMod p))).toFinset.card := by
  rw [primesOver_card_eq_monicFactors (cyclotomicInteger q)
    (by rw [cyclotomicInteger_exponent]; exact (Fact.out : p.Prime).not_dvd_one)]
  simp only [monicFactorsMod, cyclotomicInteger_minpoly, map_cyclotomic]

theorem cyclotomic_primeIdeals_count_order (q p : ℕ)
    [NeZero q] [hq : Fact q.Prime] [Fact p.Prime] (hc : p.Coprime q) :
    (primesOver (span {(p : ℤ)}) (𝓞 (CyclotomicField q ℚ))).ncard =
      (q - 1) / orderOf (ZMod.unitOfCoprime p hc) := by
  rw [cyclotomic_primesOver_card]
  simpa only [Nat.totient_prime hq.out, pow_one] using
    (normalizedFactors_cyclotomic_card (K := ZMod p) (f := 1) (n := q)
      (by simp) hc)

theorem unitOfCoprime_eq_one_iff_dvd_sub_one {p q : ℕ} (hp : 1 ≤ p)
    (hc : p.Coprime q) : ZMod.unitOfCoprime p hc = 1 ↔ q ∣ p - 1 := by
  constructor
  · intro h
    have hcast : (p : ZMod q) = 1 := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h
    apply (ZMod.natCast_eq_zero_iff (p - 1) q).mp
    rw [Nat.cast_sub hp, Nat.cast_one, hcast, sub_self]
  · intro h
    apply Units.ext
    change (p : ZMod q) = 1
    have hz := (ZMod.natCast_eq_zero_iff (p - 1) q).mpr h
    rw [Nat.cast_sub hp, Nat.cast_one, sub_eq_zero] at hz
    exact hz

/-- This is complete splitting in the ring of integers, not merely splitting
of a polynomial. It closes the cyclotomic part of the Kummer tower. -/
theorem cyclotomic_prime_splitsCompletely_iff {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (primesOver (span {(p : ℤ)}) (𝓞 (CyclotomicField q ℚ))).ncard =
      Module.finrank ℚ (CyclotomicField q ℚ) ↔ q ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr (by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h | h
    · exact hp.ne_one h
    · exact hpq h)
  rw [cyclotomic_primeIdeals_count_order q p hc, prime_cyclotomic_degree hq]
  constructor
  · intro h
    have ho : orderOf (ZMod.unitOfCoprime p hc) = 1 := by
      have hpos := orderOf_pos (ZMod.unitOfCoprime p hc)
      by_contra hne
      have hgt : 1 < orderOf (ZMod.unitOfCoprime p hc) := by omega
      have hlt := Nat.div_lt_self (by have := hq.two_le; omega : 0 < q - 1) hgt
      omega
    exact (unitOfCoprime_eq_one_iff_dvd_sub_one hp.one_le hc).mp
      (orderOf_eq_one_iff.mp ho)
  · intro h
    have hu := (unitOfCoprime_eq_one_iff_dvd_sub_one hp.one_le hc).mpr h
    simp only [hu, orderOf_one, Nat.div_one]

theorem cyclotomic_prime_splitsCompletely_iff_polynomial {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (primesOver (span {(p : ℤ)}) (𝓞 (CyclotomicField q ℚ))).ncard =
      Module.finrank ℚ (CyclotomicField q ℚ) ↔ (cyclotomic q (ZMod p)).Splits := by
  rw [cyclotomic_prime_splitsCompletely_iff hp hq hpq,
    cyclotomic_mod_splits_iff hp hq hpq]

end SimultaneousPrimitiveRoots

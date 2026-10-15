module

public import SimultaneousPrimitiveRoots.CandidateSets
public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial

/-- A power test gives polynomial divisibility, without choosing a generator of
the multiplicative group or computing a discrete logarithm. -/
theorem radical_dvd_fermatPolynomial {F : Type*} [CommRing F] {n q : ℕ}
    {a : F} (hqn : q ∣ n) (ha : a ^ (n / q) = 1) :
    (X ^ q - C a : F[X]) ∣ X ^ n - 1 := by
  have h := sub_dvd_pow_sub_pow (X ^ q : F[X]) (C a) (n / q)
  simpa only [← pow_mul, Nat.mul_div_cancel' hqn, ← C_pow, ha, C_1] using h

theorem radical_dvd_frobeniusPolynomial {F : Type*} [CommRing F] {p q : ℕ}
    {a : F} (hp : 0 < p) (hqp : q ∣ p - 1) (ha : a ^ ((p - 1) / q) = 1) :
    (X ^ q - C a : F[X]) ∣ X ^ p - X := by
  have h := dvd_mul_of_dvd_right (radical_dvd_fermatPolynomial hqp ha) (X : F[X])
  simpa only [mul_sub, ← pow_succ', Nat.sub_add_cancel hp, mul_one] using h

/-- For q dividing p-1, splitting of the radical polynomial over F_p is exactly
the power-residue test used by the exceptional-prime set. -/
theorem powerResidue_iff_radical_splits {a p q : ℕ} (hp : p.Prime)
    (hq : 0 < q) (hqp : q ∣ p - 1) (ha : ¬ p ∣ a) :
    (a : ZMod p) ^ ((p - 1) / q) = 1 ↔
      (X ^ q - C (a : ZMod p)).Splits := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hpow
    have hf : (X ^ p - X : (ZMod p)[X]).Splits := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (splits_X_pow_nat_card_sub_X (K := ZMod p))
    exact hf.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hp.one_lt)
      (radical_dvd_frobeniusPolynomial hp.pos hqp hpow)
  · intro hs
    obtain ⟨b, hb⟩ := hs.exists_eval_eq_zero (by
      rw [degree_X_pow_sub_C hq]
      exact_mod_cast hq.ne')
    have hbpow : b ^ q = (a : ZMod p) := by
      simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hb
    have hbne : b ≠ 0 := by
      intro hzero
      apply ha
      apply (ZMod.natCast_eq_zero_iff a p).mp
      simpa only [hzero, zero_pow hq.ne'] using hbpow.symm
    rw [← hbpow, ← pow_mul, Nat.mul_div_cancel' hqp]
    exact ZMod.pow_card_sub_one_eq_one hbne

theorem powerResidue_iff_exists_radical_root {a p q : ℕ} (hp : p.Prime)
    (hq : 0 < q) (hqp : q ∣ p - 1) (ha : ¬ p ∣ a) :
    (a : ZMod p) ^ ((p - 1) / q) = 1 ↔ ∃ b : ZMod p, b ^ q = (a : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hpow
    obtain ⟨b, hb⟩ := ((powerResidue_iff_radical_splits hp hq hqp ha).mp hpow).exists_eval_eq_zero
      (by rw [degree_X_pow_sub_C hq]; exact_mod_cast hq.ne')
    exact ⟨b, by simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hb⟩
  · rintro ⟨b, hb⟩
    have hbne : b ≠ 0 := by
      intro hzero
      apply ha
      apply (ZMod.natCast_eq_zero_iff a p).mp
      simpa only [hzero, zero_pow hq.ne'] using hb.symm
    rw [← hb, ← pow_mul, Nat.mul_div_cancel' hqp]
    exact ZMod.pow_card_sub_one_eq_one hbne

theorem radical_mod_separable {a p q : ℕ} (hp : p.Prime) (hq : 0 < q)
    (hqp : q ∣ p - 1) (ha : ¬ p ∣ a) :
    (X ^ q - C (a : ZMod p)).Separable := by
  let : Fact p.Prime := ⟨hp⟩
  have hqle : q ≤ p - 1 := Nat.le_of_dvd (by have := hp.two_le; omega) hqp
  have hpq : ¬ p ∣ q := Nat.not_dvd_of_pos_of_lt hq (by omega)
  exact separable_X_pow_sub_C' p q (a : ZMod p) hpq
    (fun hz => ha ((ZMod.natCast_eq_zero_iff a p).mp hz))

theorem radical_mod_roots_card {a p q : ℕ} [Fact p.Prime] (hq : 0 < q)
    (hqp : q ∣ p - 1) (ha : ¬ p ∣ a)
    (hpow : (a : ZMod p) ^ ((p - 1) / q) = 1) :
    (X ^ q - C (a : ZMod p)).roots.toFinset.card = q := by
  have hp : p.Prime := Fact.out
  classical
  rw [Multiset.toFinset_card_of_nodup (nodup_roots (radical_mod_separable hp hq hqp ha)),
    ← ((powerResidue_iff_radical_splits hp hq hqp ha).mp hpow).natDegree_eq_card_roots,
    natDegree_X_pow_sub_C]

/-- The two factors are coprime unless a=1 in the residue field. This explicit
Bezout identity will be used before applying a field-splitting criterion. -/
theorem cyclotomic_radical_isCoprime {F : Type*} [Field F] (q : ℕ) {a : F}
    (ha : a ≠ 1) : IsCoprime (cyclotomic q F) (X ^ q - C a) := by
  have hane : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have hc : IsCoprime (X ^ q - 1 : F[X]) (X ^ q - C a) := by
    refine ⟨C ((a - 1)⁻¹), -C ((a - 1)⁻¹), ?_⟩
    calc
      C ((a - 1)⁻¹) * (X ^ q - 1) + -C ((a - 1)⁻¹) * (X ^ q - C a) =
          C ((a - 1)⁻¹ * (a - 1)) := by
        rw [C_mul, C_sub, C_1]
        ring
      _ = 1 := by rw [inv_mul_cancel₀ hane, C_1]
  exact hc.of_isCoprime_of_dvd_left (cyclotomic.dvd_X_pow_sub_one q F)

theorem cyclotomic_mod_splits_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (cyclotomic q (ZMod p)).Splits ↔ q ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpndq : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq).mp h with h | h
    · exact hp.ne_one h
    · exact hpq h
  let : NeZero (q : ZMod p) := ⟨fun hz => hpndq ((ZMod.natCast_eq_zero_iff q p).mp hz)⟩
  constructor
  · intro hs
    obtain ⟨ζ, hζ⟩ := hs.exists_eval_eq_zero (by
      rw [degree_eq_natDegree (cyclotomic_ne_zero q (ZMod p)), natDegree_cyclotomic,
        Nat.totient_prime hq]
      exact_mod_cast (by have := hq.two_le; omega : q - 1 ≠ 0))
    have hprim : IsPrimitiveRoot ζ q := isRoot_cyclotomic_iff.mp hζ
    rw [hprim.eq_orderOf]
    exact ZMod.orderOf_dvd_card_sub_one (hprim.ne_zero hq.ne_zero)
  · intro hqp
    have hf : (X ^ p - X : (ZMod p)[X]).Splits := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (splits_X_pow_nat_card_sub_X (K := ZMod p))
    apply hf.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hp.one_lt)
    exact (cyclotomic.dvd_X_pow_sub_one q (ZMod p)).trans
      (by simpa only [C_1] using
        radical_dvd_frobeniusPolynomial (a := (1 : ZMod p)) hp.pos hqp (by simp))

/-- An integral model is required for reduction modulo a prime: there is no
ring homomorphism from Q to F_p. Its rational image is the splitting polynomial. -/
noncomputable def integralKummerPolynomial (a q : ℕ) : ℤ[X] :=
  cyclotomic q ℤ * (X ^ q - C (a : ℤ))

theorem integralKummerPolynomial_rat_map (a q : ℕ) :
    (integralKummerPolynomial a q).map (Int.castRingHom ℚ) =
      kummerSplittingPolynomial a q := by
  simp [integralKummerPolynomial, kummerSplittingPolynomial, map_cyclotomic]

theorem integralKummerPolynomial_mod_map (a q p : ℕ) :
    (integralKummerPolynomial a q).map (Int.castRingHom (ZMod p)) =
      cyclotomic q (ZMod p) * (X ^ q - C (a : ZMod p)) := by
  simp [integralKummerPolynomial, map_cyclotomic]

theorem integralKummerPolynomial_monic {a q : ℕ} (hq : 0 < q) :
    (integralKummerPolynomial a q).Monic :=
  (cyclotomic.monic q ℤ).mul (monic_X_pow_sub_C (a : ℤ) hq.ne')

theorem integralKummerPolynomial_natDegree {a q : ℕ} (hq : q.Prime) :
    (integralKummerPolynomial a q).natDegree = q + (q - 1) := by
  rw [integralKummerPolynomial,
    natDegree_mul (cyclotomic_ne_zero q ℤ) (X_pow_sub_C_ne_zero hq.pos _),
    natDegree_cyclotomic, Nat.totient_prime hq, natDegree_X_pow_sub_C]
  omega

theorem integralKummer_mod_separable {a p q : ℕ} (hp : p.Prime) (ha : 2 ≤ a)
    (hq : q.Prime) (haq : a < q) (hqp : q ∣ p - 1) :
    ((integralKummerPolynomial a q).map (Int.castRingHom (ZMod p))).Separable := by
  let : Fact p.Prime := ⟨hp⟩
  have hpge := hp.two_le
  have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqp
  have haq' : a < p := by omega
  have hpna : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt (by omega) haq'
  have hpnq : ¬ p ∣ q := Nat.not_dvd_of_pos_of_lt hq.pos (by omega)
  let : NeZero (q : ZMod p) := ⟨fun hz => hpnq ((ZMod.natCast_eq_zero_iff q p).mp hz)⟩
  have hane : (a : ZMod p) ≠ 1 := by
    intro hone
    have hz : ((a - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, hone, sub_self]
    have hdvd := (ZMod.natCast_eq_zero_iff (a - 1) p).mp hz
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hdvd
  rw [integralKummerPolynomial_mod_map]
  exact (separable_cyclotomic q (ZMod p)).mul (radical_mod_separable hp hq.pos hqp hpna)
    (cyclotomic_radical_isCoprime q hane)

theorem powerResidue_iff_integralKummer_splits {a p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (ha : ¬ p ∣ a) :
    (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) ↔
      ((integralKummerPolynomial a q).map (Int.castRingHom (ZMod p))).Splits := by
  let : Fact p.Prime := ⟨hp⟩
  rw [integralKummerPolynomial_mod_map,
    splits_mul (cyclotomic_ne_zero q (ZMod p)) (X_pow_sub_C_ne_zero hq.pos _),
    cyclotomic_mod_splits_iff hp hq hpq]
  exact and_congr_right fun hqp => powerResidue_iff_radical_splits hp hq.pos hqp ha

/-- The exact dyadic exception set, expressed by complete splitting of an
integral polynomial over F_p. Splitting of prime ideals is a subsequent step. -/
noncomputable def polynomialSplitExceptionPrimes (a q : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ ¬ p ∣ a ∧ p ≠ q ∧
      ((integralKummerPolynomial a q).map (Int.castRingHom (ZMod p))).Splits

theorem powerResidueExceptionPrimes_eq_polynomialSplit {a q : ℕ} (hq : q.Prime) (x : ℝ) :
    powerResidueExceptionPrimes a q x = polynomialSplitExceptionPrimes a q x := by
  classical
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hp, hpx, hp2x, ha, hqp, hpow⟩
    have hpq : p ≠ q := by
      intro h
      subst q
      have hpge := hp.two_le
      have := Nat.le_of_dvd (by have := hp.two_le; omega : 0 < p - 1) hqp
      omega
    exact ⟨hp, hpx, hp2x, ha, hpq,
      (powerResidue_iff_integralKummer_splits hp hq hpq ha).mp ⟨hqp, hpow⟩⟩
  · rintro ⟨hp, hpx, hp2x, ha, hpq, hs⟩
    obtain ⟨hqp, hpow⟩ := (powerResidue_iff_integralKummer_splits hp hq hpq ha).mpr hs
    exact ⟨hp, hpx, hp2x, ha, hqp, hpow⟩

end SimultaneousPrimitiveRoots

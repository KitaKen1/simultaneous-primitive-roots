module

public import SimultaneousPrimitiveRoots.ProgressionSelbergDenominator
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset
open scoped ArithmeticFunction.omega
noncomputable section
open Classical

theorem sieveLevel_ceil_one_le {y : ℝ} (hy : 1 ≤ y) : 1 ≤ Nat.ceil y := by
  exact_mod_cast hy.trans (Nat.le_ceil y)

/-- Keep the actual finite sieve product, but allow a real Selberg level. -/
def realProgressionSelbergSieve (q : ℕ) (hq : q.Prime) (y : ℝ) (N : ℕ)
    (hy : 1 ≤ y) : LPSelbergSieve :=
  { progressionSelbergSieve q hq (Nat.ceil y) N (sieveLevel_ceil_one_le hy) with
    level := y
    one_le_level := hy }

theorem realProgressionSelbergSieve_boundingSum_ge_nu {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 ≤ y) :
    (∑ m ∈ Icc 1 (Nat.floor (Real.sqrt y)), progressionSieveNu q m) ≤
      (realProgressionSelbergSieve q hq y N hy).selbergBoundingSum := by
  apply selbergBoundingSum_ge_sum_nonzero (realProgressionSelbergSieve q hq y N hy)
  · intro p hp hpy hnu
    apply (prime_dvd_progressionSieveProduct_iff q (Nat.ceil y) hp).mpr
    constructor
    · change (p : ℝ) ≤ y at hpy
      exact_mod_cast hpy.trans (Nat.le_ceil y)
    · rintro rfl
      apply hnu
      simp [realProgressionSelbergSieve, progressionSelbergSieve,
        progressionSieveNu, Nat.coprime_self, hq.ne_one]
  · exact progressionSieveNu_completelyMultiplicative q
  · exact progressionSieveNu_nonneg q
  · intro p hp hd
    exact progressionSieveNu_lt_one_of_prime_dvd hq hp (Nat.ceil y) hd

theorem realProgressionSelbergSieve_boundingSum_ge_log {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 ≤ y) :
    Real.log y / 4 ≤ (realProgressionSelbergSieve q hq y N hy).selbergBoundingSum := by
  have hnu := realProgressionSelbergSieve_boundingSum_ge_nu hq y N hy
  have hharm : (∑ m ∈ (Icc 1 (Nat.floor (Real.sqrt y))).filter (q.Coprime ·),
      1 / (m : ℝ)) ≤ (realProgressionSelbergSieve q hq y N hy).selbergBoundingSum := by
    simpa only [Finset.sum_filter, progressionSieveNu_apply] using hnu
  have hyR : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have h := (harmonic_coprime_ge_log hq (Real.sqrt y) hyR).trans hharm
  rw [Real.log_sqrt (by linarith : 0 ≤ y)] at h
  linarith

theorem realProgressionSelbergSieve_abs_rem_le_one {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 ≤ y) {d : ℕ} (hd : 0 < d) :
    |(realProgressionSelbergSieve q hq y N hy).rem d| ≤ 1 := by
  exact progressionSelbergSieve_abs_rem_le_one hq (Nat.ceil y) N
    (sieveLevel_ceil_one_le hy) hd

theorem realProgressionSelbergSieve_remainder_sum_le {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 ≤ y) :
    (∑ d ∈ (progressionSieveProduct q (Nat.ceil y)).divisors,
      if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d *
        |(realProgressionSelbergSieve q hq y N hy).rem d| else 0) ≤
      y * (1 + Real.log y) ^ 3 := by
  calc
    _ ≤ ∑ d ∈ (progressionSieveProduct q (Nat.ceil y)).divisors,
      if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d else 0 := by
        apply sum_le_sum
        intro d hd
        split_ifs
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (realProgressionSelbergSieve_abs_rem_le_one hq y N hy (Nat.pos_of_mem_divisors hd))
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        · rfl
    _ ≤ _ := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow y hy
      (progressionSieveProduct_squarefree q (Nat.ceil y))

theorem realProgressionSelbergSieve_siftedSum {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 ≤ y) :
    (realProgressionSelbergSieve q hq y N hy).siftedSum =
      ((progressionSiftedSupport q (Nat.ceil y) N).card : ℝ) := by
  exact progressionSelbergSieve_siftedSum hq (Nat.ceil y) N (sieveLevel_ceil_one_le hy)

theorem progressionPrefixPrimes_card_real_sieve_le {q : ℕ} (hq : q.Prime)
    (y : ℝ) (N : ℕ) (hy : 1 < y) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      4 * (N : ℝ) / ((q : ℝ) * Real.log y) + y * (1 + Real.log y) ^ 3 + y + 2 := by
  have hy1 := hy.le
  let s := realProgressionSelbergSieve q hq y N hy1
  have hs : s.siftedSum ≤ ((N : ℝ) / q) / s.selbergBoundingSum + y * (1 + Real.log y) ^ 3 := by
    have hb := LPSelbergSieve.selberg_bound_simple s
    change s.siftedSum ≤ ((N : ℝ) / q) / s.selbergBoundingSum +
      ∑ d ∈ (progressionSieveProduct q (Nat.ceil y)).divisors,
        if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |s.rem d| else 0 at hb
    have hr := realProgressionSelbergSieve_remainder_sum_le hq y N hy1
    change (∑ d ∈ (progressionSieveProduct q (Nat.ceil y)).divisors,
      if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |s.rem d| else 0) ≤
        y * (1 + Real.log y) ^ 3 at hr
    linarith only [hb, hr]
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ (N : ℝ) / q)
    (by positivity : 0 < Real.log y / 4)
    (realProgressionSelbergSieve_boundingSum_ge_log hq y N hy1)
  have hp := progressionPrefixPrimes_card_le_sifted_add q (Nat.ceil y) N
  rw [← realProgressionSelbergSieve_siftedSum hq y N hy1] at hp
  have hceil : (Nat.ceil y : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
  have heq : ((N : ℝ) / q) / (Real.log y / 4) = 4 * (N : ℝ) / ((q : ℝ) * Real.log y) := by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    field_simp [hq0, hlog.ne']
  dsimp [s] at hs
  rw [heq] at hdiv
  linarith

end
end SimultaneousPrimitiveRoots

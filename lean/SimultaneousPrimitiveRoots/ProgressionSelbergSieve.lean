module

public import SimultaneousPrimitiveRoots.ProgressionSieveData
public import LeanPool.SelbergSieve4.Selberg
public import LeanPool.SelbergSieve4.AuxResults

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset
open scoped ArithmeticFunction.omega

noncomputable section
open Classical

/-- The actual progression 1 mod q, with unit weights and the modulus prime excluded. -/
def progressionSelbergSieve (q : ℕ) (hq : q.Prime) (z N : ℕ) (hz : 1 ≤ z) : LPSelbergSieve where
  support := progressionDivisorSupport q 1 N
  prodPrimes := progressionSieveProduct q z
  prodPrimes_squarefree := progressionSieveProduct_squarefree q z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (N : ℝ) / q
  nu := progressionSieveNu q
  nu_mult := progressionSieveNu_multiplicative q
  nu_pos_of_prime := fun p hp hd => progressionSieveNu_pos_of_prime_dvd hq hp z hd
  nu_lt_one_of_prime := fun p hp hd => progressionSieveNu_lt_one_of_prime_dvd hq hp z hd
  level := z
  one_le_level := by exact_mod_cast hz

theorem prime_dvd_progressionSieveProduct_iff (q z : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∣ progressionSieveProduct q z ↔ p ≤ z ∧ p ≠ q := by
  unfold progressionSieveProduct
  constructor
  · intro h
    obtain ⟨r, hr, hpr⟩ := hp.prime.exists_mem_finset_dvd h
    obtain ⟨hrz, hrp, hrq⟩ := mem_filter.mp hr
    have heq := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr
    subst r
    exact ⟨by have := mem_range.mp hrz; omega, hrq⟩
  · intro h
    apply Finset.dvd_prod_of_mem
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp, h.2⟩

theorem progressionSieveProduct_coprime_iff (q z n : ℕ) :
    (progressionSieveProduct q z).Coprime n ↔
      ∀ p ∈ progressionSievePrimes q z, ¬ p ∣ n := by
  unfold progressionSieveProduct
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact (Nat.Prime.coprime_iff_not_dvd (mem_filter.mp hp).2.1).mp (h p hp)
  · intro h p hp
    exact (Nat.Prime.coprime_iff_not_dvd (mem_filter.mp hp).2.1).mpr (h p hp)

theorem progressionSelbergSieve_siftedSum {q : ℕ} (hq : q.Prime) (z N : ℕ) (hz : 1 ≤ z) :
    (progressionSelbergSieve q hq z N hz).siftedSum =
      ((progressionSiftedSupport q z N).card : ℝ) := by
  unfold Sieve.siftedSum progressionSelbergSieve
  simp only [progressionSieveProduct_coprime_iff]
  rw [Finset.sum_boole]
  rfl

theorem progressionSelbergSieve_multSum {q : ℕ} (hq : q.Prime) (z N : ℕ) (hz : 1 ≤ z)
    (d : ℕ) :
    (progressionSelbergSieve q hq z N hz).multSum d =
      ((progressionDivisorSupport q d N).card : ℝ) := by
  unfold Sieve.multSum progressionSelbergSieve
  rw [Finset.sum_boole]
  congr 2
  ext n
  simp [progressionDivisorSupport, and_assoc]

theorem progressionSelbergSieve_rem {q : ℕ} (hq : q.Prime) (z N : ℕ) (hz : 1 ≤ z)
    (d : ℕ) :
    (progressionSelbergSieve q hq z N hz).rem d =
      ((progressionDivisorSupport q d N).card : ℝ) -
        ((N : ℝ) / q) * progressionSieveNu q d := by
  rw [Sieve.rem, progressionSelbergSieve_multSum]
  change _ - progressionSieveNu q d * ((N : ℝ) / q) = _
  ring

theorem progressionSelbergSieve_abs_rem_le_one {q : ℕ} (hq : q.Prime) (z N : ℕ)
    (hz : 1 ≤ z) {d : ℕ} (hd : 0 < d) :
    |(progressionSelbergSieve q hq z N hz).rem d| ≤ 1 := by
  rw [progressionSelbergSieve_rem]
  exact progressionSieve_remainder_le_one hq hd N

theorem progressionSelbergSieve_remainder_sum_le {q : ℕ} (hq : q.Prime) (z N : ℕ)
    (hz : 1 ≤ z) :
    (∑ d ∈ (progressionSieveProduct q z).divisors,
      if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d *
        |(progressionSelbergSieve q hq z N hz).rem d| else 0) ≤
      (z : ℝ) * (1 + Real.log z) ^ 3 := by
  calc
    _ ≤ ∑ d ∈ (progressionSieveProduct q z).divisors,
      if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d else 0 := by
        apply sum_le_sum
        intro d hd
        split_ifs
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (progressionSelbergSieve_abs_rem_le_one hq z N hz (Nat.pos_of_mem_divisors hd))
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        · rfl
    _ ≤ _ := Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (z : ℝ)
      (by exact_mod_cast hz) (progressionSieveProduct_squarefree q z)

theorem progressionSiftedSupport_card_selberg_le {q : ℕ} (hq : q.Prime) (z N : ℕ)
    (hz : 1 ≤ z) :
    ((progressionSiftedSupport q z N).card : ℝ) ≤
      ((N : ℝ) / q) / (progressionSelbergSieve q hq z N hz).selbergBoundingSum +
        (z : ℝ) * (1 + Real.log z) ^ 3 := by
  rw [← progressionSelbergSieve_siftedSum hq z N hz]
  exact (LPSelbergSieve.selberg_bound_simple _).trans
    (add_le_add_right (progressionSelbergSieve_remainder_sum_le hq z N hz) _)

theorem progressionPrefixPrimes_card_selberg_le {q : ℕ} (hq : q.Prime) (z N : ℕ)
    (hz : 1 ≤ z) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      ((N : ℝ) / q) / (progressionSelbergSieve q hq z N hz).selbergBoundingSum +
        (z : ℝ) * (1 + Real.log z) ^ 3 + z + 1 := by
  exact (progressionPrefixPrimes_card_le_sifted_add q z N).trans
    (by gcongr; exact progressionSiftedSupport_card_selberg_le hq z N hz)

end

end SimultaneousPrimitiveRoots

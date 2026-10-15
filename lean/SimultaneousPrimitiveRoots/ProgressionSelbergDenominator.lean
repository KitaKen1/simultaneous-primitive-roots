/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in vendor/LEANPOOL_LICENSE.
The generalized denominator proof adapts LeanPool/SelbergSieve4/Applications/
PrimeCountingUpperBound.lean at fbe0fe3397f00e1933ffec1aed9a7f882898b1d2.
-/
module

public import SimultaneousPrimitiveRoots.ProgressionSelbergSieve
public import SimultaneousPrimitiveRoots.ProgressionHarmonic
public import LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open Finset Real Nat PrimeUpperBound
noncomputable section
open Classical

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

theorem selbergBoundingSum_ge_sum_nonzero (s : LPSelbergSieve)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → s.nu p ≠ 0 → p ∣ s.prodPrimes)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := by
  have heq : (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m) =
      ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt s.level))).filter
        (fun m => s.nu m ≠ 0), s.nu m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp_all
  rw [heq]
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then s.selbergTerms l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => l ^ 2 ≤ s.level),
        ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
   _ ≥ ∑ m ∈ (Finset.Icc 1 (Nat.floor (Real.sqrt s.level))).filter (fun m => s.nu m ≠ 0), s.nu m := ?_
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
      · intro p hpp hpl
        apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      obtain ⟨hm, hmnu⟩ := Finset.mem_filter.mp hm
      have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
        apply Finset.prod_pos
        intro p hp
        exact Nat.pos_of_mem_primeFactors hp
      have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
        pow_ne_zero _ (ne_of_gt hprod_pos)
      rw [Finset.mem_biUnion]
      simp_rw [Finset.mem_filter, Nat.mem_divisors]
      rw [Finset.mem_Icc, Nat.le_floor_iff (Real.sqrt_nonneg s.level)] at hm
      have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor
      · constructor
        · constructor
          · apply lem0 <;> intro p hp
            · apply hP p (Nat.prime_of_mem_primeFactors hp)
              · trans (m : ℝ)
                · norm_cast
                  exact Nat.le_of_mem_primeFactors hp
                trans (Real.sqrt s.level)
                · exact hm.2
                exact sqrt_le_self s.level s.one_le_level
              · obtain ⟨k, hk⟩ := Nat.dvd_of_mem_primeFactors hp
                intro hzero
                apply hmnu
                rw [hk, hnu.2, hzero, zero_mul]
            · exact Nat.prime_of_mem_primeFactors hp
          · exact s.prodPrimes_ne_zero
        · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Nat.cast_pow,
            Real.sqrt_sq]
          · trans (m : ℝ)
            · norm_cast
              apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
              exact Nat.prod_primeFactors_dvd m
            · exact hm.2
          · apply le_of_lt
            norm_cast
      · constructor
        · constructor
          · rw [← Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
            · intro p
              have hy_mul_prod_nonneg :
                  0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
                zero_le
              trans (Nat.factorization m) p * 1
              · rw [mul_one]
              trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
              swap
              · apply le_rfl
              by_cases hpp : p.Prime
              swap
              · simp_all
              by_cases hpdvd : p ∣ m
              swap
              · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
                exact hy_mul_prod_nonneg
              apply mul_le_mul
              · trans m
                · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
                apply Nat.le_floor
                refine le_trans hm.2 ?_
                apply sqrt_le_self _ s.one_le_level
              · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos,
                  pow_one]
                apply Finset.dvd_prod_of_mem
                simp_all
              · norm_num
              · norm_num
            · exact hm_ne_zero
          · exact hprod_ne_zero
        · exact Nat.prod_primeFactors_dvd m
    · simp_all
  · intro i hi j hj hij t hti htj x hx
    exfalso
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply nat_squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi


theorem progressionSieveNu_completelyMultiplicative (q : ℕ) :
    PrimeUpperBound.CompletelyMultiplicative (progressionSieveNu q) := by
  constructor
  · simp [progressionSieveNu]
  · intro m n
    change (if q.Coprime (m * n) then 1 / ((m * n : ℕ) : ℝ) else 0) =
      (if q.Coprime m then 1 / (m : ℝ) else 0) * (if q.Coprime n then 1 / (n : ℝ) else 0)
    split_ifs <;> simp_all [Nat.coprime_mul_iff_right, mul_comm]

theorem progressionSieveNu_apply (q d : ℕ) :
    progressionSieveNu q d = if q.Coprime d then 1 / (d : ℝ) else 0 := rfl

theorem progressionSelbergSieve_boundingSum_ge_nu {q : ℕ} (hq : q.Prime)
    (z N : ℕ) (hz : 1 ≤ z) :
    (∑ m ∈ Icc 1 (Nat.floor (Real.sqrt (z : ℝ))), progressionSieveNu q m) ≤
      (progressionSelbergSieve q hq z N hz).selbergBoundingSum := by
  apply selbergBoundingSum_ge_sum_nonzero (progressionSelbergSieve q hq z N hz)
  · intro p hp hpz hnu
    apply (prime_dvd_progressionSieveProduct_iff q z hp).mpr
    constructor
    · change (p : ℝ) ≤ z at hpz
      exact_mod_cast hpz
    · rintro rfl
      apply hnu
      simp [progressionSelbergSieve, progressionSieveNu, Nat.coprime_self, hq.ne_one]
  · exact progressionSieveNu_completelyMultiplicative q
  · exact progressionSieveNu_nonneg q
  · intro p hp hd
    exact progressionSieveNu_lt_one_of_prime_dvd hq hp z hd

theorem progressionSelbergSieve_boundingSum_ge_harmonic {q : ℕ} (hq : q.Prime)
    (z N : ℕ) (hz : 1 ≤ z) :
    (∑ m ∈ (Icc 1 (Nat.floor (Real.sqrt (z : ℝ)))).filter (q.Coprime ·), 1 / (m : ℝ)) ≤
      (progressionSelbergSieve q hq z N hz).selbergBoundingSum := by
  simpa only [Finset.sum_filter, progressionSieveNu_apply] using
    progressionSelbergSieve_boundingSum_ge_nu hq z N hz

theorem progressionSelbergSieve_boundingSum_ge_log {q : ℕ} (hq : q.Prime)
    (z N : ℕ) (hz : 1 ≤ z) :
    Real.log (z : ℝ) / 4 ≤ (progressionSelbergSieve q hq z N hz).selbergBoundingSum := by
  have hzR : (1 : ℝ) ≤ Real.sqrt (z : ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ z by exact_mod_cast hz)
  have h := (harmonic_coprime_ge_log hq (Real.sqrt (z : ℝ)) hzR).trans
    (progressionSelbergSieve_boundingSum_ge_harmonic hq z N hz)
  rw [Real.log_sqrt (Nat.cast_nonneg z)] at h
  linarith

theorem progressionPrefixPrimes_card_log_sieve_le {q : ℕ} (hq : q.Prime)
    (z N : ℕ) (hz : 1 < z) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      ((N : ℝ) / q) / (Real.log (z : ℝ) / 4) +
        (z : ℝ) * (1 + Real.log z) ^ 3 + z + 1 := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ (N : ℝ) / q)
    (by positivity : 0 < Real.log (z : ℝ) / 4)
    (progressionSelbergSieve_boundingSum_ge_log hq z N (le_of_lt hz))
  exact (progressionPrefixPrimes_card_selberg_le hq z N (le_of_lt hz)).trans
    (by linarith)

theorem progressionPrefixPrimes_card_explicit_sieve_le {q : ℕ} (hq : q.Prime)
    (z N : ℕ) (hz : 1 < z) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      4 * (N : ℝ) / ((q : ℝ) * Real.log z) +
        (z : ℝ) * (1 + Real.log z) ^ 3 + z + 1 := by
  have hlog : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  convert progressionPrefixPrimes_card_log_sieve_le hq z N hz using 1
  field_simp [hq0, hlog.ne']

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.ProgressionSieveCounting
public import SimultaneousPrimitiveRoots.BrunTitchmarshBridge
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset

noncomputable section
open Classical

/-- Local divisor density within the progression 1 mod q. -/
def progressionSieveNu (q : ℕ) : ArithmeticFunction ℝ where
  toFun := fun d => if q.Coprime d then 1 / (d : ℝ) else 0
  map_zero' := by simp

theorem progressionSieveNu_multiplicative (q : ℕ) :
    (progressionSieveNu q).IsMultiplicative := by
  constructor
  · simp [progressionSieveNu]
  · intro m n _
    change (if q.Coprime (m * n) then 1 / ((m * n : ℕ) : ℝ) else 0) =
      (if q.Coprime m then 1 / (m : ℝ) else 0) * (if q.Coprime n then 1 / (n : ℝ) else 0)
    split_ifs <;> simp_all [Nat.coprime_mul_iff_right, mul_comm]

theorem progressionSieveNu_nonneg (q d : ℕ) : 0 ≤ progressionSieveNu q d := by
  change 0 ≤ if q.Coprime d then 1 / (d : ℝ) else 0
  split_ifs <;> positivity

theorem progressionSieveDensity_eq_nu (q d : ℕ) :
    progressionSieveDensity q d = (1 / (q : ℝ)) * progressionSieveNu q d := by
  unfold progressionSieveDensity
  change (if q.Coprime d then 1 / ((q : ℝ) * d) else 0) =
    (1 / (q : ℝ)) * (if q.Coprime d then 1 / (d : ℝ) else 0)
  split_ifs <;> simp [one_div, mul_comm]

theorem progressionSieveNu_prime {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    progressionSieveNu q p = 1 / (p : ℝ) := by
  have hc : q.Coprime p := (Nat.coprime_primes hq hp).mpr hpq.symm
  simp [progressionSieveNu, hc]

theorem progressionSieveNu_prime_pos {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    0 < progressionSieveNu q p := by
  rw [progressionSieveNu_prime hq hp hpq]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  positivity

theorem progressionSieveNu_prime_lt_one {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    progressionSieveNu q p < 1 := by
  rw [progressionSieveNu_prime hq hp hpq]
  simpa only [one_div] using inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)

def progressionSievePrimes (q z : ℕ) : Finset ℕ :=
  (range (z + 1)).filter fun p => p.Prime ∧ p ≠ q

def progressionSieveProduct (q z : ℕ) : ℕ := ∏ p ∈ progressionSievePrimes q z, p

theorem progressionSieveProduct_squarefree (q z : ℕ) : Squarefree (progressionSieveProduct q z) := by
  unfold progressionSieveProduct
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_)
    (fun p hp => (mem_filter.mp hp).2.1.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_filter.mp hp).2.1 (mem_filter.mp hr).2.1).mpr hpr

theorem progressionSieveProduct_coprime {q : ℕ} (hq : q.Prime) (z : ℕ) :
    q.Coprime (progressionSieveProduct q z) := by
  unfold progressionSieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨_, hprime, hpq⟩ := mem_filter.mp hp
  exact (Nat.coprime_primes hq hprime).mpr hpq.symm

theorem progressionSieveNu_eq_inv_of_dvd {q d : ℕ} (hq : q.Prime) (z : ℕ)
    (hd : d ∣ progressionSieveProduct q z) : progressionSieveNu q d = 1 / (d : ℝ) := by
  have hc : q.Coprime d := (progressionSieveProduct_coprime hq z).of_dvd_right hd
  simp [progressionSieveNu, hc]

theorem progressionSieveNu_pos_of_prime_dvd {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (z : ℕ)
    (hd : p ∣ progressionSieveProduct q z) : 0 < progressionSieveNu q p := by
  rw [progressionSieveNu_eq_inv_of_dvd hq z hd]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  positivity

theorem progressionSieveNu_lt_one_of_prime_dvd {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (z : ℕ)
    (hd : p ∣ progressionSieveProduct q z) : progressionSieveNu q p < 1 := by
  rw [progressionSieveNu_eq_inv_of_dvd hq z hd]
  simpa only [one_div] using inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)

theorem progressionSieve_remainder_le_one {q d : ℕ} (hq : q.Prime) (hd : 0 < d) (N : ℕ) :
    |((progressionDivisorSupport q d N).card : ℝ) -
      ((N : ℝ) / q) * progressionSieveNu q d| ≤ 1 := by
  have h := progressionDivisorSupport_card_error hq hd N
  rw [progressionSieveDensity_eq_nu] at h
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

def progressionSiftedSupport (q z N : ℕ) : Finset ℕ :=
  (progressionDivisorSupport q 1 N).filter fun n =>
    ∀ p ∈ progressionSievePrimes q z, ¬ p ∣ n

theorem progressionPrefixPrimes_subset_support (q N : ℕ) :
    progressionPrefixPrimes q N ⊆ progressionDivisorSupport q 1 N := by
  intro p hp
  obtain ⟨hpN, hprime, hqd⟩ := mem_filter.mp hp
  have hp1 := hprime.one_le
  obtain ⟨k, hk⟩ := hqd
  have heq : p = q * k + 1 := by omega
  apply mem_filter.mpr
  refine ⟨hpN, ?_, one_dvd _⟩
  simp [heq, Nat.ModEq, Nat.add_mod]

theorem progressionPrefixPrimes_subset_sifted_union (q z N : ℕ) :
    progressionPrefixPrimes q N ⊆
      progressionSiftedSupport q z N ∪ progressionPrefixPrimes q (z + 1) := by
  intro p hp
  obtain ⟨hpN, hprime, hqd⟩ := mem_filter.mp hp
  by_cases hpz : p ≤ z
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hprime, hqd⟩)
  · apply mem_union_left
    apply mem_filter.mpr
    refine ⟨progressionPrefixPrimes_subset_support q N hp, ?_⟩
    intro r hr hrd
    obtain ⟨hrz, hrprime, _⟩ := mem_filter.mp hr
    obtain hr1 | hrp := (Nat.dvd_prime hprime).mp hrd
    · exact hrprime.ne_one hr1
    · subst r
      have := mem_range.mp hrz
      omega

theorem progressionPrefixPrimes_card_le_sifted_add (q z N : ℕ) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      ((progressionSiftedSupport q z N).card : ℝ) + (z : ℝ) + 1 := by
  have hc := (card_le_card (progressionPrefixPrimes_subset_sifted_union q z N)).trans
    (card_union_le _ _)
  have hs : (progressionPrefixPrimes q (z + 1)).card ≤ z + 1 :=
    (card_le_card (filter_subset _ _)).trans_eq (card_range _)
  have h := hc.trans (Nat.add_le_add_left hs _)
  exact_mod_cast h

end

end SimultaneousPrimitiveRoots

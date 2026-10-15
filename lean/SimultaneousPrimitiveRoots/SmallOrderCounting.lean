module

public import SimultaneousPrimitiveRoots.SmallOrder
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace SimultaneousPrimitiveRoots

theorem log_smallOrderProduct_le {a : ℕ} (ha : 2 ≤ a) (N : ℕ) :
    Real.log (smallOrderProduct a N) ≤ (N : ℝ) ^ 2 * Real.log a := by
  have hlog : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a))
  have hfactor (j : ℕ) (hj : j ∈ Finset.Icc 1 N) : 0 < a ^ j - 1 := by
    have hjpos : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    have := one_lt_pow₀ (by omega : 1 < a) hjpos
    omega
  unfold smallOrderProduct
  rw [Nat.cast_prod, Real.log_prod (fun j hj => by exact_mod_cast (hfactor j hj).ne')]
  calc
    (∑ j ∈ Finset.Icc 1 N, Real.log ((a ^ j - 1 : ℕ) : ℝ)) ≤
        ∑ _j ∈ Finset.Icc 1 N, (N : ℝ) * Real.log a := by
      apply Finset.sum_le_sum
      intro j hj
      have hpos : 0 < ((a ^ j - 1 : ℕ) : ℝ) := by exact_mod_cast hfactor j hj
      have hle : ((a ^ j - 1 : ℕ) : ℝ) ≤ (a : ℝ) ^ j := by
        exact_mod_cast (Nat.sub_le (a ^ j) 1)
      calc
        Real.log ((a ^ j - 1 : ℕ) : ℝ) ≤ Real.log ((a : ℝ) ^ j) :=
          Real.log_le_log hpos hle
        _ = (j : ℝ) * Real.log a := Real.log_pow _ _
        _ ≤ (N : ℝ) * Real.log a :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_Icc.mp hj).2) hlog
    _ = (N : ℝ) ^ 2 * Real.log a := by simp [pow_two, mul_assoc]

/-- Distinct primes larger than x that divide a positive integer M consume
at least log x each from log M. -/
theorem prime_divisors_card_mul_log_le {S : Finset ℕ} {M : ℕ} {x : ℝ}
    (hM : 0 < M) (hx : 1 < x)
    (hS : ∀ p ∈ S, p.Prime ∧ x < (p : ℝ) ∧ p ∣ M) :
    (S.card : ℝ) * Real.log x ≤ Real.log M := by
  have hsub : S ⊆ M.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2.2, hM.ne'⟩
  have hdiv : (∏ p ∈ S, p) ∣ M :=
    (Finset.prod_dvd_prod_of_subset S M.primeFactors (fun p => p) hsub).trans
      (Nat.prod_primeFactors_dvd M)
  have hprod : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hS p hp).1.pos
  have hle : (∏ p ∈ S, (p : ℝ)) ≤ M := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hM hdiv
  calc
    (S.card : ℝ) * Real.log x = ∑ _p ∈ S, Real.log x := by simp
    _ ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by linarith) (hS p hp).2.1.le
    _ = Real.log (∏ p ∈ S, (p : ℝ)) :=
      (Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).1.ne_zero)).symm
    _ ≤ Real.log M := Real.log_le_log (by rw [← Nat.cast_prod]; exact_mod_cast hprod) hle

theorem small_order_exception_card_le {S : Finset ℕ} {a N : ℕ} {x : ℝ}
    (ha : 2 ≤ a) (hx : 1 < x)
    (hS : ∀ p ∈ S, p.Prime ∧ x < (p : ℝ) ∧ p ∣ smallOrderProduct a N) :
    (S.card : ℝ) ≤ (N : ℝ) ^ 2 * Real.log a / Real.log x := by
  apply (le_div_iff₀ (Real.log_pos hx)).mpr
  exact (prime_divisors_card_mul_log_le (smallOrderProduct_pos ha N) hx hS).trans
    (log_smallOrderProduct_le ha N)

end SimultaneousPrimitiveRoots

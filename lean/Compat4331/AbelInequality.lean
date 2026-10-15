/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Copyright (c) 2022 Dylan MacKenzie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies, Dylan MacKenzie
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Tactic

/-! Summation by parts and Abel's inequality from the pinned later Mathlib. -/

public section

namespace Finset

section
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  (f : ℕ → R) (g : ℕ → M) (n : ℕ)
theorem sum_range_by_parts' :
    ∑ i ∈ range n, f i • g i =
      (∑ i ∈ range n, f i) • g (n - 1) -
        ∑ i ∈ range (n - 1), (∑ j ∈ range (i + 1), f j) • (g (i + 1) - g i) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel]
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ (f := fun i ↦ f i • g i), ih]
      simp only [sum_range_succ, smul_sub, add_smul]
      abel

end

end Finset

namespace Finset

variable {R : Type*} {f c g : ℕ → R} {M m : R} {n : ℕ}

section IsOrderedRing
variable [Ring R] [PartialOrder R] [IsOrderedRing R]

/-- **Abel's inequality** (comparison form): if the partial sums of `f` are dominated by those of
`c` up to `n`, and `g` is nonnegative and antitone, then the `g`-weighted sum of `f` is dominated by
that of `c`. -/
theorem sum_mul_le_sum_mul_of_sum_range_le
    (hfc : ∀ k ≤ n, ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, c i) (hg₀ : 0 ≤ g)
    (hg : AntitoneOn g (Set.Iio n)) :
    ∑ i ∈ range n, f i * g i ≤ ∑ i ∈ range n, c i * g i := by
  rw [← sub_nonneg, ← sum_sub_distrib]
  have hD (k) (hk : k ≤ n) : 0 ≤ ∑ i ∈ range k, (c i - f i) := by simpa [sub_nonneg] using hfc k hk
  simp_rw [← sub_mul, ← smul_eq_mul, sum_range_by_parts' (fun i ↦ c i - f i) g n, smul_eq_mul]
  rw [sub_nonneg]
  refine (sum_nonpos fun i hi ↦ ?_).trans (mul_nonneg (hD n le_rfl) (hg₀ (n - 1)))
  have hi' : i < n - 1 := mem_range.1 hi
  exact mul_nonpos_of_nonneg_of_nonpos (hD (i + 1) (by omega))
    (sub_nonpos.2 (hg (Set.mem_Iio.2 (by omega)) (Set.mem_Iio.2 (by omega)) (Nat.le_succ i)))

/-- **Abel's inequality** (one-sided upper form): if every partial sum of `f` up to `n` is at most
`M`, and `g` is nonnegative and antitone, then `∑ i ∈ range n, f i * g i ≤ M * g 0`. -/
theorem sum_mul_le_mul_of_sum_range_le
    (hf : ∀ k ≤ n, ∑ i ∈ range k, f i ≤ M) (hg₀ : 0 ≤ g) (hg : AntitoneOn g (Set.Iio n)) :
    ∑ i ∈ range n, f i * g i ≤ M * g 0 := by
  have : 0 ≤ M := by simpa using hf 0 n.zero_le
  refine (sum_mul_le_sum_mul_of_sum_range_le (c := fun i ↦ if i = 0 then M else 0)
    (fun k hk ↦ ?_) hg₀ hg).trans ?_
  · rw [sum_ite_eq']
    split_ifs <;> simp_all
  · simp_rw [ite_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp [mul_nonneg this (hg₀ 0)]

/-- **Abel's inequality** (one-sided lower form): if every partial sum of `f` up to `n` is at least
`m`, and `g` is nonnegative and antitone, then `m * g 0 ≤ ∑ i ∈ range n, f i * g i`. -/
theorem mul_le_sum_mul_of_le_sum_range
    (hf : ∀ k ≤ n, m ≤ ∑ i ∈ range k, f i) (hg₀ : 0 ≤ g) (hg : AntitoneOn g (Set.Iio n)) :
    m * g 0 ≤ ∑ i ∈ range n, f i * g i := by
  have : m ≤ 0 := by simpa using hf 0 n.zero_le
  refine le_trans ?_ (sum_mul_le_sum_mul_of_sum_range_le (f := fun i ↦ if i = 0 then m else 0)
    (c := f) (fun k hk ↦ ?_) hg₀ hg)
  · simp_rw [ite_mul, zero_mul, sum_ite_eq']
    split_ifs <;> simp [mul_nonpos_of_nonpos_of_nonneg this (hg₀ 0)]
  · rw [sum_ite_eq']
    split_ifs <;> simp_all

end IsOrderedRing

/-- **Abel's inequality**: if every partial sum of `f` up to `n` has absolute value at most `M`, and
`g` is nonnegative and antitone, then `|∑ i ∈ range n, f i * g i| ≤ M * g 0`. -/
theorem abs_sum_mul_le_mul_of_abs_sum_range_le [Ring R] [LinearOrder R] [IsOrderedRing R]
    (hf : ∀ k ≤ n, |∑ i ∈ range k, f i| ≤ M) (hg₀ : 0 ≤ g) (hg : AntitoneOn g (Set.Iio n)) :
    |∑ i ∈ range n, f i * g i| ≤ M * g 0 := by
  rw [abs_le]
  refine ⟨?_, sum_mul_le_mul_of_sum_range_le (fun k hk ↦ (abs_le.1 (hf k hk)).2) hg₀ hg⟩
  simpa [neg_mul] using
    mul_le_sum_mul_of_le_sum_range (m := -M) (fun k hk ↦ (abs_le.1 (hf k hk)).1) hg₀ hg

end Finset

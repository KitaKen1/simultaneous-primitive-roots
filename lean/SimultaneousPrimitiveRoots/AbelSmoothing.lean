module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Finset

noncomputable section

/-- A discrete kernel with an exactly telescoping total mass. -/
def rationalSmoothingKernel (x : ℝ) (n : ℕ) : ℝ :=
  x ^ 2 / ((x + n) * (x + n + 1))

theorem rationalSmoothingKernel_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 ≤ rationalSmoothingKernel x n := by
  unfold rationalSmoothingKernel
  positivity

theorem rationalSmoothingKernel_antitone {x : ℝ} (hx : 0 < x) :
    Antitone (rationalSmoothingKernel x) := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  unfold rationalSmoothingKernel
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

theorem rationalSmoothingKernel_sum_range {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ range N, rationalSmoothingKernel x n = x - x ^ 2 / (x + N) := by
  induction N with
  | zero =>
    simp only [sum_range_zero, Nat.cast_zero, add_zero]
    field_simp
    ring
  | succ N ih =>
    rw [sum_range_succ, ih]
    unfold rationalSmoothingKernel
    push_cast
    have hN : x + (N : ℝ) ≠ 0 := by positivity
    have hN1 : x + (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem rationalSmoothingKernel_sum_range_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    ∑ n ∈ range N, rationalSmoothingKernel x n ≤ x := by
  rw [rationalSmoothingKernel_sum_range hx]
  exact sub_le_self _ (by positivity)

theorem rationalSmoothingKernel_zero_le_one {x : ℝ} (hx : 0 < x) :
    rationalSmoothingKernel x 0 ≤ 1 := by
  unfold rationalSmoothingKernel
  simp only [Nat.cast_zero, add_zero]
  apply (div_le_one (by positivity)).2
  nlinarith

/-- Abel comparison: only the prefix sums of the two sequences are needed. -/
theorem sum_range_mul_le_of_prefix_le (k a b : ℕ → ℝ)
    (hk : ∀ n, 0 ≤ k n) (hmono : Antitone k)
    (hprefix : ∀ N, ∑ n ∈ range N, a n ≤ ∑ n ∈ range N, b n) (N : ℕ) :
    ∑ n ∈ range N, k n * a n ≤ ∑ n ∈ range N, k n * b n := by
  have h1 := sum_range_by_parts k a N
  have h2 := sum_range_by_parts k b N
  simp only [smul_eq_mul] at h1 h2
  rw [h1, h2]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hprefix N) (hk _)
  · apply sum_le_sum
    intro n _
    exact mul_le_mul_of_nonpos_left (hprefix (n + 1))
      (sub_nonpos.mpr (hmono (by omega)))

/-- A linear prefix bound, with an additive error, survives smoothing.
The additive error is charged only once, at the start of the sequence. -/
theorem rationalSmoothing_sum_range_le {x A B : ℝ} (hx : 0 < x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (a : ℕ → ℝ)
    (hprefix : ∀ N, ∑ n ∈ range N, a n ≤ A * N + B) (N : ℕ) :
    ∑ n ∈ range N, a n * rationalSmoothingKernel x n ≤ A * x + B := by
  classical
  let b : ℕ → ℝ := fun n => A + if n = 0 then B else 0
  have hb : ∀ M, ∑ n ∈ range M, a n ≤ ∑ n ∈ range M, b n := by
    intro M
    cases M with
    | zero => simp
    | succ M =>
      simpa [b, sum_add_distrib, sum_ite_eq', Nat.cast_add, Nat.cast_one, mul_comm]
        using hprefix (M + 1)
  have hcomp := sum_range_mul_le_of_prefix_le (rationalSmoothingKernel x) a b
    (rationalSmoothingKernel_nonneg hx) (rationalSmoothingKernel_antitone hx) hb N
  simp only [mul_comm (rationalSmoothingKernel x _) (a _)] at hcomp
  apply hcomp.trans
  calc
    _ = A * (∑ n ∈ range N, rationalSmoothingKernel x n) +
        if 0 < N then B * rationalSmoothingKernel x 0 else 0 := by
      simp only [b, mul_add, mul_ite, mul_zero]
      rw [sum_add_distrib, ← sum_mul]
      simp [sum_ite_eq', mul_comm]
    _ ≤ A * x + B := by
      apply add_le_add (mul_le_mul_of_nonneg_left (rationalSmoothingKernel_sum_range_le hx N) hA)
      split_ifs
      · exact (mul_le_mul_of_nonneg_left (rationalSmoothingKernel_zero_le_one hx) hB).trans_eq
          (mul_one B)
      · exact hB

theorem rationalSmoothing_summable {x A B : ℝ} (hx : 0 < x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, ∑ n ∈ range N, a n ≤ A * N + B) :
    Summable (fun n => a n * rationalSmoothingKernel x n) := by
  exact summable_of_sum_range_le (fun n => mul_nonneg (ha n) (rationalSmoothingKernel_nonneg hx n))
    (rationalSmoothing_sum_range_le hx hA hB a hprefix)

theorem rationalSmoothing_tsum_le {x A B : ℝ} (hx : 0 < x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, ∑ n ∈ range N, a n ≤ A * N + B) :
    (∑' n, a n * rationalSmoothingKernel x n) ≤ A * x + B := by
  exact Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (ha n) (rationalSmoothingKernel_nonneg hx n))
    (rationalSmoothing_sum_range_le hx hA hB a hprefix)

end

end SimultaneousPrimitiveRoots

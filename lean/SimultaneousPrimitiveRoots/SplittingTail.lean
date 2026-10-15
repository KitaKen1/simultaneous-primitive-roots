module

public import SimultaneousPrimitiveRoots.SmallOrderAsymptotic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics
open scoped Topology

/-- Summing over all integers suffices for the main term of the splitting tail. -/
theorem reciprocal_tail_telescope {Y N : ℕ} (hY : 1 ≤ Y) (hN : Y ≤ N) :
    (∑ q ∈ Finset.Ico (Y + 1) (N + 1),
      1 / ((q : ℝ) * ((q : ℝ) - 1))) = 1 / (Y : ℝ) - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    push_cast
    field_simp [hkpos.ne']
    ring

/-- No prime number theorem is required to bound a finite prime tail. -/
theorem reciprocal_tail_finset_le {Y : ℕ} (hY : 1 ≤ Y) (S : Finset ℕ)
    (hS : ∀ q ∈ S, Y < q) :
    (∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1))) ≤ 1 / (Y : ℝ) := by
  classical
  let N := max Y (S.sup id)
  have hN : Y ≤ N := le_max_left _ _
  have hsub : S ⊆ Finset.Ico (Y + 1) (N + 1) := by
    intro q hq
    have hqN : q ≤ N := (Finset.le_sup (f := id) hq).trans (le_max_right _ _)
    exact Finset.mem_Ico.mpr ⟨by have := hS q hq; omega, by omega⟩
  calc
    (∑ q ∈ S, 1 / ((q : ℝ) * ((q : ℝ) - 1))) ≤
        ∑ q ∈ Finset.Ico (Y + 1) (N + 1),
          1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q hq _
      have hqnat := (Finset.mem_Ico.mp hq).1
      have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
    _ = 1 / (Y : ℝ) - 1 / (N : ℝ) := reciprocal_tail_telescope hY hN
    _ ≤ 1 / (Y : ℝ) := sub_le_self _ (by positivity)

/-- A power saving absorbs one logarithm after the error sums are estimated trivially. -/
theorem sublinear_power_isLittleO_prime_scale (C : ℝ) {α : ℝ} (hα : α < 1) :
    (fun x : ℝ => C * x ^ α) =o[atTop] (fun x => x / Real.log x) := by
  have hratio : Tendsto (fun x : ℝ => C * (Real.log x / x ^ (1 - α)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul
      (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).tendsto_div_nhds_zero
  have hratio' : Tendsto (fun x : ℝ => (C * x ^ α) / (x / Real.log x))
      atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hratio
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [Real.rpow_sub hxpos, Real.rpow_one]
    have hpow : x ^ α ≠ 0 := (Real.rpow_pos_of_pos hxpos α).ne'
    field_simp
  apply isLittleO_of_tendsto' ?_ hratio'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact fun h => (div_pos (by linarith) (Real.log_pos (by linarith))).ne' h |>.elim

theorem splitting_power_error_isLittleO (C : ℝ) {δ η : ℝ} (hη : η < δ) :
    (fun x : ℝ => C * x ^ (1 - δ + η)) =o[atTop]
      (fun x => x / Real.log x) :=
  sublinear_power_isLittleO_prime_scale C (by linarith)

end SimultaneousPrimitiveRoots

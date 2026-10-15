module

public import SimultaneousPrimitiveRoots.SmallOrderCounting
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics
open scoped Topology

noncomputable def smallOrderExceptionPrimes (a : ℕ) (η x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ p ∣ smallOrderProduct a ⌊2 * x ^ η⌋₊

theorem smallOrderExceptionPrimes_card_le {a : ℕ} (ha : 2 ≤ a) (η : ℝ)
    {x : ℝ} (hx : 1 < x) :
    ((smallOrderExceptionPrimes a η x).card : ℝ) ≤
      (4 * Real.log a) * x ^ (2 * η) / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a))
  have hN : (⌊2 * x ^ η⌋₊ : ℝ) ≤ 2 * x ^ η := Nat.floor_le (by positivity)
  have hNpos : 0 ≤ (⌊2 * x ^ η⌋₊ : ℝ) := by positivity
  have hpowpos : 0 ≤ x ^ η := Real.rpow_nonneg hxpos.le _
  have hpow : x ^ (2 * η) = (x ^ η) ^ (2 : ℕ) := by
    rw [mul_comm (2 : ℝ) η, Real.rpow_mul hxpos.le, Real.rpow_two]
  have hsquare : (⌊2 * x ^ η⌋₊ : ℝ) ^ 2 ≤ 4 * x ^ (2 * η) := by
    rw [hpow]
    nlinarith
  calc
    ((smallOrderExceptionPrimes a η x).card : ℝ) ≤
        (⌊2 * x ^ η⌋₊ : ℝ) ^ 2 * Real.log a / Real.log x :=
      small_order_exception_card_le ha hx (fun p hp => (Finset.mem_filter.mp hp).2)
    _ ≤ (4 * Real.log a) * x ^ (2 * η) / Real.log x := by
      apply div_le_div_of_nonneg_right _ (Real.log_pos hx).le
      nlinarith [mul_le_mul_of_nonneg_right hsquare hlog]

theorem sublinear_power_over_log_isLittleO (C : ℝ) {α : ℝ} (hα : α < 1) :
    (fun x : ℝ => C * x ^ α / Real.log x) =o[atTop] (fun x => x / Real.log x) := by
  have hC : Tendsto (fun x : ℝ => C * x ^ (-(1 - α))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_rpow_neg_atTop (sub_pos.mpr hα))
  have hratio : Tendsto
      (fun x : ℝ => (C * x ^ α / Real.log x) / (x / Real.log x)) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hC
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hxpos : 0 < x := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [show -(1 - α) = α - 1 by ring, Real.rpow_sub_one hxpos.ne']
    field_simp
  apply isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hpos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos (by linarith))
  exact fun hzero => (hpos.ne' hzero).elim

theorem smallOrderExceptionPrimes_isLittleO {a : ℕ} (ha : 2 ≤ a) {η : ℝ}
    (hη : η < 1 / 2) :
    (fun x : ℝ => ((smallOrderExceptionPrimes a η x).card : ℝ)) =o[atTop]
      (fun x => x / Real.log x) := by
  have hb : (fun x : ℝ => ((smallOrderExceptionPrimes a η x).card : ℝ)) =O[atTop]
      (fun x => (4 * Real.log a) * x ^ (2 * η) / Real.log x) := by
    apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hlog : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a))
    have hbpos : 0 ≤ (4 * Real.log a) * x ^ (2 * η) / Real.log x :=
      div_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
        (Real.log_pos (by linarith)).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hbpos]
    exact smallOrderExceptionPrimes_card_le ha η (by linarith)
  exact hb.trans_isLittleO (sublinear_power_over_log_isLittleO (4 * Real.log a) (by linarith))

theorem smallOrderExceptionUnion_isLittleO {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) {η : ℝ} (hη : η < 1 / 2) :
    (fun x : ℝ => ((A.biUnion fun a => smallOrderExceptionPrimes a η x).card : ℝ))
      =o[atTop] (fun x => x / Real.log x) := by
  classical
  have hsum : (fun x : ℝ => ∑ a ∈ A, ((smallOrderExceptionPrimes a η x).card : ℝ))
      =o[atTop] (fun x => x / Real.log x) := by
    simpa only [Finset.sum_fn] using
      IsLittleO.sum (fun a ha => smallOrderExceptionPrimes_isLittleO (hpos a ha) hη)
  apply IsBigO.trans_isLittleO (IsBigO.of_bound' ?_) hsum
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_biUnion_le

end SimultaneousPrimitiveRoots

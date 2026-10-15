module

public import SimultaneousPrimitiveRoots.SplittingTail

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics

theorem moving_cutoff_pos {η x : ℝ} (hη : 0 ≤ η) (hx : 2 ≤ x) :
    1 ≤ ⌊2 * x ^ η⌋₊ := by
  have hp : 1 ≤ x ^ η := Real.one_le_rpow (by linarith) hη
  exact Nat.le_floor (by norm_num; linarith)

theorem moving_cutoff_log_le {η x : ℝ} (hη : 0 ≤ η) (hx : 2 ≤ x) :
    Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) ≤ (η + 2) * Real.log x := by
  have hxpos : 0 < x := by linarith
  have hNpos : 0 < (⌊2 * x ^ η⌋₊ : ℝ) := by
    exact_mod_cast (by have := moving_cutoff_pos hη hx; omega : 0 < ⌊2 * x ^ η⌋₊)
  have hNle : (⌊2 * x ^ η⌋₊ : ℝ) ≤ 2 * x ^ η := Nat.floor_le (by positivity)
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  calc
    Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) ≤ Real.log (4 * x ^ η) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4 + η * Real.log x := by
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos η).ne',
        Real.log_rpow hxpos]
    _ ≤ (η + 2) * Real.log x := by
      have hfour : Real.log 4 = 2 * Real.log 2 := by
        simpa only [pow_two, Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num] using
          Real.log_pow (2 : ℝ) 2
      rw [hfour]
      nlinarith

/-- A crude integer count suffices for the logarithmic part of the prime sum. -/
theorem sum_log_twice_le {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : ∀ q ∈ S, 1 ≤ q ∧ q ≤ N) :
    (∑ q ∈ S, Real.log (2 * (q : ℝ))) ≤ ((N : ℝ) + 1) * Real.log (2 * (N : ℝ)) := by
  have hcard : S.card ≤ N + 1 := by
    apply (Finset.card_le_card ?_).trans_eq (Finset.card_range (N + 1))
    intro q hq
    exact Finset.mem_range.mpr (by have := (hS q hq).2; omega)
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * N))
  calc
    (∑ q ∈ S, Real.log (2 * (q : ℝ))) ≤ ∑ _q ∈ S, Real.log (2 * (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqp : 0 < (q : ℝ) := by exact_mod_cast (by have := (hS q hq).1; omega : 0 < q)
      have hqN : (q : ℝ) ≤ N := by exact_mod_cast (hS q hq).2
      exact Real.log_le_log (by positivity) (by linarith)
    _ = (S.card : ℝ) * Real.log (2 * (N : ℝ)) := by simp
    _ ≤ ((N : ℝ) + 1) * Real.log (2 * (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast hcard

noncomputable def splittingErrorEnvelope (C δ η x : ℝ) : ℝ :=
  ((⌊2 * x ^ η⌋₊ : ℝ) + 1) * C * x ^ (1 - δ) *
    Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) / Real.log x

theorem splittingErrorEnvelope_le {C δ η x : ℝ} (hC : 0 ≤ C)
    (hη : 0 ≤ η) (hx : 2 ≤ x) :
    splittingErrorEnvelope C δ η x ≤ (3 * C * (η + 2)) * x ^ (1 - δ + η) := by
  have hxpos : 0 < x := by linarith
  have hp : 1 ≤ x ^ η := Real.one_le_rpow (by linarith) hη
  have hNle : (⌊2 * x ^ η⌋₊ : ℝ) + 1 ≤ 3 * x ^ η := by
    have := Nat.floor_le (show 0 ≤ 2 * x ^ η by positivity)
    linarith
  have hNpos : 1 ≤ (⌊2 * x ^ η⌋₊ : ℝ) := by exact_mod_cast moving_cutoff_pos hη hx
  have hlogN : 0 ≤ Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) := Real.log_nonneg (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  unfold splittingErrorEnvelope
  calc
    ((⌊2 * x ^ η⌋₊ : ℝ) + 1) * C * x ^ (1 - δ) *
        Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) / Real.log x ≤
        (3 * x ^ η) * C * x ^ (1 - δ) * ((η + 2) * Real.log x) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogx.le
      apply mul_le_mul _ (moving_cutoff_log_le hη hx) hlogN (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNle hC)
        (Real.rpow_nonneg hxpos.le _)
    _ = (3 * C * (η + 2)) * x ^ (1 - δ + η) := by
      rw [Real.rpow_add hxpos]
      field_simp

theorem splittingErrorEnvelope_isLittleO {C δ η : ℝ} (hC : 0 ≤ C)
    (hη : 0 ≤ η) (hηδ : η < δ) :
    splittingErrorEnvelope C δ η =o[atTop] (fun x : ℝ => x / Real.log x) := by
  apply IsBigO.trans_isLittleO (IsBigO.of_bound' ?_)
    (splitting_power_error_isLittleO (3 * C * (η + 2)) hηδ)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hNpos : 1 ≤ (⌊2 * x ^ η⌋₊ : ℝ) := by exact_mod_cast moving_cutoff_pos hη hx
  have hlogN : 0 ≤ Real.log (2 * (⌊2 * x ^ η⌋₊ : ℝ)) := Real.log_nonneg (by linarith)
  have hnonneg : 0 ≤ splittingErrorEnvelope C δ η x := by
    unfold splittingErrorEnvelope
    exact div_nonneg (mul_nonneg (by positivity) hlogN) (Real.log_pos (by linarith)).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (by positivity : 0 ≤ (3 * C * (η + 2)) * x ^ (1 - δ + η))]
  exact splittingErrorEnvelope_le hC hη hx

end SimultaneousPrimitiveRoots

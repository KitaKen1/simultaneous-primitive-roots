module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The original source length is negligible relative to every prime group

The source has R = ceil(L^0.52), N = 2R and N+1 visit positions. Both
the small-group lower bound exp(L^a) and the big-group lower bound exp(L^c)
are covered by an arbitrary fixed positive exponent. All eventual thresholds
are chosen before prime groups, visit subsets and lifespan coefficients.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open Filter

noncomputable def sourceMemoryLength (L : ℝ) : ℕ :=
  2 * Nat.ceil (L ^ ((13 : ℝ) / 25))

noncomputable def sourcePrimeLowerBound (c L : ℝ) : ℝ := Real.exp (L ^ c)

theorem source_prime_lower_bound_pos (c L : ℝ) : 0 < sourcePrimeLowerBound c L :=
  Real.exp_pos _

theorem source_memory_length_pos (L : ℝ) (hL : 0 < L) :
    0 < sourceMemoryLength L := by
  unfold sourceMemoryLength
  exact Nat.mul_pos (by norm_num) (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hL _))

theorem source_memory_length_upper (L : ℝ) (hL : 0 ≤ L) :
    (sourceMemoryLength L : ℝ) ≤ 2 * (L ^ ((13 : ℝ) / 25) + 1) := by
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hL ((13 : ℝ) / 25))).le
  simpa only [sourceMemoryLength, Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_left hceil (by norm_num : (0 : ℝ) ≤ 2)

theorem source_prime_lower_bound_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (sourcePrimeLowerBound c) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hc)

theorem source_rpow_div_prime_lower_bound_tendsto (s c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ s / sourcePrimeLowerBound c L) atTop (nhds 0) := by
  have h := ((tendsto_exp_div_rpow_atTop (s / c)).comp
    (tendsto_rpow_atTop hc)).inv_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  change (Real.exp (L ^ c) / (L ^ c) ^ (s / c))⁻¹ = L ^ s / Real.exp (L ^ c)
  have hcs : c * (s / c) = s := by field_simp
  rw [inv_div, ← Real.rpow_mul hL, hcs]

theorem source_visit_ratio_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => 2 * ((sourceMemoryLength L : ℝ) + 1) /
      sourcePrimeLowerBound c L) atTop (nhds 0) := by
  have hp := source_rpow_div_prime_lower_bound_tendsto ((13 : ℝ) / 25) c hc
  have hi := (source_prime_lower_bound_tendsto c hc).inv_tendsto_atTop
  have hu : Tendsto (fun L : ℝ =>
      4 * (L ^ ((13 : ℝ) / 25) / sourcePrimeLowerBound c L) +
      6 * (sourcePrimeLowerBound c L)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, Pi.inv_apply] using
      (hp.const_mul 4).add (hi.const_mul 6)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [] with L
    exact div_nonneg (by positivity) (source_prime_lower_bound_pos c L).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hb := source_memory_length_upper L hL
    have hd := source_prime_lower_bound_pos c L
    apply (div_le_iff₀ hd).mpr
    calc
      2 * ((sourceMemoryLength L : ℝ) + 1) ≤ 4 * L ^ ((13 : ℝ) / 25) + 6 := by
        linarith
      _ = _ := by field_simp

theorem source_visit_ratio_eventually_small (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, 2 * ((sourceMemoryLength L : ℝ) + 1) /
      sourcePrimeLowerBound c L < ε :=
  (source_visit_ratio_tendsto c hc).eventually (gt_mem_nhds hε)

theorem source_prime_eventually_dominates_visits (c : ℝ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 2 * ((sourceMemoryLength L : ℝ) + 1) ≤
      sourcePrimeLowerBound c L := by
  filter_upwards [source_visit_ratio_eventually_small c 1 hc (by norm_num)] with L hL
  exact ((div_lt_one (source_prime_lower_bound_pos c L)).mp hL).le

theorem source_log_visit_ratio_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => 2 * ((sourceMemoryLength (Real.log x) : ℝ) + 1) /
      sourcePrimeLowerBound c (Real.log x)) atTop (nhds 0) :=
  (source_visit_ratio_tendsto c hc).comp Real.tendsto_log_atTop

end SimultaneousPrimitiveRoots.Unconditional.Graph

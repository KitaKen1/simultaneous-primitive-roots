module

public import SimultaneousPrimitiveRoots.QuotientHorizontalLogDerivative
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric Filter
open scoped Topology
noncomputable section

/-- A coarse fifth-power envelope avoids optimizing the height polynomial. -/
def horizontalQuotientGrowthConstant (B d : ℝ) : ℝ :=
  (diskLogDerivativeConstant + 16 * (1 + (9 * B + 4 * d) / Real.log 2) /
    Real.log (3 / 2)) * (1 + 9 * B + 4 * d)

theorem diskLogDerivativeConstant_pos : 0 < diskLogDerivativeConstant := by
  unfold diskLogDerivativeConstant
  have hlog : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  positivity

theorem horizontalQuotientGrowthConstant_nonneg {B d : ℝ} (hB : 0 ≤ B) (hd : 0 ≤ d) :
    0 ≤ horizontalQuotientGrowthConstant B d := by
  unfold horizontalQuotientGrowthConstant
  have := diskLogDerivativeConstant_pos
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)
  positivity

/-- The exact disk bound is polynomial in height under the existing growth
input. Dropping a harmless denominator gives a convenient fifth power. -/
theorem horizontal_logDeriv_bound_le_polynomial {N B d : ℝ}
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hd : 0 ≤ d) :
    (diskLogDerivativeConstant + 16 * (N + 5) *
      (1 + (B * (2 * N + 11) ^ 2 + 4 * d) / Real.log 2) / Real.log (3 / 2)) *
      (1 + B * (2 * N + 11) ^ 2 + 4 * d) / (4 * (N + 5)) ≤
        horizontalQuotientGrowthConstant B d * (N + 5) ^ 5 := by
  let L := N + 5
  let M := B * (2 * N + 11) ^ 2
  let A := 1 + 9 * B + 4 * d
  let F := 1 + (9 * B + 4 * d) / Real.log 2
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hm : M ≤ 9 * B * L ^ 2 := by
    have hh : (2 * N + 11) ^ 2 ≤ 9 * L ^ 2 := by dsimp [L]; nlinarith
    exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)
  have hmd : M + 4 * d ≤ (9 * B + 4 * d) * L ^ 2 := by
    have hh : 4 * d ≤ 4 * d * L ^ 2 := le_mul_of_one_le_right (by positivity) hL2
    nlinarith only [hm, hh]
  have ha : 1 + M + 4 * d ≤ A * L ^ 2 := by dsimp [A]; nlinarith only [hmd, hL2]
  have hf : 1 + (M + 4 * d) / Real.log 2 ≤ F * L ^ 2 := by
    calc 1 + (M + 4 * d) / Real.log 2
        ≤ L ^ 2 + ((9 * B + 4 * d) * L ^ 2) / Real.log 2 :=
          add_le_add hL2 (div_le_div_of_nonneg_right hmd hlog2.le)
      _ = F * L ^ 2 := by dsimp [F]; ring
  have hk : diskLogDerivativeConstant ≤ diskLogDerivativeConstant * L ^ 3 :=
    le_mul_of_one_le_right diskLogDerivativeConstant_pos.le hL3
  have hb : diskLogDerivativeConstant + 16 * L *
      (1 + (M + 4 * d) / Real.log 2) / Real.log (3 / 2) ≤
        (diskLogDerivativeConstant + 16 * F / Real.log (3 / 2)) * L ^ 3 := by
    calc _ ≤ diskLogDerivativeConstant * L ^ 3 +
        (16 * L * (F * L ^ 2)) / Real.log (3 / 2) := by
          exact add_le_add hk (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hf (by positivity)) hlog3.le)
      _ = _ := by ring
  have hp := mul_le_mul hb ha (by positivity : 0 ≤ 1 + M + 4 * d)
    (by have := diskLogDerivativeConstant_pos; positivity :
      0 ≤ (diskLogDerivativeConstant + 16 * F / Real.log (3 / 2)) * L ^ 3)
  have hd1 : 1 ≤ 4 * L := by linarith
  have hu : 0 ≤ (diskLogDerivativeConstant + 16 * L *
      (1 + (M + 4 * d) / Real.log 2) / Real.log (3 / 2)) * (1 + M + 4 * d) := by
    have := diskLogDerivativeConstant_pos; positivity
  apply (div_le_self hu hd1).trans
  convert hp using 1 <;> dsimp [horizontalQuotientGrowthConstant, L, M, A, F] <;> ring

theorem numberFieldEntireFullQuotientContinuation_exists_horizontal_polynomial_bound
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) :
    ∃ T : ℝ, N < T ∧ T < N + 1 ∧
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T →
        H s ≠ 0 ∧ ‖deriv H s / H s‖ ≤
          horizontalQuotientGrowthConstant B (Module.finrank ℚ E : ℝ) * (N + 5) ^ 5 := by
  have hb : ∀ z ∈ sphere (2 : ℂ) (4 * (N + 5)),
      ‖H z‖ ≤ Real.exp (B * (2 * N + 11) ^ 2) := by
    intro z hz
    have hh := hgrowth (2 * N + 8) (by linarith) z
    have hr : 2 * (2 * N + 8 + 2) = 4 * (N + 5) := by ring
    have hm : 2 * N + 8 + 3 = 2 * N + 11 := by ring
    rw [hr, hm] at hh
    exact hh hz
  obtain ⟨T, hl, hr, hh⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_horizontal_logDeriv_bound K E hH hN
      (by positivity : 0 ≤ B * (2 * N + 11) ^ 2) hb
  refine ⟨T, hl, hr, ?_⟩
  intro s hs hs2 hi
  have ht := hh s hs hs2 hi
  exact ⟨ht.1, ht.2.trans (horizontal_logDeriv_bound_le_polynomial hN hB (Nat.cast_nonneg _))⟩

/-- Any fixed coefficient is killed by the Gaussian height decay. -/
theorem gaussian_horizontal_polynomial_tendsto (C : ℝ) :
    Tendsto (fun N : ℝ => C * (N + 5) ^ 5 * Real.exp (-N ^ 2 / 4)) atTop (𝓝 0) := by
  have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((5 : ℕ) : ℝ) (1 / 4) (by norm_num)
  have hh' : Tendsto (fun N : ℝ => N ^ (5 : ℕ) * Real.exp (-(1 / 4) * N)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using hh
  have hu := hh'.const_mul (|C| * 6 ^ (5 : ℕ))
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hu)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with N hN
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N + 5) ^ 5),
    abs_of_pos (Real.exp_pos _)]
  have hp : (N + 5) ^ 5 ≤ 6 ^ (5 : ℕ) * N ^ 5 := by
    calc _ ≤ (6 * N) ^ 5 := by gcongr; linarith
      _ = _ := by ring
  have he : Real.exp (-N ^ 2 / 4) ≤ Real.exp (-(1 / 4) * N) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul hp he (Real.exp_pos _).le
      (by positivity : 0 ≤ 6 ^ (5 : ℕ) * N ^ 5)) (abs_nonneg C)
  simpa only [mul_assoc] using hh

end
end SimultaneousPrimitiveRoots

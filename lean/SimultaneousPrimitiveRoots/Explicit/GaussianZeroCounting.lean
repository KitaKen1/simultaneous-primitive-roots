module

public import SimultaneousPrimitiveRoots.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount

/-! Generalization of `SimultaneousPrimitiveRoots.GaussianZeroCounting` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Classical
noncomputable section

theorem numberFieldEntireFullQuotientContinuation_gaussianMass_of_quadratic_count
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ n : ℕ, (fullQuotientZeroCount H ((n : ℝ) + 1) : ℝ) ≤
      C * ((n : ℝ) + 4) ^ 2) :
    Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientZeroIndex H,
        Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤ C * gaussianZeroCountingConstant := by
  exact gaussianHeightMass_of_quadratic_count (fullQuotientIndexedZero H) hC
    (fun n => numberFieldEntireFullQuotientContinuation_finite_heightZeroIndex K L hH _)
    hcount

/-- A quantified boundary growth estimate supplies the actual Gaussian zero
mass. No separate zero-mass summability assumption is required. -/
theorem numberFieldEntireFullQuotientContinuation_gaussianMass_of_boundary_growth
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp (B * (T + 3) ^ 2)) :
    Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientZeroIndex H,
        Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤
          ((B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) * gaussianZeroCountingConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ (Module.finrank ℚ L : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ (B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := by positivity
  apply numberFieldEntireFullQuotientContinuation_gaussianMass_of_quadratic_count K L hH hC
  intro n
  have ht : 0 ≤ (n : ℝ) + 1 := by positivity
  have hm : 1 ≤ Real.exp (B * ((n : ℝ) + 1 + 3) ^ 2) := by
    simpa using Real.exp_le_exp.mpr (mul_nonneg hB (sq_nonneg ((n : ℝ) + 1 + 3)))
  have h := numberFieldEntireFullQuotientContinuation_zeroCount_jensen_le K L hH ht hm
    (hb ((n : ℝ) + 1) ht)
  rw [Real.log_exp, show (n : ℝ) + 1 + 3 = (n : ℝ) + 4 by ring] at h
  apply h.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog.le
  have hp : 1 ≤ ((n : ℝ) + 4) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

end
end SimultaneousPrimitiveRoots.Explicit

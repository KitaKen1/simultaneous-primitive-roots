module

public import SimultaneousPrimitiveRoots.QuotientLeftHeightBands
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.QuotientDiskLogDerivative
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.FiniteZeroSeparation
public import SimultaneousPrimitiveRoots.Explicit.QuotientHorizontalLogDerivative
public import SimultaneousPrimitiveRoots.Explicit.HorizontalQuotientGrowth
public import SimultaneousPrimitiveRoots.Explicit.QuotientSpatialAverage

/-! Generalization of `SimultaneousPrimitiveRoots.QuotientLeftHeightBands` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Metric MeasureTheory Set
noncomputable section

/-- Coarse disk areas suffice: a fourth-power height loss is still harmless
for Gaussian integration. No exact rectangle area calculation is required. -/
theorem numberFieldEntireFullQuotientContinuation_left_band_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : EntireZeroData K E H)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) (n : ℕ) :
    IntegrableOn (fun s : ℂ => deriv H s / H s) (negativeStripHeightBand n) ∧
      (∫ s : ℂ in negativeStripHeightBand n, ‖deriv H s / H s‖) ≤
        quotientLeftSpatialConstant B (Module.finrank ℚ E : ℝ) * ((n : ℝ) + 5) ^ 4 := by
  let N : ℝ := n
  let L := N + 5
  let d : ℝ := Module.finrank ℚ E
  let V : ℝ := (volume (negativeStripHeightBand n)).toReal
  have hL : 1 ≤ L := by dsimp [L, N]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hb : ∀ z ∈ sphere (2 : ℂ) (4 * L),
      ‖H z‖ ≤ Real.exp (B * (2 * N + 11) ^ 2) := by
    intro z hz
    have hh := hgrowth (2 * N + 8) (by dsimp [N]; positivity) z
    have hr : 2 * (2 * N + 8 + 2) = 4 * L := by dsimp [L]; ring
    rw [hr, show 2 * N + 8 + 3 = 2 * N + 11 by ring] at hh
    exact hh hz
  have hi := numberFieldEntireFullQuotientContinuation_logDeriv_spatial_integral_le K E hH
    (D := 4 * L) (M := B * (2 * N + 11) ^ 2) (by positivity) (by positivity) hb
    (negativeStripHeightBand_measurable n) (negativeStripHeightBand_volume_ne_top n)
    (by simpa [L, N] using
      negativeStripHeightBand_subset_closedBall n)
  refine ⟨hi.1, hi.2.trans ?_⟩
  have hV : V ≤ Real.pi * L ^ 2 := negativeStripHeightBand_area_le n
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hA : 1 + B * (2 * N + 11) ^ 2 + 4 * d ≤ (1 + 9 * B + 4 * d) * L ^ 2 := by
    have hn : 0 ≤ N := Nat.cast_nonneg n
    have hp : (2 * N + 11) ^ 2 ≤ 9 * L ^ 2 := by dsimp [L]; nlinarith
    have hb' := mul_le_mul_of_nonneg_left hp hB
    have hd' : 4 * d ≤ 4 * d * L ^ 2 := le_mul_of_one_le_right (by positivity) hL2
    nlinarith only [hb', hd', hL2]
  have hcoef : diskLogDerivativeConstant * V / (4 * L) +
      (2 * Real.pi + V) / Real.log (3 / 2) ≤
        Real.pi * (diskLogDerivativeConstant + 3 / Real.log (3 / 2)) * L ^ 2 := by
    have h1 : diskLogDerivativeConstant * V / (4 * L) ≤
        diskLogDerivativeConstant * (Real.pi * L ^ 2) := by
      apply (div_le_self (by have := diskLogDerivativeConstant_pos; positivity)
        (by linarith : 1 ≤ 4 * L)).trans
      exact mul_le_mul_of_nonneg_left hV diskLogDerivativeConstant_pos.le
    have h2 : 2 * Real.pi + V ≤ 3 * Real.pi * L ^ 2 := by
      have hp := mul_le_mul_of_nonneg_left hL2 (by positivity : 0 ≤ 2 * Real.pi)
      nlinarith only [hp, hV]
    have hh := add_le_add h1 (div_le_div_of_nonneg_right h2 hlog.le)
    convert hh using 1 <;> first | rfl | ring
  have hh := mul_le_mul hcoef hA (by positivity)
    (by have := diskLogDerivativeConstant_pos; positivity)
  convert hh using 1 <;> (try rfl) <;> dsimp [quotientLeftSpatialConstant, L, N, d, V] <;> ring

end
end SimultaneousPrimitiveRoots.Explicit

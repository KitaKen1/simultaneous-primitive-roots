module

public import SimultaneousPrimitiveRoots.GaussianLeftSpatialIntegral
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
public import SimultaneousPrimitiveRoots.Explicit.QuotientLeftHeightBands
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientRectangle
public import SimultaneousPrimitiveRoots.Explicit.GaussianHorizontalIntegral
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientLeftZeroCount

/-! Generalization of `SimultaneousPrimitiveRoots.GaussianLeftSpatialIntegral` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Metric MeasureTheory Set Function
noncomputable section

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_measurable
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : EntireZeroData K E H)
    {x : ℝ} (hx : 0 < x) (d : ℂ) :
    Measurable (gaussianFullQuotientIntegrand H d x) := by
  have hc : Continuous (gaussianQuotientContourKernel x) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (gaussianQuotientContourKernel_analyticAt hx s).continuousAt)
  exact hc.measurable.mul
    ((hH.1.deriv.continuous.measurable.div hH.1.continuous.measurable).neg.div_const d)

theorem numberFieldEntireFullQuotientContinuation_gaussian_left_band_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : EntireZeroData K E H)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) {x : ℝ} (hx : 1 ≤ x) (d : ℂ) (n : ℕ) :
    IntegrableOn (gaussianFullQuotientIntegrand H d x) (negativeStripHeightBand n) ∧
      (∫ s : ℂ in negativeStripHeightBand n, ‖gaussianFullQuotientIntegrand H d x s‖) ≤
        (artinGaussianConstant * quotientLeftSpatialConstant B (Module.finrank ℚ E : ℝ) / ‖d‖) *
          gaussianLeftSpatialSeries n := by
  let C := artinGaussianConstant * Real.exp (-(n : ℝ) ^ 2 / 4) / ‖d‖
  have hC : 0 ≤ C := by dsimp [C, artinGaussianConstant]; positivity
  obtain ⟨hi, hb⟩ := numberFieldEntireFullQuotientContinuation_left_band_integral_le K E hH hB
    hgrowth n
  have hp : ∀ s ∈ negativeStripHeightBand n, ‖gaussianFullQuotientIntegrand H d x s‖ ≤
      C * ‖deriv H s / H s‖ := by
    intro s hs
    have he : Real.exp (-s.im ^ 2 / 4) ≤ Real.exp (-(n : ℝ) ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [hs.2.2.1, sq_abs s.im]
    have hk := (gaussianQuotientContourKernel_norm_le_left hx ⟨hs.1, hs.2.1⟩).trans
      (mul_le_mul_of_nonneg_left he (by unfold artinGaussianConstant; positivity))
    rw [gaussianFullQuotientIntegrand, norm_mul, fullQuotientSignedLogDerivative,
      norm_div, norm_neg, logDeriv_apply]
    have hh := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ ‖deriv H s / H s‖ / ‖d‖)
    convert hh using 1 <;> (try rfl) <;> dsimp [C] <;> ring
  have hm := hi.norm.mul_const C
  have hm' : IntegrableOn (fun s : ℂ => C * ‖deriv H s / H s‖) (negativeStripHeightBand n) := by
    simpa only [IntegrableOn, mul_comm] using hm
  have hf : IntegrableOn (gaussianFullQuotientIntegrand H d x) (negativeStripHeightBand n) :=
    hm'.mono'
      (numberFieldEntireFullQuotientContinuation_gaussian_integrand_measurable K E hH
        (by linarith : 0 < x) d).aestronglyMeasurable.restrict
      (by filter_upwards [self_mem_ae_restrict (negativeStripHeightBand_measurable n)] with s hs
          exact hp s hs)
  refine ⟨hf, ?_⟩
  have hh := setIntegral_mono_on hf.norm hm' (negativeStripHeightBand_measurable n) hp
  rw [integral_const_mul] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hb hC)
  convert hh' using 1 <;> (try rfl) <;> dsimp [C, gaussianLeftSpatialSeries] <;> ring

/-- A spatial Gaussian L1 bound on the whole negative strip. The constant is
independent of x >= 1, and the actual integrability is part of the conclusion. -/
theorem numberFieldEntireFullQuotientContinuation_gaussian_left_spatial_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : EntireZeroData K E H)
    {B : ℝ} (hB : 0 ≤ B)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) {x : ℝ} (hx : 1 ≤ x) (d : ℂ) :
    IntegrableOn (gaussianFullQuotientIntegrand H d x) negativeClosedStrip ∧
      (∫ s : ℂ in negativeClosedStrip, ‖gaussianFullQuotientIntegrand H d x s‖) ≤
        (artinGaussianConstant * quotientLeftSpatialConstant B (Module.finrank ℚ E : ℝ) / ‖d‖) *
          gaussianLeftSpatialConstant := by
  let C := artinGaussianConstant * quotientLeftSpatialConstant B (Module.finrank ℚ E : ℝ) / ‖d‖
  have hC : 0 ≤ C := by
    dsimp [C]
    have := quotientLeftSpatialConstant_nonneg hB (Nat.cast_nonneg (Module.finrank ℚ E))
    unfold artinGaussianConstant
    positivity
  have hi := fun n => numberFieldEntireFullQuotientContinuation_gaussian_left_band_integral_le
    K E hH hB hgrowth hx d n
  have hm := gaussianLeftSpatialSeries_summable.mul_left C
  have hs : Summable (fun n => ∫ s : ℂ in negativeStripHeightBand n,
      ‖gaussianFullQuotientIntegrand H d x s‖) :=
    hm.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun n => (hi n).2)
  have hf := integrableOn_iUnion_of_summable_integral_norm (fun n => (hi n).1) hs
  rw [← negativeClosedStrip_eq_iUnion_heightBand] at hf
  refine ⟨hf, ?_⟩
  rw [negativeClosedStrip_eq_iUnion_heightBand, integral_iUnion
    negativeStripHeightBand_measurable negativeStripHeightBand_pairwise_disjoint
    (by rw [← negativeClosedStrip_eq_iUnion_heightBand]; exact hf.norm)]
  exact (hs.tsum_le_tsum (fun n => (hi n).2) hm).trans_eq (tsum_mul_left)

end
end SimultaneousPrimitiveRoots.Explicit

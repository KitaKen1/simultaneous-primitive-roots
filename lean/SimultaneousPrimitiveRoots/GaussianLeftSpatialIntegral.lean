module

public import SimultaneousPrimitiveRoots.QuotientLeftHeightBands
public import SimultaneousPrimitiveRoots.GaussianHorizontalIntegral
public import SimultaneousPrimitiveRoots.GaussianLeftZeroBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric MeasureTheory Set Function
noncomputable section

def gaussianLeftSpatialSeries (n : ℕ) : ℝ :=
  ((n : ℝ) + 5) ^ 4 * Real.exp (-(n : ℝ) ^ 2 / 4)

def gaussianLeftSpatialConstant : ℝ := ∑' n : ℕ, gaussianLeftSpatialSeries n

def negativeClosedStrip : Set ℂ := {s : ℂ | -1 ≤ s.re ∧ s.re ≤ 0}

theorem gaussianLeftSpatialSeries_nonneg (n : ℕ) : 0 ≤ gaussianLeftSpatialSeries n := by
  unfold gaussianLeftSpatialSeries
  positivity

theorem gaussianLeftSpatialSeries_summable : Summable gaussianLeftSpatialSeries := by
  let r : ℝ := Real.exp (-(1 : ℝ) / 4)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hs3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hr
  have hs4 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 4 hr
  have hp : Summable (fun n : ℕ => ((n : ℝ) + 5) ^ 4 * r ^ n) := by
    convert (((hs4.add (hs3.mul_left 20)).add (hs2.mul_left 150)).add
      (hs1.mul_left 500)).add (hs0.mul_left 625) using 1 <;>
      first | rfl | (funext n; ring)
  apply hp.of_nonneg_of_le gaussianLeftSpatialSeries_nonneg
  intro n
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change Real.exp (-(n : ℝ) ^ 2 / 4) ≤ Real.exp (-(1 : ℝ) / 4) ^ n
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)
  nlinarith

theorem gaussianLeftSpatialConstant_nonneg : 0 ≤ gaussianLeftSpatialConstant :=
  tsum_nonneg gaussianLeftSpatialSeries_nonneg

theorem negativeStripHeightBand_pairwise_disjoint :
    Pairwise (Disjoint on negativeStripHeightBand) := by
  intro n m hnm
  change Disjoint (negativeStripHeightBand n) (negativeStripHeightBand m)
  rw [Set.disjoint_left]
  intro s hn hm
  change -1 ≤ s.re ∧ s.re ≤ 0 ∧ (n : ℝ) ≤ |s.im| ∧ |s.im| < (n : ℝ) + 1 at hn
  change -1 ≤ s.re ∧ s.re ≤ 0 ∧ (m : ℝ) ≤ |s.im| ∧ |s.im| < (m : ℝ) + 1 at hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
    linarith [hn.2.2.2, hm.2.2.1]
  · have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith [hm.2.2.2, hn.2.2.1]

theorem negativeClosedStrip_eq_iUnion_heightBand :
    negativeClosedStrip = ⋃ n : ℕ, negativeStripHeightBand n := by
  ext s
  constructor
  · intro hs
    apply Set.mem_iUnion.mpr
    refine ⟨⌊|s.im|⌋₊, hs.1, hs.2, Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩
  · intro hs
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
    exact ⟨hn.1, hn.2.1⟩

theorem gaussianQuotientContourKernel_norm_le_left {x : ℝ} (hx : 1 ≤ x)
    {s : ℂ} (hs : -1 ≤ s.re ∧ s.re ≤ 0) :
    ‖gaussianQuotientContourKernel x s‖ ≤
      artinGaussianConstant * Real.exp (-s.im ^ 2 / 4) := by
  have hm : ‖artinGaussianMellin s‖ ≤ artinGaussianConstant * Real.exp (-s.im ^ 2 / 4) := by
    rw [artinGaussianMellin_norm, artinGaussianConstant, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [hs.1, hs.2]
  rw [gaussianQuotientContourKernel_eq (by linarith : 0 < x), norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
  calc x ^ s.re * ‖artinGaussianMellin s‖ ≤ 1 * ‖artinGaussianMellin s‖ :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hx hs.2) (norm_nonneg _)
    _ ≤ _ := by simpa using hm

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_measurable
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {x : ℝ} (hx : 0 < x) (d : ℂ) :
    Measurable (gaussianFullQuotientIntegrand H d x) := by
  have hc : Continuous (gaussianQuotientContourKernel x) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (gaussianQuotientContourKernel_analyticAt hx s).continuousAt)
  exact hc.measurable.mul
    ((hH.1.deriv.continuous.measurable.div hH.1.continuous.measurable).neg.div_const d)

theorem numberFieldEntireFullQuotientContinuation_gaussian_left_band_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
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
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
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
end SimultaneousPrimitiveRoots

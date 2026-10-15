module

public import SimultaneousPrimitiveRoots.KummerQuotientRectangle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric MeasureTheory
noncomputable section

def gaussianHorizontalKernelConstant : ℝ :=
  Real.sqrt Real.pi * Real.exp ((Real.log 2) ^ 2 + 1)

theorem gaussianHorizontalKernelConstant_pos : 0 < gaussianHorizontalKernelConstant := by
  exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)

theorem gaussianQuotientContourKernel_norm_le_horizontal {x : ℝ} (hx : 1 ≤ x)
    {s : ℂ} (hs : -1 ≤ s.re ∧ s.re ≤ 2) :
    ‖gaussianQuotientContourKernel x s‖ ≤
      gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-s.im ^ 2 / 4) := by
  have hx0 : 0 < x := by linarith
  have hp : x ^ s.re ≤ x ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hx hs.2
  have hm : ‖artinGaussianMellin s‖ ≤ gaussianHorizontalKernelConstant *
      Real.exp (-s.im ^ 2 / 4) := by
    rw [artinGaussianMellin_norm, gaussianHorizontalKernelConstant, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ s.re + 2) (by linarith : 0 ≤ 2 - s.re)]
  rw [gaussianQuotientContourKernel_eq hx0, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hh := mul_le_mul hp hm (norm_nonneg _) (sq_nonneg x)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

theorem gaussianFullQuotientIntegrand_norm_le_horizontal {H : ℂ → ℂ} {d s : ℂ}
    {x L : ℝ} (hx : 1 ≤ x) (hs : -1 ≤ s.re ∧ s.re ≤ 2)
    (hL : ‖deriv H s / H s‖ ≤ L) :
    ‖gaussianFullQuotientIntegrand H d x s‖ ≤
      gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-s.im ^ 2 / 4) * L / ‖d‖ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  rw [gaussianFullQuotientIntegrand, norm_mul, fullQuotientSignedLogDerivative,
    norm_div, norm_neg, logDeriv_apply]
  have hh := mul_le_mul (gaussianQuotientContourKernel_norm_le_horizontal hx hs)
    (div_le_div_of_nonneg_right hL (norm_nonneg d)) (by positivity)
    (by have := gaussianHorizontalKernelConstant_pos; positivity)
  simpa only [mul_div_assoc] using hh

theorem numberFieldEntireFullQuotientContinuation_gaussian_integrand_analyticAt
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {x : ℝ} (hx : 0 < x) {d s : ℂ} (hs : H s ≠ 0) :
    AnalyticAt ℂ (gaussianFullQuotientIntegrand H d x) s := by
  change AnalyticAt ℂ (fun z => gaussianQuotientContourKernel x z * (-logDeriv H z / d)) s
  simp only [logDeriv_apply]
  exact (gaussianQuotientContourKernel_analyticAt hx s).mul
    (((hH.1.deriv s (Set.mem_univ _)).div (hH.1 s (Set.mem_univ _)) hs).neg.div_const)

/-- A zero-free vertical line has actual integrability on every finite segment. -/
theorem numberFieldEntireFullQuotientContinuation_vertical_intervalIntegrable
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {x σ : ℝ} {d : ℂ} (hx : 0 < x)
    (hline : ∀ s : ℂ, s.re = σ → H s ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => gaussianFullQuotientIntegrand H d x
      ((σ : ℂ) + y * Complex.I)) volume a b := by
  have hc : Continuous (fun y : ℝ => gaussianFullQuotientIntegrand H d x
      ((σ : ℂ) + y * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hh := (numberFieldEntireFullQuotientContinuation_gaussian_integrand_analyticAt
      K E hH (d := d) hx (hline ((σ : ℂ) + y * Complex.I) (by simp))).continuousAt
    have hmap : ContinuousAt (fun v : ℝ => (σ : ℂ) + v * Complex.I) y := by fun_prop
    exact ContinuousAt.comp (f := fun v : ℝ => (σ : ℂ) + v * Complex.I)
      (g := gaussianFullQuotientIntegrand H d x) hh hmap
  exact hc.intervalIntegrable a b

/-- Actual integrability on the edge is included; the norm estimate is not
obtained merely by assigning zero to an undefined interval integral. -/
theorem numberFieldEntireFullQuotientContinuation_horizontal_integral_le
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K E H)
    {x σ y L : ℝ} {d : ℂ} (hx : 1 ≤ x) (hσ : -1 ≤ σ) (hσ2 : σ ≤ 2)
    (hL : 0 ≤ L)
    (hedge : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 → s.im = y →
      H s ≠ 0 ∧ ‖deriv H s / H s‖ ≤ L) :
    IntervalIntegrable (fun u : ℝ => gaussianFullQuotientIntegrand H d x
      ((u : ℂ) + y * Complex.I)) volume σ 2 ∧
    ‖PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 y‖ ≤
      (3 / (2 * Real.pi)) *
        (gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-y ^ 2 / 4) * L / ‖d‖) := by
  have he : ∀ u ∈ Set.Icc σ 2,
      H ((u : ℂ) + y * Complex.I) ≠ 0 ∧
        ‖deriv H ((u : ℂ) + y * Complex.I) / H ((u : ℂ) + y * Complex.I)‖ ≤ L := by
    intro u hu
    exact hedge _ (by simpa using hu.1) (by simpa using hu.2) (by simp)
  have hc : ContinuousOn (fun u : ℝ => gaussianFullQuotientIntegrand H d x
      ((u : ℂ) + y * Complex.I)) (Set.Icc σ 2) := by
    intro u hu
    have hh := (numberFieldEntireFullQuotientContinuation_gaussian_integrand_analyticAt
      K E hH (d := d) (x := x) (s := (u : ℂ) + y * Complex.I)
        (by linarith : 0 < x) (he u hu).1).continuousAt
    have hmap : ContinuousAt (fun v : ℝ => (v : ℂ) + y * Complex.I) u := by fun_prop
    exact (ContinuousAt.comp (f := fun v : ℝ => (v : ℂ) + y * Complex.I)
      (g := gaussianFullQuotientIntegrand H d x) hh hmap).continuousWithinAt
  refine ⟨hc.intervalIntegrable_of_Icc hσ2, ?_⟩
  let C := gaussianHorizontalKernelConstant * x ^ 2 * Real.exp (-y ^ 2 / 4) * L / ‖d‖
  have hC : 0 ≤ C := by dsimp [C]; have := gaussianHorizontalKernelConstant_pos; positivity
  have hi : ‖∫ u : ℝ in σ..2,
      gaussianFullQuotientIntegrand H d x ((u : ℂ) + y * Complex.I)‖ ≤ C * |2 - σ| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : u ∈ Set.Icc σ 2 := by
      have huoc : u ∈ Set.Ioc σ 2 := by simpa only [Set.uIoc_of_le hσ2] using hu
      exact ⟨huoc.1.le, huoc.2⟩
    have hh := gaussianFullQuotientIntegrand_norm_le_horizontal (H := H) (d := d) (L := L) hx
      (s := (u : ℂ) + y * Complex.I)
      (by simpa using (show -1 ≤ u ∧ u ≤ 2 from ⟨hσ.trans hu'.1, hu'.2⟩))
      (he u hu').2
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using hh
  have hn : ‖(1 : ℂ) / (2 * Real.pi * Complex.I)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
  unfold PNTAnd.HIntegral' PNTAnd.HIntegral
  rw [norm_smul, hn]
  have hlen : |2 - σ| ≤ 3 := by rw [abs_of_nonneg (by linarith)]; linarith
  calc (1 / (2 * Real.pi)) * ‖∫ u : ℝ in σ..2,
      gaussianFullQuotientIntegrand H d x ((u : ℂ) + y * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) * (C * |2 - σ|) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (C * 3) := by gcongr
    _ = _ := by dsimp [C]; ring

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.MultiplicativeMellinConvolution
public import SimultaneousPrimitiveRoots.ReflectionKernelMellin
public import Mathlib.Analysis.MellinInversion

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution FourierTransform
noncomputable section

def reflectionKernelReciprocal (C A : ℝ) (r : ℕ) (T : ℝ) : ℂ :=
  reflectionKernel C A r T⁻¹

def reflectionMellinSmoothing (C A : ℝ) (r : ℕ) (V : ℝ → ℂ) : ℝ → ℂ :=
  artinMultiplicativeConvolution (reflectionKernelReciprocal C A r) V

theorem reflectionKernelReciprocal_mellin_convergent (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) (z : ℂ) :
    MellinConvergent (reflectionKernelReciprocal C A r) z := by
  have heq : artinMellinLogPullback (reflectionKernelReciprocal C A r) z =
      fun v => artinMellinLogPullback (reflectionKernel C A r) (-z) (-v) := by
    funext v
    simp [artinMellinLogPullback, reflectionKernelReciprocal, Real.exp_neg]
  rw [artinMellin_convergent_iff_logPullback, heq]
  exact ((artinMellin_convergent_iff_logPullback (reflectionKernel C A r) (-z)).mp
    (reflectionKernel_mellin_convergent C hA r (-z))).comp_neg

theorem reflectionKernelReciprocal_mellin (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (z : ℂ) :
    mellin (reflectionKernelReciprocal C A r) z = reflectionGammaQuotient C A r z := by
  have h := mellin_comp_rpow (reflectionKernel C A r) z (-1)
  simp only [Real.rpow_neg_one, abs_neg, abs_one, inv_one, one_smul,
    Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] at h
  exact h.trans (reflectionKernel_mellin_neg C hA r z)

theorem reflectionKernelReciprocal_logPullback (C A : ℝ) (r : ℕ) (v : ℝ) :
    artinMellinLogPullback (reflectionKernelReciprocal C A r) 0 v =
      reflectionKernel C A r (Real.exp v) := by
  simp [artinMellinLogPullback, reflectionKernelReciprocal, Real.exp_neg]

theorem reflectionKernelReciprocal_logPullback_continuous (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) :
    Continuous (artinMellinLogPullback (reflectionKernelReciprocal C A r) 0) := by
  have hc : Continuous (fun v => reflectionKernel C A r (Real.exp v)) :=
    (reflectionKernel_continuousOn C hA r).comp_continuous Real.continuous_exp
      (fun v => Real.exp_pos v)
  have heq := funext (reflectionKernelReciprocal_logPullback C A r)
  rw [heq]
  exact hc

theorem reflectionKernelReciprocal_logPullback_bounded (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) :
    BddAbove (range fun v => ‖artinMellinLogPullback
      (reflectionKernelReciprocal C A r) 0 v‖) := by
  obtain ⟨M, _, hb⟩ := reflectionKernel_power_bound C hA r 0
  refine ⟨M, ?_⟩
  rintro _ ⟨v, rfl⟩
  simpa only [reflectionKernelReciprocal_logPullback, Real.rpow_zero, mul_one]
    using hb (Real.exp v) (Real.exp_pos v)

theorem reflectionMellinSmoothing_mellin_convergent (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ} {z : ℂ} (hV : MellinConvergent V z) :
    MellinConvergent (reflectionMellinSmoothing C A r V) z :=
  artinMultiplicativeConvolution_mellin_convergent
    (reflectionKernelReciprocal_mellin_convergent C hA r z) hV

theorem reflectionMellinSmoothing_log (C A : ℝ) (r : ℕ) (V : ℝ → ℂ)
    {u : ℝ} (hu : 0 < u) :
    reflectionMellinSmoothing C A r V u = convolution
      (artinMellinLogPullback (reflectionKernelReciprocal C A r) 0)
      (artinMellinLogPullback V 0) (ContinuousLinearMap.mul ℂ ℂ) volume (-Real.log u) := by
  have h := artinMellinLogPullback_convolution (reflectionKernelReciprocal C A r) V
    0 (-Real.log u)
  simpa only [artinMellinLogPullback, zero_mul, neg_zero, Complex.exp_zero, one_mul,
    neg_neg, Real.exp_log hu, reflectionMellinSmoothing] using h

/-- Only absolute Mellin integrability of V at zero is used. No continuity
assumption on V is needed to recover pointwise continuity of the smoothing. -/
theorem reflectionMellinSmoothing_continuousOn (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) {V : ℝ → ℂ} (hV : MellinConvergent V 0) :
    ContinuousOn (reflectionMellinSmoothing C A r V) (Ioi 0) := by
  have hc := (reflectionKernelReciprocal_logPullback_bounded C hA r).continuous_convolution_left_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      (reflectionKernelReciprocal_logPullback_continuous C hA r)
      ((artinMellin_convergent_iff_logPullback V 0).mp hV)
  have hlog : ContinuousOn (fun u : ℝ => -Real.log u) (Ioi 0) :=
    (Real.continuousOn_log.mono (fun _ hu => ne_of_gt hu)).neg
  have hcomp := hc.continuousOn.comp hlog (mapsTo_univ _ _)
  apply hcomp.congr
  intro u hu
  exact reflectionMellinSmoothing_log C A r V hu

/-- The defining smoothing integral is absolutely convergent at every positive
point. This is stronger than almost-everywhere existence for two L1 factors. -/
theorem reflectionMellinSmoothing_integrand_integrable (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ} (hV : MellinConvergent V 0)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun T => reflectionKernel C A r T * V (u * T))
      artinPositiveMultiplicativeMeasure := by
  have hv : Integrable V artinPositiveMultiplicativeMeasure := by
    simpa only [Complex.cpow_zero, one_mul] using
      (artinMellin_convergent_iff_multiplicative V 0).mp hV
  have hvu := (artinMultiplicative_integrable_comp_mul_iff V hu).mpr hv
  have hvlog := (artinPositiveMultiplicative_integrable_exp_iff
    (fun T => V (u * T))).mp hvu
  have hk : Continuous (fun v => reflectionKernel C A r (Real.exp v)) :=
    (reflectionKernel_continuousOn C hA r).comp_continuous Real.continuous_exp
      (fun v => Real.exp_pos v)
  obtain ⟨M, _, hb⟩ := reflectionKernel_power_bound C hA r 0
  rw [artinPositiveMultiplicative_integrable_exp_iff]
  apply hvlog.bdd_mul (c := M) hk.aestronglyMeasurable
  apply ae_of_all
  intro v
  simpa only [Real.rpow_zero, mul_one] using hb (Real.exp v) (Real.exp_pos v)

theorem reflectionMellinSmoothing_integral (C A : ℝ) (r : ℕ) (V : ℝ → ℂ) (u : ℝ) :
    reflectionMellinSmoothing C A r V u =
      ∫ T, reflectionKernel C A r T * V (u * T) ∂artinPositiveMultiplicativeMeasure := by
  rw [reflectionMellinSmoothing, artinMultiplicativeConvolution,
    artinPositiveMultiplicative_integral_exp, artinPositiveMultiplicative_integral_exp]
  have heq : (fun v : ℝ => reflectionKernelReciprocal C A r (Real.exp v) *
      V (u / Real.exp v)) =
      fun v => (fun w : ℝ => reflectionKernel C A r (Real.exp w) * V (u * Real.exp w)) (-v) := by
    funext v
    simp [reflectionKernelReciprocal, Real.exp_neg, div_eq_mul_inv]
  rw [heq]
  exact integral_neg_eq_self
    (fun v : ℝ => reflectionKernel C A r (Real.exp v) * V (u * Real.exp v)) volume

theorem reflectionGammaQuotient_cancel {C A : ℝ} (hC : C ≠ 0) (hA : 0 < A)
    (r : ℕ) {z : ℂ} (hz : -(5 / 6 : ℝ) < z.re) :
    reflectionGammaQuotient C A r z *
      ((C : ℂ) * (A : ℂ) ^ z * (Complex.Gamma (z + 5 / 6) *
        Complex.Gamma (z + 7 / 6)) ^ r) = Complex.exp (z ^ 2) := by
  have hg1 : Complex.Gamma (z + 5 / 6) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hg2 : Complex.Gamma (z + 7 / 6) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have h := congrArg Complex.re hn
    simp at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have ha : (A : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hA)))
  have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hC
  have hginv : ((Complex.Gamma (z + 5 / 6))⁻¹ *
      (Complex.Gamma (z + 7 / 6))⁻¹) ^ r =
      ((Complex.Gamma (z + 5 / 6) * Complex.Gamma (z + 7 / 6)) ^ r)⁻¹ := by
    rw [← inv_pow, mul_inv_rev, mul_comm]
  rw [reflectionGammaQuotient, Complex.cpow_neg, hginv]
  have he : (C : ℂ)⁻¹ * ((A : ℂ) ^ z)⁻¹ * Complex.exp (z ^ 2) *
      ((Complex.Gamma (z + 5 / 6) * Complex.Gamma (z + 7 / 6)) ^ r)⁻¹ *
      ((C : ℂ) * (A : ℂ) ^ z * (Complex.Gamma (z + 5 / 6) *
        Complex.Gamma (z + 7 / 6)) ^ r) =
      Complex.exp (z ^ 2) * ((C : ℂ)⁻¹ * C) *
        (((A : ℂ) ^ z)⁻¹ * (A : ℂ) ^ z) *
        (((Complex.Gamma (z + 5 / 6) * Complex.Gamma (z + 7 / 6)) ^ r)⁻¹ *
          (Complex.Gamma (z + 5 / 6) * Complex.Gamma (z + 7 / 6)) ^ r) := by ring
  rw [he, inv_mul_cancel₀ hC', inv_mul_cancel₀ ha,
    inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero hg1 hg2)), mul_one, mul_one, mul_one]

def reflectionLogGaussian (u : ℝ) : ℂ :=
  (1 / (2 * Real.sqrt Real.pi) : ℂ) * Complex.exp (-((Real.log u : ℂ) ^ 2) / 4)

end
end SimultaneousPrimitiveRoots

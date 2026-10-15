module

public import SimultaneousPrimitiveRoots.ReflectionGaussianSmoothing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable section

/-- Absolute convergence at zero suffices for every purely imaginary Mellin exponent. -/
theorem artinMellin_vertical_convergent {V : ℝ → ℂ} (hV : MellinConvergent V 0)
    (y : ℝ) : MellinConvergent V ((y : ℂ) * I) := by
  have hv := (artinMellin_convergent_iff_logPullback V 0).mp hV
  have he : artinMellinLogPullback V 0 = fun v => V (Real.exp (-v)) := by
    funext v
    simp [artinMellinLogPullback]
  rw [he] at hv
  rw [artinMellin_convergent_iff_logPullback]
  change Integrable (fun v : ℝ => Complex.exp (-((y : ℂ) * I) * v) * V (Real.exp (-v)))
  have hc : Continuous (fun v : ℝ => Complex.exp (-((y : ℂ) * I) * v)) := by fun_prop
  have hn : ∀ v : ℝ, ‖Complex.exp (-((y : ℂ) * I) * v)‖ = 1 := by
    intro v
    have he : -((y : ℂ) * I) * v = ((-y * v : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  exact hv.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun v => (hn v).le))

theorem artinMellin_convergent_congr_ae {V W : ℝ → ℂ}
    (hVW : V =ᵐ[artinPositiveMultiplicativeMeasure] W) (s : ℂ) :
    MellinConvergent V s ↔ MellinConvergent W s := by
  rw [artinMellin_convergent_iff_multiplicative,
    artinMellin_convergent_iff_multiplicative]
  exact integrable_congr (hVW.mono (fun T hT => by
    change (T : ℂ) ^ s * V T = (T : ℂ) ^ s * W T
    rw [hT]))

theorem artinMellin_congr_ae {V W : ℝ → ℂ}
    (hVW : V =ᵐ[artinPositiveMultiplicativeMeasure] W) (s : ℂ) :
    mellin V s = mellin W s := by
  rw [artinMellin_eq_multiplicative, artinMellin_eq_multiplicative]
  exact integral_congr_ae (hVW.mono (fun T hT => by
    change (T : ℂ) ^ s * V T = (T : ℂ) ^ s * W T
    rw [hT]))

theorem artinPositiveMultiplicative_integral_comp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a : ℝ} (ha : 0 < a) :
    (∫ T, f (a * T) ∂artinPositiveMultiplicativeMeasure) =
      ∫ T, f T ∂artinPositiveMultiplicativeMeasure := by
  rw [artinPositiveMultiplicative_integral_exp, artinPositiveMultiplicative_integral_exp]
  have he : (fun v : ℝ => f (a * Real.exp v)) =
      fun v => (fun w : ℝ => f (Real.exp w)) (Real.log a + v) := by
    funext v
    change f (a * Real.exp v) = f (Real.exp (Real.log a + v))
    rw [Real.exp_add, Real.exp_log ha]
  rw [he]
  exact integral_add_left_eq_self (fun w : ℝ => f (Real.exp w)) (Real.log a)

/-- Null-set differences remain null after positive radial scaling. The proof
uses the actual integral of the norm difference and the dt/t scaling identity. -/
theorem artinPositiveMultiplicative_ae_comp_mul {V W : ℝ → ℂ}
    (hVW : V =ᵐ[artinPositiveMultiplicativeMeasure] W) {a : ℝ} (ha : 0 < a) :
    (fun T => V (a * T)) =ᵐ[artinPositiveMultiplicativeMeasure] fun T => W (a * T) := by
  have hd : Integrable (fun T => V T - W T) artinPositiveMultiplicativeMeasure := by
    apply (integrable_congr (g := fun _ => (0 : ℂ))
      (hVW.mono (fun T hT => by simp [hT]))).mpr
    exact integrable_zero ℝ ℂ artinPositiveMultiplicativeMeasure
  have hda := (artinMultiplicative_integrable_comp_mul_iff
    (fun T => V T - W T) ha).mpr hd
  have hz : (∫ T, ‖V (a * T) - W (a * T)‖ ∂artinPositiveMultiplicativeMeasure) = 0 := by
    rw [artinPositiveMultiplicative_integral_comp_mul (fun T => ‖V T - W T‖) ha]
    apply integral_eq_zero_of_ae
    exact hVW.mono (fun T hT => by simp [hT])
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun T => norm_nonneg (V (a * T) - W (a * T)))) hda.norm).mp hz
  exact hae.mono (fun T hT => sub_eq_zero.mp (norm_eq_zero.mp hT))

theorem reflectionProfile_integral_congr_ae (C A : ℝ) (r : ℕ) {V W : ℝ → ℂ}
    (hVW : V =ᵐ[artinPositiveMultiplicativeMeasure] W) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel C A r T * V (u * T) ∂artinPositiveMultiplicativeMeasure) =
      ∫ T, reflectionKernel C A r T * W (u * T) ∂artinPositiveMultiplicativeMeasure :=
  integral_congr_ae ((artinPositiveMultiplicative_ae_comp_mul hVW hu).mono
    (fun T hT => by
      change V (u * T) = W (u * T) at hT
      change reflectionKernel C A r T * V (u * T) = reflectionKernel C A r T * W (u * T)
      rw [hT]))

/-- The smoothing needs only one absolute-convergence hypothesis, at zero,
and the Mellin formula on the imaginary axis. -/
theorem reflectionProfile_gaussian_of_mellin_zero {C A : ℝ} (hC : C ≠ 0)
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ} (hV : MellinConvergent V 0)
    (hM : ∀ y : ℝ, mellin V ((y : ℂ) * I) =
      (C : ℂ) * (A : ℂ) ^ ((y : ℂ) * I) *
        (Complex.Gamma ((y : ℂ) * I + 5 / 6) *
          Complex.Gamma ((y : ℂ) * I + 7 / 6)) ^ r)
    {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel C A r T * V (u * T) ∂artinPositiveMultiplicativeMeasure) =
      reflectionLogGaussian u :=
  reflectionProfile_actual_integral_eq_gaussian hC hA r
    (artinMellin_vertical_convergent hV) hM hu

/-- Only almost-everywhere identification of the actual Haar profile is needed
to transfer the every-point Gaussian smoothing of the constructed finite K profile. -/
theorem artinHaarProfile_gaussian_of_ae_finiteProfile {D c : ℝ} (hD : 0 < D)
    (hc : 0 < c) {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {V : ℝ → ℂ}
    (hV : V =ᵐ[artinPositiveMultiplicativeMeasure] artinBesselFiniteProfile D c ds)
    {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (D * artinBesselProductC c ds) (artinBesselProductA c ds)
      (ds.length + 1) T * V (u * T) ∂artinPositiveMultiplicativeMeasure) =
        reflectionLogGaussian u := by
  rw [reflectionProfile_integral_congr_ae _ _ _ hV hu]
  exact artinBesselFiniteProfile_gaussian_smoothing hD hc hds hu

end
end SimultaneousPrimitiveRoots

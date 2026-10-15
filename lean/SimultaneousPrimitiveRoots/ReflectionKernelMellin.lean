module

public import SimultaneousPrimitiveRoots.ReflectionKernelConstruction
public import SimultaneousPrimitiveRoots.MellinProbeFourier
public import SimultaneousPrimitiveRoots.ReflectionProfileFubini

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology FourierTransform
noncomputable section

/-- Every actual complex Mellin integral converges, by the already proved
absolute moments of the constructed kernel. -/
theorem reflectionKernel_mellin_convergent (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (z : ℂ) : MellinConvergent (reflectionKernel C A r) z := by
  rw [MellinConvergent, mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi
    ((reflectionKernel_continuousOn C hA r).aestronglyMeasurable measurableSet_Ioi)]
  exact (artinKernelMoment_integrable_iff _ z.re).mp
    (reflectionKernel_moment_integrable C hA r z.re)

theorem reflectionKernel_logPullback (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (σ u : ℝ) :
    probeLogPullback (reflectionKernel C A r) 0 σ u =
      𝓕 (fun y : ℝ => reflectionGammaQuotient C A r
        ((σ : ℂ) + (2 * Real.pi * y) * I)) u := by
  rw [probeLogPullback, sub_zero,
    reflectionKernel_eq_line C hA (Real.exp_pos (-u)) r σ,
    reflectionInverseMellinLine_fourier C A r σ (Real.exp_pos (-u)),
    Real.log_exp, Real.fourierInv_eq_fourier_neg, neg_neg, ← mul_assoc]
  have hp : (Real.exp (σ * u) : ℂ) * (Real.exp (-u) : ℂ) ^ (σ : ℂ) = 1 := by
    rw [← Complex.ofReal_cpow (Real.exp_pos (-u)).le, ← Complex.ofReal_mul,
      ← Real.exp_mul, ← Real.exp_add, show σ * u + -u * σ = 0 by ring,
      Real.exp_zero, Complex.ofReal_one]
  rw [hp, one_mul]

theorem reflectionKernel_logPullback_integrable (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (σ : ℝ) : Integrable (probeLogPullback (reflectionKernel C A r) 0 σ) := by
  change Integrable (fun u : ℝ => (Real.exp ((σ - 0) * u) : ℂ) *
    reflectionKernel C A r (Real.exp (-u)))
  simpa only [sub_zero, neg_neg] using
    mellinConvergent_integrable_logPullback
      (reflectionKernel_mellin_convergent C hA r ((-σ : ℝ) : ℂ))

/-- Fourier inversion identifies the actual convergent Mellin transform;
integrability of the Fourier transform is derived from the kernel bounds. -/
theorem reflectionKernel_mellin_vertical (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (σ τ : ℝ) :
    mellin (reflectionKernel C A r) (-((σ : ℂ) + τ * I)) =
      reflectionGammaQuotient C A r ((σ : ℂ) + τ * I) := by
  let g : ℝ → ℂ := fun y => reflectionGammaQuotient C A r ((σ : ℂ) + (2 * Real.pi * y) * I)
  have hg : Integrable g := reflectionGammaQuotient_fourierLine_integrable C hA r σ
  have hc : Continuous g := (reflectionGammaQuotient_entire C hA r).continuous.comp
    (by fun_prop)
  have heq : probeLogPullback (reflectionKernel C A r) 0 σ = 𝓕 g :=
    funext (reflectionKernel_logPullback C hA r σ)
  have hFg : Integrable (𝓕 g) := by
    rw [← heq]
    exact reflectionKernel_logPullback_integrable C hA r σ
  have hid := probeMellinTransform_vertical_eq_fourierInv (reflectionKernel C A r) 0 σ τ
  simp only [probeMellinTransform, Complex.ofReal_zero, zero_sub] at hid
  rw [hid, heq, hg.fourierInv_fourier_eq hFg hc.continuousAt]
  dsimp [g]
  congr 1
  push_cast
  field_simp

theorem reflectionKernel_mellin_neg (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (z : ℂ) :
    mellin (reflectionKernel C A r) (-z) = reflectionGammaQuotient C A r z := by
  simpa only [Complex.re_add_im] using reflectionKernel_mellin_vertical C hA r z.re z.im

/-- The kernel endpoint and moment assumptions are now discharged for the
constructed kernel. Actual theta coefficients and profile bounds remain inputs. -/
theorem reflectionKernel_profile_Fubini (K : Type*) [Field K] [NumberField K]
    (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (C₀ : ℝ) {A₀ : ℝ} (hA₀ : 0 < A₀) (r : ℕ)
    (a : ReflectionIdealIndices K s → ℂ) (ψ : ReflectionIdealIndices K s → ℝ → ℂ)
    (hψc : ∀ x, ContinuousOn (ψ x) (Ioi 0)) {σ C t : ℝ}
    (hσ : 1 / 2 < σ) (hC : 0 ≤ C) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x)
    (hψ : ∀ x u, 0 < u → ‖ψ x u‖ ≤ C * u ^ (-σ)) :
    ((∑' x, ∫ T, reflectionProfileTerm K s (reflectionKernel C₀ A₀ r) a ψ t x T
        ∂artinPositiveMultiplicativeMeasure) =
      ∫ T, (∑' x, reflectionProfileTerm K s (reflectionKernel C₀ A₀ r) a ψ t x T)
        ∂artinPositiveMultiplicativeMeasure) ∧
    (∫ T, (∑' x, ‖reflectionProfileTerm K s (reflectionKernel C₀ A₀ r) a ψ t x T‖)
        ∂artinPositiveMultiplicativeMeasure) ≤
      C * t ^ σ * artinKernelMoment (reflectionKernel C₀ A₀ r) σ *
        ∑' x, admissibleFrozenTripleTerm K s σ x := by
  have hκ := reflectionKernel_decay C₀ hA₀ r
  exact ⟨reflectionProfile_integral_tsum K s hκ a ψ hψc hσ ht ha hψ,
    reflectionProfile_absolute_integral_le K s hκ a ψ hψc hσ hC ht ha hψ⟩

end
end SimultaneousPrimitiveRoots

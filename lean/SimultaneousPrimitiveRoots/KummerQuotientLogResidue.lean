module

public import SimultaneousPrimitiveRoots.AnalyticLogDerivativeResidue
public import SimultaneousPrimitiveRoots.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.KummerGaussianMellin

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter Metric MeasureTheory
open scoped Topology
noncomputable section
open Classical

/-- The signed logarithmic derivative of the actual entire full quotient.
The function H remains an explicit input until its existence is proved. -/
def fullQuotientSignedLogDerivative (H : ℂ → ℂ) (d : ℂ) (s : ℂ) : ℂ :=
  -logDeriv H s / d

theorem numberFieldEntireFullQuotientContinuation_boundary_matches (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {s : ℂ} (hs : 1 ≤ s.re) :
    H s = numberFieldIncompleteZetaQuotient K L ∅ ∅ s := by
  have hadd : ContinuousAt (fun t : ℝ => s + (t : ℂ)) (0 : ℝ) := by fun_prop
  have h1 : ContinuousAt (fun t : ℝ => H (s + (t : ℂ))) 0 := by
    have hc : ContinuousAt H (s + ((0 : ℝ) : ℂ)) := by
      simpa using (hH.1 s (Set.mem_univ s)).continuousAt
    exact hc.comp (f := fun t : ℝ => s + (t : ℂ)) (x := (0 : ℝ)) hadd
  have h2 : ContinuousAt
      (fun t : ℝ => numberFieldIncompleteZetaQuotient K L ∅ ∅ (s + (t : ℂ))) 0 := by
    have hc : ContinuousAt (numberFieldIncompleteZetaQuotient K L ∅ ∅)
        (s + ((0 : ℝ) : ℂ)) := by
      simpa using (numberFieldIncompleteZetaQuotient_differentiableAt K L ∅ ∅ hs).continuousAt
    exact hc.comp (f := fun t : ℝ => s + (t : ℂ)) (x := (0 : ℝ)) hadd
  have heq : (fun t : ℝ => H (s + (t : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => numberFieldIncompleteZetaQuotient K L ∅ ∅ (s + (t : ℂ))) := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hz : 1 < (s + (t : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    rw [hH.2 _ hz]
    simp [numberFieldIncompleteZetaQuotient, numberFieldIncompleteZetaNormalized,
      numberFieldDeletedZetaCorrection]
  have ht1 : Tendsto (fun t : ℝ => H (s + (t : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (H s)) := by
    simpa using h1.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have ht2 : Tendsto
      (fun t : ℝ => numberFieldIncompleteZetaQuotient K L ∅ ∅ (s + (t : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (numberFieldIncompleteZetaQuotient K L ∅ ∅ s)) := by
    simpa using h2.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  exact tendsto_nhds_unique_of_eventuallyEq ht1 ht2 heq

theorem numberFieldEntireFullQuotientContinuation_boundary_ne_zero (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {s : ℂ} (hs : 1 ≤ s.re) : H s ≠ 0 := by
  rw [numberFieldEntireFullQuotientContinuation_boundary_matches K L hH hs]
  exact numberFieldIncompleteZetaQuotient_ne_zero K L ∅ ∅ hs

theorem numberFieldEntireFullQuotientContinuation_logDeriv_eq_full (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv H s = logDeriv (dedekindZeta K) s - logDeriv (dedekindZeta L) s := by
  have heq : H =ᶠ[𝓝 s] numberFieldIncompleteZetaQuotient K L ∅ ∅ :=
    eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      (fun z hz => numberFieldEntireFullQuotientContinuation_boundary_matches K L hH hz.le)
  rw [(logDeriv_congr_nhds heq).eq_of_nhds,
    numberFieldIncompleteZetaQuotient_logDeriv_eq K L ∅ ∅ hs,
    numberFieldIncompleteZeta_logDeriv_eq K ∅ hs,
    numberFieldIncompleteZeta_logDeriv_eq L ∅ hs]
  simp [numberFieldDeletedLogCorrection]

theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_meromorphic
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (d : ℂ) :
    Meromorphic (fullQuotientSignedLogDerivative H d) := by
  intro s
  exact (((hH.1 s (Set.mem_univ _)).meromorphicAt.deriv.div
    (hH.1 s (Set.mem_univ _)).meromorphicAt).neg.div (MeromorphicAt.const d s))

/-- The analytic remainder and the coefficient -m/d are derived from H,
not assumed as an explicit-formula input. -/
theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_principal_part
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (d s : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      fullQuotientSignedLogDerivative H d =ᶠ[𝓝[≠] s] fun z =>
        (-(fullQuotientZeroMultiplicity H s : ℂ) / d) / (z - s) + g z := by
  obtain ⟨g, hg, heq⟩ := analyticAt_logDeriv_principal_part
    (hH.1 s (Set.mem_univ _))
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)
  refine ⟨fun z => -g z / d, hg.neg.div_const, ?_⟩
  filter_upwards [heq] with z hz
  unfold fullQuotientSignedLogDerivative
  rw [hz]
  change -((fullQuotientZeroMultiplicity H s : ℂ) / (z - s) + g z) / d = _
  ring

theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_residue
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (d s : ℂ) :
    Tendsto (fun z => (z - s) * fullQuotientSignedLogDerivative H d z)
      (𝓝[≠] s) (𝓝 (-(fullQuotientZeroMultiplicity H s : ℂ) / d)) := by
  have ht := (analyticAt_tendsto_mul_logDeriv (hH.1 s (Set.mem_univ _))
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)).neg.div_const d
  convert ht using 1
  · funext z
    unfold fullQuotientSignedLogDerivative
    ring
  · simp only [fullQuotientZeroMultiplicity, analyticOrderNatAt]

def gaussianQuotientContourKernel (x : ℝ) (s : ℂ) : ℂ :=
  ((1 / x : ℝ) : ℂ) ^ (-s) * artinGaussianMellin s

theorem gaussianQuotientContourKernel_eq {x : ℝ} (hx : 0 < x) (s : ℂ) :
    gaussianQuotientContourKernel x s = (x : ℂ) ^ s * artinGaussianMellin s := by
  unfold gaussianQuotientContourKernel
  push_cast
  rw [one_div, Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv]

/-- The local residue coefficient of the actual Gaussian Mellin integrand.
It is -m/d times x^rho*w_hat(rho), with the actual natural multiplicity. -/
theorem numberFieldEntireFullQuotientContinuation_gaussian_residue
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {x : ℝ} (hx : 0 < x) (d s : ℂ) :
    Tendsto (fun z => (z - s) * (gaussianQuotientContourKernel x z *
      fullQuotientSignedLogDerivative H d z)) (𝓝[≠] s)
      (𝓝 ((-(fullQuotientZeroMultiplicity H s : ℂ) / d) *
        ((x : ℂ) ^ s * artinGaussianMellin s))) := by
  have hn : ((1 / x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_div_ne_zero hx.ne')
  have hm : Differentiable ℂ artinGaussianMellin := by
    unfold artinGaussianMellin
    fun_prop
  have hc : ContinuousAt (gaussianQuotientContourKernel x) s :=
    (((differentiable_id.neg.const_cpow (Or.inl hn)).mul hm) s).continuousAt
  have ht := (numberFieldEntireFullQuotientContinuation_signedLogDerivative_residue
    K L hH d s).mul (hc.tendsto.mono_left
      (show 𝓝[≠] s ≤ 𝓝 s from nhdsWithin_le_nhds))
  rw [gaussianQuotientContourKernel_eq hx s] at ht
  convert ht using 1
  funext z
  ring

private theorem kummerFullQuotientGaussian_integrand_eq {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {σ : ℝ} (hσ : 1 < σ) (x y : ℝ) :
    gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I) =
    (gaussianDirichletVerticalKernel x σ y *
        (-logDeriv (numberFieldIncompleteZeta (PrimeKummerField a q) ∅)
          ((σ : ℂ) + y * Complex.I)) -
      gaussianDirichletVerticalKernel x σ y *
        (-logDeriv (numberFieldIncompleteZeta (CyclotomicField q ℚ) ∅)
          ((σ : ℂ) + y * Complex.I))) / ((q : ℂ) - 1) := by
  have hs : 1 < ((σ : ℂ) + y * Complex.I).re := by simpa using hσ
  rw [fullQuotientSignedLogDerivative,
    numberFieldEntireFullQuotientContinuation_logDeriv_eq_full _ _ hH hs,
    numberFieldIncompleteZeta_logDeriv_eq _ ∅ hs,
    numberFieldIncompleteZeta_logDeriv_eq _ ∅ hs]
  simp only [numberFieldDeletedLogCorrection, Finset.sum_empty, add_zero]
  ring

/-- The actual entire quotient yields the full signed-trace integral on
Re(s)>1. Global contour shifting is not asserted by this identity. -/
theorem kummerFullQuotientSignedLogDerivative_integrable {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I)) := by
  simp_rw [kummerFullQuotientGaussian_integrand_eq hH hσ]
  exact ((gaussianDeletedZetaLogDerivative_integrable (PrimeKummerField a q) ∅ hx hσ).sub
    (gaussianDeletedZetaLogDerivative_integrable (CyclotomicField q ℚ) ∅ hx hσ)).div_const _

theorem kummerFullQuotientSignedLogDerivative_integral {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I)) =
        ((2 * Real.pi * primeKummerGaussianFullSignedTrace a q x : ℝ) : ℂ) := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  simp_rw [kummerFullQuotientGaussian_integrand_eq hH hσ]
  rw [integral_div, integral_sub
    (gaussianDeletedZetaLogDerivative_integrable (PrimeKummerField a q) ∅ hx hσ)
    (gaussianDeletedZetaLogDerivative_integrable (CyclotomicField q ℚ) ∅ hx hσ),
    gaussianDeletedZetaLogDerivative_integral _ ∅ hx hσ,
    gaussianDeletedZetaLogDerivative_integral _ ∅ hx hσ,
    gaussianDeletedPrimeIdealTrace_empty _ hx, gaussianDeletedPrimeIdealTrace_empty _ hx,
    primeKummerGaussianFullSignedTrace]
  push_cast
  ring

theorem kummerFullQuotientSignedLogDerivative_mellinInv {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    mellinInv σ (fun s => artinGaussianMellin s *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) s) (1 / x) =
        (primeKummerGaussianFullSignedTrace a q x : ℂ) := by
  rw [mellinInv]
  simp only [smul_eq_mul, Complex.real_smul]
  simp_rw [← mul_assoc]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I)) = _
  rw [kummerFullQuotientSignedLogDerivative_integral hH hx hσ]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end
end SimultaneousPrimitiveRoots

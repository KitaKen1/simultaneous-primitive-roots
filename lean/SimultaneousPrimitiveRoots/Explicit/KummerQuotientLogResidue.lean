module

public import SimultaneousPrimitiveRoots.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting

/-! Generalization of `SimultaneousPrimitiveRoots.KummerQuotientLogResidue` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField IsDedekindDomain Filter Metric MeasureTheory
open scoped Topology
noncomputable section
open Classical

theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_meromorphic
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (d : ℂ) :
    Meromorphic (fullQuotientSignedLogDerivative H d) := by
  intro s
  exact (((hH.1 s (Set.mem_univ _)).meromorphicAt.deriv.div
    (hH.1 s (Set.mem_univ _)).meromorphicAt).neg.div (MeromorphicAt.const d s))

/-- The analytic remainder and the coefficient -m/d are derived from H,
not assumed as an explicit-formula input. -/
theorem numberFieldEntireFullQuotientContinuation_signedLogDerivative_principal_part
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (d s : ℂ) :
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
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (d s : ℂ) :
    Tendsto (fun z => (z - s) * fullQuotientSignedLogDerivative H d z)
      (𝓝[≠] s) (𝓝 (-(fullQuotientZeroMultiplicity H s : ℂ) / d)) := by
  have ht := (analyticAt_tendsto_mul_logDeriv (hH.1 s (Set.mem_univ _))
    (numberFieldEntireFullQuotientContinuation_analyticOrderAt_ne_top K L hH s)).neg.div_const d
  convert ht using 1
  · funext z
    unfold fullQuotientSignedLogDerivative
    ring
  · simp only [fullQuotientZeroMultiplicity, analyticOrderNatAt]

/-- The local residue coefficient of the actual Gaussian Mellin integrand.
It is -m/d times x^rho*w_hat(rho), with the actual natural multiplicity. -/
theorem numberFieldEntireFullQuotientContinuation_gaussian_residue
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
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
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {σ : ℝ} (hσ : 1 < σ) (x y : ℝ) :
    gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I) =
    (gaussianDirichletVerticalKernel x σ y *
        (-logDeriv (numberFieldIncompleteZeta (PrimeKummerField a q) ∅)
          ((σ : ℂ) + y * Complex.I)) -
      gaussianDirichletVerticalKernel x σ y / (((σ : ℂ) + y * Complex.I) - 1)) /
        ((q : ℂ) - 1) := by
  have hs : 1 < ((σ : ℂ) + y * Complex.I).re := by simpa using hσ
  rw [fullQuotientSignedLogDerivative, entireZeroData_logDeriv_eq hH hs]
  ring

/-- On `Re s > 1` the signed logarithmic derivative of `F_K` against the Gaussian kernel is
integrable (Dirichlet series of `ζ_K` plus the pole term). -/
theorem kummerFullQuotientSignedLogDerivative_integrable {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ => gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I)) := by
  simp_rw [kummerFullQuotientGaussian_integrand_eq hH hσ]
  exact ((gaussianDeletedZetaLogDerivative_integrable (PrimeKummerField a q) ∅ hx hσ).sub
    (Hecke.integrable_gaussianKernel_div_sub_one hx hσ)).div_const _

/-- **The Dirichlet side for `F_K`:** on `Re s = σ > 1` the Gaussian integral of the signed
logarithmic derivative is `2π (Θ_K(x) - M(x))/(q - 1)`. -/
theorem kummerFullQuotientSignedLogDerivative_integral {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    (∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      fullQuotientSignedLogDerivative H ((q : ℂ) - 1) ((σ : ℂ) + y * Complex.I)) =
        ((2 * Real.pi * primeKummerGaussianFullSignedTrace a q x : ℝ) : ℂ) := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  simp_rw [kummerFullQuotientGaussian_integrand_eq hH hσ]
  rw [integral_div, integral_sub
    (gaussianDeletedZetaLogDerivative_integrable (PrimeKummerField a q) ∅ hx hσ)
    (Hecke.integrable_gaussianKernel_div_sub_one hx hσ),
    gaussianDeletedZetaLogDerivative_integral _ ∅ hx hσ,
    gaussianDeletedPrimeIdealTrace_empty _ hx, Hecke.integral_gaussianKernel_div_sub_one hx hσ,
    primeKummerGaussianFullSignedTrace]
  push_cast
  ring

theorem kummerFullQuotientSignedLogDerivative_mellinInv {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
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
end SimultaneousPrimitiveRoots.Explicit

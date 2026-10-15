module

public import SimultaneousPrimitiveRoots.GaussianDirichletMellin
public import SimultaneousPrimitiveRoots.Hecke.EntireBasics
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The pole of `ζ_K` against the Gaussian kernel (step D6, Dirichlet side)

For `F_K(s) = (s - 1) ζ_K(s)` the logarithmic derivative on `Re s > 1` is
`-F_K'/F_K = -ζ_K'/ζ_K - 1/(s - 1)`. Integrated against the project's Gaussian kernel
`x^s ŵ(s)` on a vertical line `Re s = σ > 1`:

* `integral_gaussianKernel_div_sub_one`: `∫ x^s ŵ(s)/(s - 1) dy = 2π ∫_{t > 1} w(t/x) dt`
  (write `1/(s - 1) = ∫_{t > 1} t^{-s} dt`, swap the integrals, Mellin inversion);
* `gaussianMainTerm_le`: `∫_{t > 1} w(t/x) dt ≤ x ŵ(1)` with `ŵ(1) = √π e^{(log 2)² + 1/4}`;
* `logDeriv_dedekindZetaEntire`: `F_K'/F_K = 1/(s - 1) + Z'/Z` with `Z` the project's
  `numberFieldIncompleteZeta K ∅` (`= ζ_K` on `Re s > 1`);
* `integral_gaussianKernel_neg_logDeriv_dedekindZetaEntire`: for Galois `K`,
  `∫ x^s ŵ(s) (-F_K'/F_K)(s) dy = 2π (Θ_K(x) - ∫_{t > 1} w(t/x) dt)`,
  where `Θ_K = gaussianPrimePowerTrace K`.

This is the replacement, for the single entire function `F_K`, of the quotient identity
`kummerFullQuotientSignedLogDerivative_integral`; the subtracted term is the main term `≍ x`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Complex NumberField Filter
open scoped Real Topology

/-- `∫_{t > 1} t^{-s} dt = 1/(s - 1)` for `Re s > 1`. -/
theorem integral_Ioi_one_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
  have ha : (-s).re < -1 := by simp; linarith
  rw [integral_Ioi_cpow_of_lt ha one_pos, Complex.ofReal_one, Complex.one_cpow]
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1 : -s + 1 ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  field_simp
  ring

/-- The Gaussian kernel times `t^{-s}` is the kernel rescaled by `t`. -/
theorem gaussianKernel_mul_cpow {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (σ y : ℝ) :
    gaussianDirichletVerticalKernel x σ y * (t : ℂ) ^ (-((σ : ℂ) + y * I)) =
      ((t / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) * artinGaussianMellin ((σ : ℂ) + y * I) := by
  unfold gaussianDirichletVerticalKernel
  have h := Complex.mul_cpow_ofReal_nonneg (one_div_pos.mpr hx).le ht.le (-((σ : ℂ) + y * I))
  have hxt : (((1 / x : ℝ) : ℂ) * (t : ℂ)) = ((t / x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hxt] at h
  rw [h]
  ring

/-- **The pole term against the Gaussian kernel.** For `x > 0` and `σ > 1`,
`∫ x^s ŵ(s)/(s - 1) dy = 2π ∫_{t > 1} w(t/x) dt` on `Re s = σ`. -/
theorem integral_gaussianKernel_div_sub_one {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    ∫ y : ℝ, gaussianDirichletVerticalKernel x σ y / (((σ : ℂ) + y * I) - 1) =
      ((2 * π * ∫ t in Ioi (1 : ℝ), artinGaussianWeight (t / x) : ℝ) : ℂ) := by
  have hsre : ∀ y : ℝ, 1 < ((σ : ℂ) + y * I).re := fun y => by simp; linarith
  set f : ℝ → ℝ → ℂ := fun y t =>
    gaussianDirichletVerticalKernel x σ y * (t : ℂ) ^ (-((σ : ℂ) + y * I)) with hf
  have h1 : ∀ y : ℝ, gaussianDirichletVerticalKernel x σ y / (((σ : ℂ) + y * I) - 1) =
      ∫ t in Ioi (1 : ℝ), f y t := by
    intro y
    simp only [hf]
    rw [integral_const_mul, integral_Ioi_one_cpow_neg (hsre y), div_eq_mul_one_div]
  simp_rw [h1]
  -- integrability on the product
  have hkint := (gaussianDirichletVerticalKernel_integrable hx σ).norm
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hprod : Integrable (fun p : ℝ × ℝ => ‖gaussianDirichletVerticalKernel x σ p.1‖ * p.2 ^ (-σ))
      (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := hkint.mul_prod hpow
  have hkcont : Continuous (gaussianDirichletVerticalKernel x σ) := by
    unfold gaussianDirichletVerticalKernel artinGaussianMellin
    have hb : (((1 / x : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (one_div_pos.mpr hx).ne'
    refine Continuous.mul ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl hb)
    · fun_prop
  have hmeas : Measurable (Function.uncurry f) := by
    simp only [hf, Function.uncurry_def]
    refine (hkcont.measurable.comp measurable_fst).mul ?_
    refine (Complex.measurable_ofReal.comp measurable_snd).pow ?_
    exact ((measurable_const.add ((Complex.measurable_ofReal.comp measurable_fst).mul
      measurable_const))).neg
  have hint : Integrable (Function.uncurry f) (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    refine hprod.mono' hmeas.aestronglyMeasurable ?_
    have hrestr : (volume : Measure ℝ).prod (volume.restrict (Ioi (1 : ℝ))) =
        ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi (1 : ℝ)) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hrestr, ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioi)]
    refine Eventually.of_forall fun p hp => ?_
    have hp2 : (0 : ℝ) < p.2 := lt_trans one_pos (Set.mem_prod.mp hp).2
    simp only [hf, Function.uncurry_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp2]
    simp
  rw [integral_integral_swap hint]
  have h3 : ∀ t ∈ Ioi (1 : ℝ), ∫ y : ℝ, f y t = ((2 * π * artinGaussianWeight (t / x) : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    simp only [hf]
    simp_rw [gaussianKernel_mul_cpow hx ht0]
    exact artinGaussianMellin_inverse_integral σ (div_pos ht0 hx)
  rw [setIntegral_congr_fun measurableSet_Ioi h3, integral_complex_ofReal, integral_const_mul]

/-- `ŵ(1) = √π e^{(log 2)² + 1/4}`, the total mass of the Gaussian weight. -/
def gaussianMainConstant : ℝ := Real.sqrt π * Real.exp ((Real.log 2) ^ 2 + 1 / 4)

theorem gaussianMainConstant_pos : 0 < gaussianMainConstant :=
  mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)

theorem integrableOn_artinGaussianWeight : IntegrableOn artinGaussianWeight (Ioi (0 : ℝ)) := by
  have h := (artinGaussianWeight_hasMellin 1).1
  have h' : IntegrableOn (fun t : ℝ => ((artinGaussianWeight t : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp
  exact h'.re

/-- `∫_0^∞ w = ŵ(1)`. -/
theorem integral_artinGaussianWeight_Ioi_zero :
    ∫ t in Ioi (0 : ℝ), artinGaussianWeight t = gaussianMainConstant := by
  have h := (artinGaussianWeight_hasMellin 1).2
  rw [mellin] at h
  simp only [sub_self, Complex.cpow_zero, one_smul] at h
  rw [integral_complex_ofReal] at h
  have hw : artinGaussianMellin 1 = ((gaussianMainConstant : ℝ) : ℂ) := by
    unfold artinGaussianMellin gaussianMainConstant
    push_cast
    ring_nf
  rw [hw] at h
  exact_mod_cast h

/-- **The main term:** `∫_{t > 1} w(t/x) dt ≤ x ŵ(1)`. -/
theorem gaussianMainTerm_le {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (1 : ℝ), artinGaussianWeight (t / x) ≤ x * gaussianMainConstant := by
  have hfun : (fun t : ℝ => artinGaussianWeight (t / x)) =
      fun t => artinGaussianWeight (x⁻¹ * t) := by
    ext t
    rw [div_eq_inv_mul]
  have hsub : ∫ t in Ioi (0 : ℝ), artinGaussianWeight (t / x) = x * gaussianMainConstant := by
    rw [hfun, integral_comp_mul_left_Ioi (fun u => artinGaussianWeight u) 0 (inv_pos.mpr hx),
      mul_zero, inv_inv, smul_eq_mul, integral_artinGaussianWeight_Ioi_zero]
  have hint : IntegrableOn (fun t : ℝ => artinGaussianWeight (t / x)) (Ioi (0 : ℝ)) := by
    rw [hfun]
    refine (integrableOn_Ioi_comp_mul_left_iff (fun u => artinGaussianWeight u) 0
      (inv_pos.mpr hx)).mpr ?_
    rw [mul_zero]
    exact integrableOn_artinGaussianWeight
  rw [← hsub]
  exact setIntegral_mono_set hint
    (Eventually.of_forall fun _ => (artinGaussianWeight_pos _).le)
    (Ioi_subset_Ioi zero_le_one).eventuallyLE

theorem gaussianMainTerm_nonneg (x : ℝ) :
    0 ≤ ∫ t in Ioi (1 : ℝ), artinGaussianWeight (t / x) :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (artinGaussianWeight_pos _).le

variable (K : Type*) [Field K] [NumberField K]

/-- **The logarithmic derivative of `F_K`** on `Re s > 1`:
`F_K'/F_K = 1/(s - 1) + Z'/Z` with `Z = numberFieldIncompleteZeta K ∅`. -/
theorem logDeriv_dedekindZetaEntire {s : ℂ} (hs : 1 < s.re) :
    logDeriv (dedekindZetaEntire K) s =
      1 / (s - 1) + logDeriv (numberFieldIncompleteZeta K ∅) s := by
  set Z := numberFieldIncompleteZeta K ∅
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnhds : {z : ℂ | 1 < z.re} ∈ 𝓝 s := hopen.mem_nhds hs
  -- `Z = F/(z - 1)` near `s`
  have hZeq : ∀ z : ℂ, 1 < z.re → Z z = dedekindZetaEntire K z / (z - 1) := by
    intro z hz
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    change numberFieldIncompleteZeta K ∅ z = _
    rw [dedekindZetaEntire_eq_mul K hz, numberFieldIncompleteZeta_eq K ∅ hz,
      Finset.prod_empty, mul_one]
    field_simp
  have hZd : DifferentiableAt ℂ Z s := by
    have hq : DifferentiableAt ℂ (fun z => dedekindZetaEntire K z / (z - 1)) s :=
      ((differentiable_dedekindZetaEntire K) s).div (differentiableAt_id.sub_const 1) hs1
    exact hq.congr_of_eventuallyEq (Filter.mem_of_superset hnhds fun z hz => hZeq z hz)
  have hZ0 : Z s ≠ 0 := numberFieldIncompleteZeta_ne_zero K ∅ hs
  -- `F = (z - 1) Z` near `s`
  have hFeq : dedekindZetaEntire K =ᶠ[𝓝 s] fun z => (z - 1) * Z z := by
    filter_upwards [hnhds] with z hz
    rw [hZeq z hz]
    have hz1 : z - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have : (1 : ℝ) < z.re := hz
      linarith
    field_simp
  rw [logDeriv_apply, logDeriv_apply, hFeq.deriv_eq, hFeq.eq_of_nhds]
  have hd : HasDerivAt (fun z => (z - 1) * Z z) (1 * Z s + (s - 1) * deriv Z s) s :=
    ((hasDerivAt_id s).sub_const 1).mul hZd.hasDerivAt
  rw [hd.deriv]
  field_simp

/-- The pole term `x^s ŵ(s)/(s - 1)` is integrable on `Re s = σ > 1`. -/
theorem integrable_gaussianKernel_div_sub_one {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Integrable (fun y : ℝ =>
      gaussianDirichletVerticalKernel x σ y / (((σ : ℂ) + y * I) - 1)) := by
  have hk := gaussianDirichletVerticalKernel_integrable hx σ
  have hc : Continuous fun y : ℝ => 1 / (((σ : ℂ) + y * I) - 1) := by
    refine Continuous.div continuous_const (by fun_prop) fun y => ?_
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  simp_rw [div_eq_mul_one_div (gaussianDirichletVerticalKernel x σ _)]
  refine hk.mul_bdd hc.aestronglyMeasurable (c := 1 / (σ - 1)) (Eventually.of_forall fun y => ?_)
  rw [norm_div, norm_one]
  have hre : σ - 1 ≤ ‖((σ : ℂ) + y * I) - 1‖ := by
    have := Complex.abs_re_le_norm (((σ : ℂ) + y * I) - 1)
    have hr : (((σ : ℂ) + y * I) - 1).re = σ - 1 := by simp
    rw [hr, abs_of_pos (by linarith)] at this
    exact this
  exact one_div_le_one_div_of_le (by linarith) hre

/-- **The Dirichlet side of the explicit formula for `F_K`.** For Galois `K`, `x > 0` and
`σ > 1`, on the line `Re s = σ`:
`∫ x^s ŵ(s) (-F_K'/F_K)(s) dy = 2π (Θ_K(x) - ∫_{t > 1} w(t/x) dt)`. -/
theorem integral_gaussianKernel_neg_logDeriv_dedekindZetaEntire [IsGalois ℚ K] {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 < σ) :
    ∫ y : ℝ, gaussianDirichletVerticalKernel x σ y *
        (-logDeriv (dedekindZetaEntire K) ((σ : ℂ) + y * I)) =
      ((2 * π * (gaussianPrimePowerTrace K x -
        ∫ t in Ioi (1 : ℝ), artinGaussianWeight (t / x)) : ℝ) : ℂ) := by
  have hsre : ∀ y : ℝ, 1 < ((σ : ℂ) + y * I).re := fun y => by simp; linarith
  have hsplit : ∀ y : ℝ, gaussianDirichletVerticalKernel x σ y *
      (-logDeriv (dedekindZetaEntire K) ((σ : ℂ) + y * I)) =
      gaussianDirichletVerticalKernel x σ y *
        (-logDeriv (numberFieldIncompleteZeta K ∅) ((σ : ℂ) + y * I)) -
      gaussianDirichletVerticalKernel x σ y / (((σ : ℂ) + y * I) - 1) := by
    intro y
    rw [logDeriv_dedekindZetaEntire K (hsre y)]
    ring
  simp_rw [hsplit]
  have hA := gaussianDeletedZetaLogDerivative_integrable K ∅ hx hσ
  have hB := integrable_gaussianKernel_div_sub_one hx hσ
  rw [integral_sub hA hB, gaussianDeletedZetaLogDerivative_integral K ∅ hx hσ,
    gaussianDeletedPrimeIdealTrace_empty K hx, integral_gaussianKernel_div_sub_one hx hσ]
  push_cast
  ring

end SimultaneousPrimitiveRoots.Hecke

end

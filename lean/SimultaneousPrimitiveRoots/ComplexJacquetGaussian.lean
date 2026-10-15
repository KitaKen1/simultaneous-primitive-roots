module

public import SimultaneousPrimitiveRoots.SphericalBesselProfiles
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

/-- A genuine Fourier Gaussian on the complex plane with its ordinary area measure. -/
def artinComplexGaussianFourier (t c : ℝ) (x : ℂ) : ℂ :=
  Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2 - Complex.I * c * x.re)

theorem artinComplexGaussianFourier_product (t c : ℝ) (x : ℂ) :
    artinComplexGaussianFourier t c x =
      (Real.exp (-t * ‖x‖ ^ 2) : ℂ) * Complex.exp (-Complex.I * c * x.re) := by
  unfold artinComplexGaussianFourier
  rw [sub_eq_add_neg, Complex.exp_add]
  congr 1
  · push_cast
    rfl
  · congr 1
    ring

theorem artinComplexGaussianFourier_norm (t c : ℝ) (x : ℂ) :
    ‖artinComplexGaussianFourier t c x‖ = Real.exp (-t * ‖x‖ ^ 2) := by
  rw [artinComplexGaussianFourier, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

theorem artinComplexGaussianFourier_integrable {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (artinComplexGaussianFourier t c) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht) (-Complex.I * c) (1 : ℂ)
  change Integrable (fun x : ℂ =>
    Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2 - Complex.I * c * x.re))
  convert h using 1
  funext x
  simp [Complex.inner, sub_eq_add_neg, neg_mul, mul_assoc]

theorem artinComplexGaussianFourier_integral {t : ℝ} (ht : 0 < t) (c : ℝ) :
    (∫ x : ℂ, artinComplexGaussianFourier t c x) =
      ((Real.pi / t * Real.exp (-c ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t : ℂ)) (by simpa using ht) (-Complex.I * c) (1 : ℂ)
  have hs : (-Complex.I * (c : ℂ)) ^ 2 = -(c : ℂ) ^ 2 := by
    rw [mul_pow, neg_sq, Complex.I_sq]
    ring
  simp only [Complex.inner, map_one, mul_one, norm_one, hs] at h
  norm_num at h
  convert h using 1
  · congr 1
    funext x
    simp [artinComplexGaussianFourier, sub_eq_add_neg, neg_mul, mul_assoc]
  · push_cast
    rfl

theorem artinPositiveLaplace_integrable {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  simpa only [Real.rpow_one, neg_mul] using
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := a - 1) (b := r) (by linarith) (by norm_num) hr

theorem artinPositiveLaplace_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (a - 1) * Real.exp (-(r * t))) =
      r ^ (-a) * Real.Gamma a := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr, one_div,
    Real.inv_rpow hr.le, Real.rpow_neg hr.le]

theorem artinPositiveLaplace_normalized {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (Real.Gamma a)⁻¹ * (∫ t : ℝ in Ioi 0,
      t ^ (a - 1) * Real.exp (-(r * t))) = r ^ (-a) := by
  rw [artinPositiveLaplace_integral ha hr]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos ha)]

/-- The rational spherical section in the proposed Jacquet calculation. -/
def artinComplexJacquetSection (rho : ℝ) (x : ℂ) : ℝ :=
  (rho ^ 2 + ‖x‖ ^ 2) ^ (-(4 / 3 : ℝ))

def artinComplexJacquetIntegrand (rho c : ℝ) (x : ℂ) : ℂ :=
  (artinComplexJacquetSection rho x : ℂ) * Complex.exp (-Complex.I * c * x.re)

/-- This is the actual area integral, not a definition by its expected K value. -/
def artinComplexJacquetIntegral (rho c : ℝ) : ℂ :=
  ((rho ^ (4 / 3 : ℝ) : ℝ) : ℂ) * ∫ x : ℂ, artinComplexJacquetIntegrand rho c x

def artinComplexJacquetLaplaceKernel (rho c : ℝ) (t : ℝ) (x : ℂ) : ℂ :=
  ((t ^ (1 / 3 : ℝ) * Real.exp (-(rho ^ 2 * t)) : ℝ) : ℂ) *
    artinComplexGaussianFourier t c x

theorem artinComplexJacquetSection_pos {rho : ℝ} (hrho : 0 < rho) (x : ℂ) :
    0 < artinComplexJacquetSection rho x := by
  apply Real.rpow_pos_of_pos
  positivity

theorem artinComplexJacquetSection_laplace {rho : ℝ} (hrho : 0 < rho) (x : ℂ) :
    artinComplexJacquetSection rho x = (Real.Gamma (4 / 3))⁻¹ *
      ∫ t : ℝ in Ioi 0, t ^ (1 / 3 : ℝ) *
        Real.exp (-((rho ^ 2 + ‖x‖ ^ 2) * t)) := by
  have h := artinPositiveLaplace_normalized (a := 4 / 3)
    (r := rho ^ 2 + ‖x‖ ^ 2) (by norm_num) (by positivity)
  norm_num at h
  exact h.symm

theorem artinComplexJacquetIntegrand_norm {rho : ℝ} (hrho : 0 < rho)
    (c : ℝ) (x : ℂ) :
    ‖artinComplexJacquetIntegrand rho c x‖ = artinComplexJacquetSection rho x := by
  rw [artinComplexJacquetIntegrand, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (artinComplexJacquetSection_pos hrho x).le,
    Complex.norm_exp]
  simp

theorem artinComplexJacquetLaplaceKernel_gaussian (rho c t : ℝ) (x : ℂ) :
    artinComplexJacquetLaplaceKernel rho c t x =
      ((t ^ (1 / 3 : ℝ) * Real.exp (-((rho ^ 2 + ‖x‖ ^ 2) * t)) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * c * x.re) := by
  rw [artinComplexJacquetLaplaceKernel, artinComplexGaussianFourier_product]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  norm_cast
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem artinComplexJacquetLaplaceKernel_integrable_slice {rho : ℝ}
    (hrho : 0 < rho) (c : ℝ) (x : ℂ) :
    IntegrableOn (fun t => artinComplexJacquetLaplaceKernel rho c t x) (Ioi 0) := by
  have h := artinPositiveLaplace_integrable (a := 4 / 3)
    (r := rho ^ 2 + ‖x‖ ^ 2) (by norm_num) (by positivity)
  norm_num at h
  apply (h.ofReal.mul_const (Complex.exp (-Complex.I * c * x.re))).congr
  exact Filter.Eventually.of_forall fun t =>
    (artinComplexJacquetLaplaceKernel_gaussian rho c t x).symm

theorem artinComplexJacquetIntegrand_laplace {rho : ℝ} (hrho : 0 < rho)
    (c : ℝ) (x : ℂ) :
    artinComplexJacquetIntegrand rho c x = ((Real.Gamma (4 / 3))⁻¹ : ℝ) *
      ∫ t : ℝ in Ioi 0, artinComplexJacquetLaplaceKernel rho c t x := by
  rw [artinComplexJacquetIntegrand, artinComplexJacquetSection_laplace hrho x]
  simp_rw [artinComplexJacquetLaplaceKernel_gaussian]
  rw [integral_mul_const]
  rw [integral_complex_ofReal]
  push_cast
  ring

theorem artinComplexGaussianFourier_norm_integral {t : ℝ} (ht : 0 < t) (c : ℝ) :
    (∫ x : ℂ, ‖artinComplexGaussianFourier t c x‖) = Real.pi / t := by
  simp_rw [artinComplexGaussianFourier_norm]
  have h := artinComplexGaussianFourier_integral ht 0
  simp_rw [artinComplexGaussianFourier_product] at h
  simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, zero_pow (by norm_num :
    (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem artinComplexJacquetLaplaceKernel_area_integrable {t : ℝ} (ht : 0 < t)
    (rho c : ℝ) :
    Integrable (artinComplexJacquetLaplaceKernel rho c t) := by
  exact (artinComplexGaussianFourier_integrable ht c).const_mul _

theorem artinComplexJacquetLaplaceKernel_norm_area {t : ℝ} (ht : 0 < t)
    (rho c : ℝ) :
    (∫ x : ℂ, ‖artinComplexJacquetLaplaceKernel rho c t x‖) =
      Real.pi * (t ^ (-(2 / 3 : ℝ)) * Real.exp (-(rho ^ 2 * t))) := by
  simp only [artinComplexJacquetLaplaceKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _),
    abs_of_pos (Real.exp_pos _)]
  rw [integral_const_mul, artinComplexGaussianFourier_norm_integral ht c]
  have hp : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_sub_one (ne_of_gt ht)]
    norm_num
  calc
    _ = Real.pi * (t ^ (1 / 3 : ℝ) / t) * Real.exp (-(rho ^ 2 * t)) := by ring
    _ = _ := by rw [hp]; ring

/-- Absolute convergence supplies Fubini; no exchange of conditionally convergent integrals. -/
theorem artinComplexJacquetLaplaceKernel_integrable {rho : ℝ} (hrho : 0 < rho)
    (c : ℝ) :
    Integrable (fun p : ℝ × ℂ => artinComplexJacquetLaplaceKernel rho c p.1 p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  apply (integrable_prod_iff (by
    unfold artinComplexJacquetLaplaceKernel artinComplexGaussianFourier
    fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact artinComplexJacquetLaplaceKernel_area_integrable ht rho c
  · have h := (artinPositiveLaplace_integrable (a := 1 / 3) (r := rho ^ 2)
      (by norm_num) (by positivity)).const_mul Real.pi
    norm_num at h
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (artinComplexJacquetLaplaceKernel_norm_area ht rho c).symm

theorem artinComplexJacquetIntegrand_integrable {rho : ℝ} (hrho : 0 < rho)
    (c : ℝ) : Integrable (artinComplexJacquetIntegrand rho c) := by
  have h := (artinComplexJacquetLaplaceKernel_integrable hrho c).integral_prod_right
  apply (h.const_mul (((Real.Gamma (4 / 3))⁻¹ : ℝ) : ℂ)).congr
  exact Filter.Eventually.of_forall fun x =>
    (artinComplexJacquetIntegrand_laplace hrho c x).symm

theorem artinComplexJacquetLaplaceKernel_area {t : ℝ} (ht : 0 < t) (rho c : ℝ) :
    (∫ x : ℂ, artinComplexJacquetLaplaceKernel rho c t x) =
      ((Real.pi * t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  change (∫ x : ℂ,
    ((t ^ (1 / 3 : ℝ) * Real.exp (-(rho ^ 2 * t)) : ℝ) : ℂ) *
      artinComplexGaussianFourier t c x) = _
  rw [integral_const_mul,
    artinComplexGaussianFourier_integral ht c, ← Complex.ofReal_mul]
  congr 1
  rw [Real.exp_sub, Real.exp_neg]
  have hp : t ^ (1 / 3 : ℝ) / t = t ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_sub_one (ne_of_gt ht)]
    norm_num
  rw [neg_div, Real.exp_neg]
  calc
    _ = Real.pi * (t ^ (1 / 3 : ℝ) / t) *
      (Real.exp (rho ^ 2 * t))⁻¹ * (Real.exp (c ^ 2 / (4 * t)))⁻¹ := by ring
    _ = _ := by rw [hp]; ring

theorem artinComplexJacquetIntegral_laplace {rho : ℝ} (hrho : 0 < rho) (c : ℝ) :
    artinComplexJacquetIntegral rho c =
      ((rho ^ (4 / 3 : ℝ) * Real.pi / Real.Gamma (4 / 3) : ℝ) : ℂ) *
        ∫ t : ℝ in Ioi 0,
          ((t ^ (-(2 / 3 : ℝ)) *
            Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  have he : (∫ x : ℂ, artinComplexJacquetIntegrand rho c x) =
      (((Real.Gamma (4 / 3))⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ in Ioi 0, ∫ x : ℂ, artinComplexJacquetLaplaceKernel rho c t x := by
    have hf : Integrable (Function.uncurry (artinComplexJacquetLaplaceKernel rho c))
        ((volume.restrict (Ioi 0)).prod volume) :=
      artinComplexJacquetLaplaceKernel_integrable hrho c
    calc
      _ = (((Real.Gamma (4 / 3))⁻¹ : ℝ) : ℂ) *
          ∫ x : ℂ, ∫ t : ℝ in Ioi 0, artinComplexJacquetLaplaceKernel rho c t x := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => artinComplexJacquetIntegrand_laplace hrho c x
      _ = _ := by rw [← integral_integral_swap hf]
  have hi : (∫ t : ℝ in Ioi 0, ∫ x : ℂ,
      artinComplexJacquetLaplaceKernel rho c t x) =
      (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0,
        ((t ^ (-(2 / 3 : ℝ)) *
          Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [artinComplexJacquetLaplaceKernel_area ht rho c]
    push_cast
    ring
  rw [artinComplexJacquetIntegral, he, hi]
  push_cast
  ring

theorem artinComplexJacquetLaplace_multiplicative (rho c : ℝ) :
    (∫ t : ℝ in Ioi 0,
      ((t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ)) =
    ∫ t, ((t ^ (1 / 3 : ℝ) *
      Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ)
      ∂artinPositiveMultiplicativeMeasure := by
  rw [artinPositiveMultiplicative_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [real_smul, ← Complex.ofReal_mul]
  congr 1
  have hp : t⁻¹ * t ^ (1 / 3 : ℝ) = t ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  rw [← mul_assoc, hp]

theorem artinComplexJacquetLaplace_scaled {rho c t : ℝ} (hrho : 0 < rho)
    (hc : 0 < c) (ht : 0 < t) :
    (((c / (2 * rho) * t) ^ (1 / 3 : ℝ) *
      Real.exp (-(rho ^ 2 * (c / (2 * rho) * t)) -
        c ^ 2 / (4 * (c / (2 * rho) * t))) : ℝ) : ℂ) =
    ((c / (2 * rho)) ^ (1 / 3 : ℝ) : ℝ) *
      artinBesselKIntegrand (1 / 3) (c * rho) t := by
  have hd : 0 < c / (2 * rho) := by positivity
  have he : -(rho ^ 2 * (c / (2 * rho) * t)) -
      c ^ 2 / (4 * (c / (2 * rho) * t)) =
      -(c * rho / 2) * (t + t⁻¹) := by
    field_simp
    ring
  rw [he, Real.mul_rpow hd.le ht.le, artinBesselKIntegrand]
  push_cast
  ring

theorem artinComplexJacquetLaplaceIntegral_bessel {rho c : ℝ} (hrho : 0 < rho)
    (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0,
      ((t ^ (-(2 / 3 : ℝ)) *
        Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ)) =
    ((2 * (c / (2 * rho)) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      artinBesselKIntegral (1 / 3) (c * rho) := by
  rw [artinComplexJacquetLaplace_multiplicative,
    ← artinMultiplicative_integral_comp_mul (fun t =>
      ((t ^ (1 / 3 : ℝ) * Real.exp (-(rho ^ 2 * t) - c ^ 2 / (4 * t)) : ℝ) : ℂ))
      (by positivity : 0 < c / (2 * rho))]
  have hi : (∫ t,
      (((c / (2 * rho) * t) ^ (1 / 3 : ℝ) *
        Real.exp (-(rho ^ 2 * (c / (2 * rho) * t)) -
          c ^ 2 / (4 * (c / (2 * rho) * t))) : ℝ) : ℂ)
        ∂artinPositiveMultiplicativeMeasure) =
      (((c / (2 * rho)) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        ∫ t, artinBesselKIntegrand (1 / 3) (c * rho) t
          ∂artinPositiveMultiplicativeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
    exact artinComplexJacquetLaplace_scaled hrho hc ht
  rw [hi, artinBesselKIntegral]
  push_cast
  ring

theorem artinComplexJacquet_normalization {rho c : ℝ} (hrho : 0 < rho)
    (hc : 0 < c) :
    rho ^ (4 / 3 : ℝ) * (c / (2 * rho)) ^ (1 / 3 : ℝ) =
      (c / 2) ^ (1 / 3 : ℝ) * rho := by
  rw [show c / (2 * rho) = (c / 2) / rho by ring,
    Real.div_rpow (by positivity) hrho.le]
  have hp : rho ^ (4 / 3 : ℝ) / rho ^ (1 / 3 : ℝ) = rho := by
    rw [← Real.rpow_sub hrho]
    norm_num
  calc
    _ = (c / 2) ^ (1 / 3 : ℝ) *
      (rho ^ (4 / 3 : ℝ) / rho ^ (1 / 3 : ℝ)) := by ring
    _ = _ := by rw [hp]

/-- Exact K formula for the actual ordinary-area Jacquet integral.
The original cover/representation, Haar and character conventions are a separate identification. -/
theorem artinComplexJacquetIntegral_bessel {rho c : ℝ} (hrho : 0 < rho)
    (hc : 0 < c) :
    artinComplexJacquetIntegral rho c =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) * rho : ℝ) : ℂ) *
        artinBesselKIntegral (1 / 3) (c * rho) := by
  rw [artinComplexJacquetIntegral_laplace hrho,
    artinComplexJacquetLaplaceIntegral_bessel hrho hc, ← mul_assoc,
    ← Complex.ofReal_mul]
  congr 1
  congr 1
  calc
    _ = (2 * Real.pi / Real.Gamma (4 / 3)) *
      (rho ^ (4 / 3 : ℝ) * (c / (2 * rho)) ^ (1 / 3 : ℝ)) := by ring
    _ = _ := by rw [artinComplexJacquet_normalization hrho hc]; ring

theorem artinComplexJacquetIntegral_spherical {rho c : ℝ} (hrho : 0 < rho)
    (hc : 0 < c) :
    artinComplexJacquetIntegral rho c =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        artinSphericalBesselProfile c (rho ^ 2) := by
  rw [artinComplexJacquetIntegral_bessel hrho hc, artinSphericalBesselProfile,
    Real.sqrt_sq_eq_abs, abs_of_pos hrho]
  push_cast
  ring

/-- The radial variable is the squared ordinary complex modulus. -/
def artinComplexJacquetRadialProfile (c u : ℝ) : ℂ :=
  artinComplexJacquetIntegral (Real.sqrt u) c

theorem artinComplexJacquetRadialProfile_eq_spherical {c u : ℝ} (hc : 0 < c)
    (hu : 0 < u) :
    artinComplexJacquetRadialProfile c u =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        artinSphericalBesselProfile c u := by
  rw [artinComplexJacquetRadialProfile,
    artinComplexJacquetIntegral_spherical (Real.sqrt_pos.mpr hu) hc,
    Real.sq_sqrt hu.le]

theorem artinComplexJacquet_prefactor_pos {c : ℝ} (hc : 0 < c) :
    0 < 2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) := by
  positivity

theorem artinComplexJacquetRadialProfile_mellin_convergent {c : ℝ} (hc : 0 < c)
    {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re) :
    MellinConvergent (artinComplexJacquetRadialProfile c) s := by
  have h := (artinSphericalBesselProfile_mellin_convergent hc hs).const_smul
    (((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ))
  apply (integrableOn_congr_fun (fun u hu => ?_) measurableSet_Ioi).mpr h
  change (u : ℂ) ^ (s - 1) * artinComplexJacquetRadialProfile c u = _
  rw [artinComplexJacquetRadialProfile_eq_spherical hc hu]
  rfl

theorem artinComplexJacquetRadialProfile_mellin {c : ℝ} (hc : 0 < c)
    {s : ℂ} (hs : -(1 / 3 : ℝ) < s.re) :
    mellin (artinComplexJacquetRadialProfile c) s =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (((2 / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ (s - 1 / 2) *
        (Complex.Gamma (s + 1 / 3) * Complex.Gamma (s + 2 / 3))) := by
  have he : mellin (artinComplexJacquetRadialProfile c) s =
      mellin (fun u =>
        (((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) •
          artinSphericalBesselProfile c u) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change (u : ℂ) ^ (s - 1) * artinComplexJacquetRadialProfile c u = _
    rw [artinComplexJacquetRadialProfile_eq_spherical hc hu]
    rfl
  rw [he, mellin_const_smul, artinSphericalBesselProfile_mellin hc hs, smul_eq_mul]

end
end SimultaneousPrimitiveRoots

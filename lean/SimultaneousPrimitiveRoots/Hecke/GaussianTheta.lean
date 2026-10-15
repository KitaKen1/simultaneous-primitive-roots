module

public import SimultaneousPrimitiveRoots.Hecke.GaussianSummable
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The theta transformation formula for a lattice

For an invertible linear map `A` of `ℝ^d` and `t > 0`,

`∑_{m ∈ ℤ^d} exp(-π t |A m|²) = |det A|⁻¹ t^{-d/2} ∑_{n ∈ ℤ^d} exp(-π |A^{-T} n|² / t)`,

where `|·|` is the Euclidean norm. This is the Gaussian case of Poisson summation for the lattice
`A ℤ^d`, whose dual lattice is `A^{-T} ℤ^d`. It is the input for Hecke's theta function of a
number field (step B7 of the project roadmap).
-/

@[expose] public section
noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Matrix
open scoped Real

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The dot product on `d → ℝ`. -/
def dotR (x y : d → ℝ) : ℝ := ∑ i, x i * y i

omit [DecidableEq d] in
/-- The torus character is the usual exponential. -/
theorem charPi_eq (n : d → ℤ) (u : d → ℝ) :
    charPi n u = Complex.exp (-(2 * π * Complex.I) * ((dotR (intVec n) u : ℝ) : ℂ)) := by
  unfold charPi
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusMk, Pi.neg_apply]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotR, intVec_apply]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The matrix of `A⁻¹`. -/
def invMatrix (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : Matrix d d ℝ :=
  LinearMap.toMatrix' (A.symm : (d → ℝ) →ₗ[ℝ] (d → ℝ))

/-- The matrix of `A`. -/
def fwdMatrix (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : Matrix d d ℝ :=
  LinearMap.toMatrix' (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))

theorem fwd_mul_inv (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : fwdMatrix A * invMatrix A = 1 := by
  unfold fwdMatrix invMatrix
  rw [← LinearMap.toMatrix'_comp]
  have : (A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) ∘ₗ (A.symm : (d → ℝ) →ₗ[ℝ] (d → ℝ)) = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

theorem inv_mul_fwd (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : invMatrix A * fwdMatrix A = 1 := by
  unfold fwdMatrix invMatrix
  rw [← LinearMap.toMatrix'_comp]
  have : (A.symm : (d → ℝ) →ₗ[ℝ] (d → ℝ)) ∘ₗ (A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) = LinearMap.id := by
    ext x
    simp
  rw [this, LinearMap.toMatrix'_id]

/-- The transpose-inverse `A^{-T}`, describing the dual lattice. -/
def dualEquiv (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : (d → ℝ) ≃ₗ[ℝ] (d → ℝ) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (invMatrix A)ᵀ) (Matrix.toLin' (fwdMatrix A)ᵀ)
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, fwd_mul_inv, Matrix.transpose_one,
        Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, inv_mul_fwd, Matrix.transpose_one,
        Matrix.toLin'_one])

theorem dualEquiv_apply (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v : d → ℝ) :
    dualEquiv A v = (invMatrix A)ᵀ *ᵥ v := by
  simp [dualEquiv, Matrix.toLin'_apply]

/-- `n · u = (A^{-T} n) · (A u)`. -/
theorem dotR_eq_dual (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (v u : d → ℝ) :
    dotR v u = dotR (dualEquiv A v) (A u) := by
  have hu : u = invMatrix A *ᵥ (A u) := by
    unfold invMatrix
    rw [LinearMap.toMatrix'_mulVec]
    simp
  have h1 : dotR v u = v ⬝ᵥ u := rfl
  have h2 : dotR (dualEquiv A v) (A u) = (dualEquiv A v) ⬝ᵥ (A u) := rfl
  rw [h1, h2, dualEquiv_apply, Matrix.mulVec_transpose]
  conv_lhs => rw [hu]
  rw [Matrix.dotProduct_mulVec]

/-- The Gaussian after the change of variables `x = A u`. -/
def gaussianTarget (ξ : d → ℝ) (t : ℝ) (x : d → ℝ) : ℂ :=
  Complex.exp (-(((π * t : ℝ)) : ℂ) * ∑ i, ((x i : ℝ) : ℂ) ^ 2 +
    ∑ i, (-(2 * π * Complex.I) * (ξ i : ℂ)) * ((x i : ℝ) : ℂ))

theorem charPi_mul_gaussian (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (t : ℝ) (n : d → ℤ) (u : d → ℝ) :
    charPi n u * gaussianCM A (π * t) u =
      gaussianTarget (dualEquiv A (intVec n)) t (A u) := by
  rw [charPi_eq, gaussianCM_apply, dotR_eq_dual A, Complex.ofReal_exp, ← Complex.exp_add]
  unfold gaussianTarget
  congr 1
  simp only [dotR, sqNorm]
  push_cast
  have e1 : -(2 * π * Complex.I) *
      ∑ i, ((dualEquiv A (intVec n) i : ℝ) : ℂ) * ((A u i : ℝ) : ℂ) =
      ∑ i, (-(2 * π * Complex.I) * ((dualEquiv A (intVec n) i : ℝ) : ℂ)) *
        ((A u i : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linear_combination e1

theorem integral_gaussianTarget (ξ : d → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ x, gaussianTarget ξ t x =
      (((1 / t) ^ ((Fintype.card d : ℝ) / 2) * Real.exp (-π * sqNorm ξ / t) : ℝ) : ℂ) := by
  have hb : 0 < (((π * t : ℝ)) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  unfold gaussianTarget
  rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb]
  have hpi : (π : ℂ) / (((π * t : ℝ)) : ℂ) = (((1 / t : ℝ)) : ℂ) := by
    push_cast
    field_simp
  rw [hpi]
  have hcpow : (((1 / t : ℝ)) : ℂ) ^ ((Fintype.card d : ℂ) / 2) =
      ((((1 / t) ^ ((Fintype.card d : ℝ) / 2) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [hcpow]
  have hexp : Complex.exp ((∑ i, (-(2 * π * Complex.I) * (ξ i : ℂ)) ^ 2) /
      (4 * (((π * t : ℝ)) : ℂ))) = (((Real.exp (-π * sqNorm ξ / t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    simp only [sqNorm]
    push_cast
    have hsum : ∑ i, (-(2 * π * Complex.I) * (ξ i : ℂ)) ^ 2 =
        -(4 * π ^ 2) * ∑ i, (ξ i : ℂ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hsum]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hexp]
  push_cast
  ring

/-- **The Fourier coefficients of the Gaussian on the lattice.** -/
theorem fourierInt_gaussian (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t) (n : d → ℤ) :
    fourierInt (gaussianCM A (π * t)) n =
      ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
        ((1 / t) ^ ((Fintype.card d : ℝ) / 2) *
          Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t)) : ℝ) : ℂ) := by
  have hdet : LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' A).ne_zero
  unfold fourierInt
  simp_rw [charPi_mul_gaussian]
  have hmeas : Measurable (A : (d → ℝ) → (d → ℝ)) :=
    (A.toLinearMap.continuous_of_finiteDimensional).measurable
  have hcont : Continuous (gaussianTarget (dualEquiv A (intVec n)) t) := by
    unfold gaussianTarget
    fun_prop
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  rw [← integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  change ∫ x, gaussianTarget (dualEquiv A (intVec n)) t x ∂(Measure.map
    ((A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) : (d → ℝ) → (d → ℝ)) volume) = _
  rw [hmap, integral_smul_measure, integral_gaussianTarget _ ht]
  rw [ENNReal.toReal_ofReal (by positivity), abs_inv]
  rw [Complex.real_smul]
  push_cast
  ring

/-- **The theta transformation formula for the lattice `A ℤ^d`.** -/
theorem tsum_gaussian_eq (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t) :
    ∑' m : d → ℤ, Real.exp (-(π * t) * sqNorm (A (intVec m))) =
      |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ * (1 / t) ^ ((Fintype.card d : ℝ) / 2) *
        ∑' n : d → ℤ, Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t) := by
  have hc : 0 < π * t := by positivity
  have hf := translatesSummable_gaussian A hc
  -- summability of the dual side
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower (dualEquiv A)
  have hdual : Summable fun n : d → ℤ =>
      Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t) := by
    have hs := summable_exp_neg_norm_sq (d := d) (a := π * κ / t) (by positivity)
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_) hs
    apply Real.exp_le_exp.mpr
    have h := hκA (intVec n)
    have hpt : 0 < π / t := by positivity
    have : π / t * (κ * ‖intVec n‖ ^ 2) ≤ π / t * sqNorm (dualEquiv A (intVec n)) :=
      mul_le_mul_of_nonneg_left h hpt.le
    have e1 : -π * sqNorm (dualEquiv A (intVec n)) / t =
        -(π / t * sqNorm (dualEquiv A (intVec n))) := by ring
    have e2 : -(π * κ / t) * ‖intVec n‖ ^ 2 = -(π / t * (κ * ‖intVec n‖ ^ 2)) := by ring
    rw [e1, e2]
    linarith
  have hF : Summable fun n : d → ℤ => fourierInt (gaussianCM A (π * t)) n := by
    simp_rw [fourierInt_gaussian A ht]
    apply Complex.summable_ofReal.mpr
    exact (hdual.mul_left _).mul_left _
  have hpoisson := tsum_eq_tsum_fourierInt hf hF
  simp_rw [fourierInt_gaussian A ht, gaussianCM_apply] at hpoisson
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum] at hpoisson
  have hreal := Complex.ofReal_injective hpoisson
  rw [hreal, tsum_mul_left, tsum_mul_left]
  ring

end SimultaneousPrimitiveRoots.Hecke

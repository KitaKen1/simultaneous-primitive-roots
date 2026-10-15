module

public import SimultaneousPrimitiveRoots.Hecke.GaussianTheta

/-!
# The theta transformation for a shifted lattice

For an invertible linear map `A` of `ℝ^d`, `t > 0` and a shift `v ∈ ℝ^d`,

`∑_{m ∈ ℤ^d} exp(-π t |A(m + v)|²)
  = |det A|⁻¹ t^{-d/2} ∑_{n ∈ ℤ^d} e(n·v) exp(-π |A^{-T} n|² / t)`

(`tsum_shiftedGaussian_eq`), where `e(n·v) = charPi n (-v)`.

This is the first input of Hecke's continuation of the partial zeta functions of ray classes
(step Z2 of `docs/unconditional-roadmap.md`): a coset `α₀ + 𝔪𝔟` is a shifted lattice, and the
phases `e(n·v)` on the dual side are additive characters. The proof is Poisson summation
(`tsum_eq_tsum_fourierInt`) for the translated Gaussian, whose Fourier coefficients are those of
the Gaussian times `e(n·v)` (`fourierInt_comp_addRight`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Matrix
open scoped Real

variable {d : Type*} [Fintype d]

omit [Fintype d] in
theorem torusMk_add (x y : d → ℝ) : torusMk (x + y) = torusMk x + torusMk y := by
  funext i
  simp [torusMk]

omit [Fintype d] in
theorem fourier_add_point (k : ℤ) (a b : UnitAddCircle) :
    fourier k (a + b) = fourier k a * fourier k b := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- The characters of the torus are multiplicative in the point. -/
theorem mFourier_add_point (m : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier m (x + y) = UnitAddTorus.mFourier m x * UnitAddTorus.mFourier m y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => fourier_add_point (m i) (x i) (y i)

/-- The torus characters are additive characters of `ℝ^d`. -/
theorem charPi_add (n : d → ℤ) (x y : d → ℝ) : charPi n (x + y) = charPi n x * charPi n y := by
  simp only [charPi, torusMk_add, mFourier_add_point]

theorem charPi_zero_right (n : d → ℤ) : charPi n 0 = 1 := by
  have h := charPi_add n 0 0
  rw [add_zero] at h
  have hn : charPi n 0 ≠ 0 := by
    intro h0
    have := norm_charPi n 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have : charPi n 0 * charPi n 0 = charPi n 0 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ hn this

/-- **Fourier coefficients of a translate.** `f(· + v)` has coefficients `e(n·v) f̂(n)`. -/
theorem fourierInt_comp_addRight (f : (d → ℝ) → ℂ) (v : d → ℝ) (n : d → ℤ) :
    fourierInt (fun x => f (x + v)) n = charPi n (-v) * fourierInt f n := by
  unfold fourierInt
  have h : ∀ x : d → ℝ, charPi n x * f (x + v) = charPi n (-v) * (charPi n (x + v) * f (x + v)) := by
    intro x
    have hx : charPi n x = charPi n (x + v) * charPi n (-v) := by
      rw [← charPi_add]
      congr 1
      abel
    rw [hx]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  congr 1
  exact integral_add_right_eq_self (fun y => charPi n y * f y) v

variable [DecidableEq d]

/-- The translated Gaussian `u ↦ exp(-c |A(u + v)|²)`. -/
def shiftedGaussianCM (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (c : ℝ) (v : d → ℝ) : C(d → ℝ, ℂ) :=
  (gaussianCM A c).comp (ContinuousMap.addRight v)

omit [DecidableEq d] in
theorem shiftedGaussianCM_apply (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) (c : ℝ) (v u : d → ℝ) :
    shiftedGaussianCM A c v u = ((Real.exp (-c * sqNorm (A (u + v))) : ℝ) : ℂ) := rfl

omit [DecidableEq d] in
/-- Integer translates of the translated Gaussian are summable uniformly on compact sets. -/
theorem translatesSummable_shiftedGaussian (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {c : ℝ} (hc : 0 < c)
    (v : d → ℝ) : TranslatesSummable (shiftedGaussianCM A c v) := by
  intro K
  set K' : TopologicalSpace.Compacts (d → ℝ) := K.map (· + v) (continuous_id.add continuous_const)
  have h := translatesSummable_gaussian A hc K'
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) h
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro x
  have hx' : (x : d → ℝ) + v ∈ (K' : Set (d → ℝ)) := by
    change (x : d → ℝ) + v ∈ (fun y => y + v) '' (K : Set (d → ℝ))
    exact ⟨x, x.2, rfl⟩
  have hle := ContinuousMap.norm_coe_le_norm
    (((gaussianCM A c).comp (ContinuousMap.addRight (intVec m))).restrict (K' : Set (d → ℝ)))
    ⟨_, hx'⟩
  refine le_of_eq_of_le ?_ hle
  simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    shiftedGaussianCM]
  congr 2
  abel

/-- **The theta transformation formula for the shifted lattice `A(ℤ^d + v)`.** -/
theorem tsum_shiftedGaussian_eq (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t)
    (v : d → ℝ) :
    ∑' m : d → ℤ, ((Real.exp (-(π * t) * sqNorm (A (intVec m + v))) : ℝ) : ℂ) =
      ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
          (1 / t) ^ ((Fintype.card d : ℝ) / 2) : ℝ) : ℂ) *
        ∑' n : d → ℤ, charPi n (-v) *
          ((Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t) : ℝ) : ℂ) := by
  have hc : 0 < π * t := by positivity
  have hf := translatesSummable_shiftedGaussian A hc v
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
  -- the Fourier coefficients of the translate
  have hcoeff : ∀ n : d → ℤ, fourierInt (shiftedGaussianCM A (π * t) v) n =
      charPi n (-v) * ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
        ((1 / t) ^ ((Fintype.card d : ℝ) / 2) *
          Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t)) : ℝ) : ℂ) := by
    intro n
    rw [← fourierInt_gaussian A ht n]
    exact fourierInt_comp_addRight (gaussianCM A (π * t)) v n
  have hF : Summable fun n : d → ℤ => fourierInt (shiftedGaussianCM A (π * t) v) n := by
    simp_rw [hcoeff]
    refine Summable.of_norm ?_
    have hn : ∀ n : d → ℤ, ‖charPi n (-v) * ((|LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
        ((1 / t) ^ ((Fintype.card d : ℝ) / 2) *
          Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t)) : ℝ) : ℂ)‖ =
        |LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ))|⁻¹ *
          ((1 / t) ^ ((Fintype.card d : ℝ) / 2) *
            Real.exp (-π * sqNorm (dualEquiv A (intVec n)) / t)) := by
      intro n
      rw [norm_mul, norm_charPi, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    simp_rw [hn]
    exact (hdual.mul_left _).mul_left _
  have hpoisson := tsum_eq_tsum_fourierInt hf hF
  simp_rw [hcoeff, shiftedGaussianCM_apply] at hpoisson
  rw [hpoisson, ← tsum_mul_left]
  apply tsum_congr
  intro n
  push_cast
  ring

end SimultaneousPrimitiveRoots.Hecke

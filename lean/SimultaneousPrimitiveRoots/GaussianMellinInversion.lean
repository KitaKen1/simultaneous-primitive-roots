module

public import SimultaneousPrimitiveRoots.GaussianWeight

@[expose] public section

namespace SimultaneousPrimitiveRoots

open MeasureTheory
noncomputable section

/-- The vertical inverse kernel is an actual integrable complex Gaussian. -/
theorem artinGaussianMellin_inverse_kernel (σ : ℝ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (t : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
        artinGaussianMellin ((σ : ℂ) + y * Complex.I) =
      (Real.sqrt Real.pi : ℂ) * Complex.exp
        ((-1 / 4 : ℂ) * (y : ℂ) ^ 2 +
          (((σ / 2 - Real.log t : ℝ) : ℂ) * Complex.I) * y +
          (((Real.log 2) ^ 2 + σ ^ 2 / 4 - σ * Real.log t : ℝ) : ℂ)) := by
  rw [artinGaussianMellin,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  simp only [add_sq, mul_pow, Complex.I_sq]
  ring

theorem artinGaussianMellin_inverse_integrable (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => (t : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
      artinGaussianMellin ((σ : ℂ) + y * Complex.I)) := by
  simp_rw [artinGaussianMellin_inverse_kernel σ ht]
  exact (integrable_cexp_quadratic' (b := (-1 / 4 : ℂ)) (by norm_num)
    (((σ / 2 - Real.log t : ℝ) : ℂ) * Complex.I)
    (((Real.log 2) ^ 2 + σ ^ 2 / 4 - σ * Real.log t : ℝ) : ℂ)).const_mul _

/-- Exact inverse integral for every real vertical line; no abstract
Mellin inversion theorem or contour shift is assumed. -/
theorem artinGaussianMellin_inverse_integral (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ y : ℝ, (t : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
      artinGaussianMellin ((σ : ℂ) + y * Complex.I)) =
        ((2 * Real.pi * artinGaussianWeight t : ℝ) : ℂ) := by
  simp_rw [artinGaussianMellin_inverse_kernel σ ht]
  rw [integral_const_mul,
    integral_cexp_quadratic (b := (-1 / 4 : ℂ)) (by norm_num)]
  have hsqrt : ((Real.pi : ℂ) / -(-1 / 4 : ℂ)) ^ (1 / 2 : ℂ) =
      ((2 * Real.sqrt Real.pi : ℝ) : ℂ) := by
    have heq : (Real.pi : ℂ) / -(-1 / 4 : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
      norm_num
    rw [hfour]
  rw [hsqrt]
  have hexp :
      (((Real.log 2) ^ 2 + σ ^ 2 / 4 - σ * Real.log t : ℝ) : ℂ) -
        ((((σ / 2 - Real.log t : ℝ) : ℂ) * Complex.I) ^ 2) / (4 * (-1 / 4 : ℂ)) =
      (((Real.log 2) ^ 2 - (Real.log t) ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [mul_pow, Complex.I_sq]
    ring
  rw [hexp, ← Complex.ofReal_exp]
  rw [artinGaussianWeight]
  push_cast
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  linear_combination (2 * Complex.exp ((Real.log 2 : ℂ) ^ 2 - (Real.log t : ℂ) ^ 2)) * hsq

/-- The actual Mellin inverse of the specified Gaussian equals the weight. -/
theorem artinGaussianMellin_mellinInv (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    mellinInv σ artinGaussianMellin t = (artinGaussianWeight t : ℂ) := by
  rw [mellinInv]
  simp only [smul_eq_mul, Complex.real_smul]
  rw [artinGaussianMellin_inverse_integral σ ht]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end
end SimultaneousPrimitiveRoots

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- Euler's integral already gives the vertical-line upper bound needed
on the reflected Gamma factor; no Stirling asymptotic is required. -/
theorem reflectionGamma_norm_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  calc
    _ ≤ ∫ T : ℝ in Ioi 0, ‖(Real.exp (-T) : ℂ) * (T : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hT]
      simp only [Complex.sub_re, Complex.one_re]

theorem reflectionGamma_sin_norm_le (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  norm_num only [norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ :=
      norm_sub_le _ _
    _ = Real.exp z.im + Real.exp (-z.im) := by simp [Complex.norm_exp, Complex.mul_re]
    _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _))
        (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

/-- Below Re(z)=1 the reflected Gamma factor has positive real part.
This exact identity also holds at Gamma's nonpositive integer poles. -/
theorem reflectionGamma_inv_eq {z : ℂ} (hz : z.re < 1) :
    (Complex.Gamma z)⁻¹ = Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Complex.Gamma (1 - z) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have h := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hr := Complex.Gamma_mul_Gamma_one_sub z
  by_cases h0 : Complex.Gamma z = 0
  · have hsin : Complex.sin (Real.pi * z) = 0 := by
      by_contra hn
      rw [h0, zero_mul] at hr
      exact (div_ne_zero hπ hn) hr.symm
    simp only [h0, inv_zero, hsin, mul_zero, zero_div]
  · have hsin : Complex.sin (Real.pi * z) ≠ 0 := by
      intro hn
      rw [hn, div_zero] at hr
      exact mul_ne_zero h0 hg hr
    have hp : (Complex.Gamma z * Complex.Gamma (1 - z)) *
        Complex.sin (Real.pi * z) = Real.pi := by
      rw [hr, div_mul_cancel₀ _ hsin]
    apply mul_left_cancel₀ h0
    rw [mul_inv_cancel₀ h0, ← mul_div_assoc, ← mul_assoc, hp, div_self hπ]

theorem reflectionGamma_inv_norm_le {z : ℂ} (hz : z.re < 1) :
    ‖(Complex.Gamma z)⁻¹‖ ≤
      (Real.Gamma (1 - z.re) / Real.pi) * Real.exp (Real.pi * |z.im|) := by
  rw [reflectionGamma_inv_eq hz, norm_div, norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hg := reflectionGamma_norm_le (z := 1 - z) (by simp only [sub_re, one_re]; linarith)
  have hs := reflectionGamma_sin_norm_le ((Real.pi : ℂ) * z)
  have him : |((Real.pi : ℂ) * z).im| = Real.pi * |z.im| := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos]
  rw [him] at hs
  have hg0 : 0 ≤ Real.Gamma (1 - z.re) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hprod := mul_le_mul hg hs (norm_nonneg _) hg0
  simp only [Complex.sub_re, Complex.one_re] at hprod
  simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hprod Real.pi_pos.le

/-- The explicit reciprocal-Gamma quotient displayed in A-03.
The Mellin transform of the actual Bessel profile is still a separate identity. -/
def reflectionGammaQuotient (C A : ℝ) (r : ℕ) (z : ℂ) : ℂ :=
  (C : ℂ)⁻¹ * (A : ℂ) ^ (-z) * Complex.exp (z ^ 2) *
    ((Complex.Gamma (z + 5 / 6))⁻¹ * (Complex.Gamma (z + 7 / 6))⁻¹) ^ r

theorem reflectionGammaQuotient_entire (C : ℝ) {A : ℝ} (hA : 0 < A) (r : ℕ) :
    Differentiable ℂ (reflectionGammaQuotient C A r) := by
  have h1 := Complex.differentiable_one_div_Gamma.comp
    (differentiable_id.add_const (5 / 6 : ℂ))
  have h2 := Complex.differentiable_one_div_Gamma.comp
    (differentiable_id.add_const (7 / 6 : ℂ))
  have hp := (h1.mul h2).pow r
  have ha : Differentiable ℂ (fun z : ℂ => (A : ℂ) ^ (-z)) := by
    exact differentiable_id.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hA.ne'))
  exact (((ha.const_mul (C : ℂ)⁻¹).mul (differentiable_id.pow 2).cexp).mul hp)

end
end SimultaneousPrimitiveRoots

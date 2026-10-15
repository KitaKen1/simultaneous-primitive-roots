module

public import SimultaneousPrimitiveRoots.ReflectionGammaStrip
public import Mathlib.Analysis.MellinInversion

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped FourierTransform
noncomputable section

def reflectionInverseMellinIntegrand (C A : ℝ) (r : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (T : ℂ) ^ z * reflectionGammaQuotient C A r z

theorem reflectionInverseMellinIntegrand_entire (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r : ℕ) :
    Differentiable ℂ (reflectionInverseMellinIntegrand C A r T) :=
  (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hT.ne'))).mul
    (reflectionGammaQuotient_entire C hA r)

theorem reflectionInverseMellinIntegrand_norm (C A : ℝ) (r : ℕ) {T : ℝ}
    (hT : 0 < T) (z : ℂ) :
    ‖reflectionInverseMellinIntegrand C A r T z‖ =
      T ^ z.re * ‖reflectionGammaQuotient C A r z‖ := by
  rw [reflectionInverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT]

theorem reflectionInverseMellinIntegrand_strip_gaussian (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r : ℕ) (l u : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖reflectionInverseMellinIntegrand C A r T z‖ ≤
        B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2) := by
  obtain ⟨B, hB, hb⟩ := reflectionGammaQuotient_strip_gaussian C hA r l u
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_const_rpow hT.ne').continuousOn
  refine ⟨(max M 1) * B, mul_pos
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hB, fun z hl hu => ?_⟩
  have hm : T ^ z.re ≤ max M 1 :=
    ((le_abs_self _).trans (hM _ ⟨hl, hu⟩)).trans (le_max_left _ _)
  rw [reflectionInverseMellinIntegrand_norm C A r hT]
  exact (mul_le_mul hm (hb z hl hu) (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem reflectionInverseMellinIntegrand_integrable (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r : ℕ) (σ : ℝ) :
    Integrable (fun y : ℝ => reflectionInverseMellinIntegrand C A r T ((σ : ℂ) + y * I)) := by
  have hc : Continuous (fun y : ℝ => reflectionInverseMellinIntegrand C A r T
      ((σ : ℂ) + y * I)) :=
    (reflectionInverseMellinIntegrand_entire C hA hT r).continuous.comp (by fun_prop)
  apply ((reflectionGammaQuotient_integrable_line C hA r σ).norm.const_mul (T ^ σ)).mono'
    hc.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [reflectionInverseMellinIntegrand_norm C A r hT]
  simp

/-- The actual vertical integral is defined with its line parameter visible.
Its independence of that parameter is not included in this definition. -/
def reflectionInverseMellinLine (C A : ℝ) (r : ℕ) (σ T : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ y : ℝ, reflectionInverseMellinIntegrand C A r T ((σ : ℂ) + y * I)

theorem reflectionInverseMellinLine_bound (C : ℝ) {A : ℝ} (_hA : 0 < A)
    (r : ℕ) (σ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionInverseMellinLine C A r σ T‖ ≤ M * T ^ σ := by
  let M : ℝ := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖reflectionGammaQuotient C A r ((σ : ℂ) + y * I)‖
  refine ⟨M, mul_nonneg (by positivity) (integral_nonneg (fun y => norm_nonneg _)),
    fun T hT => ?_⟩
  rw [reflectionInverseMellinLine, norm_mul,
    Complex.norm_of_nonneg (by positivity : 0 ≤ (1 / (2 * Real.pi) : ℝ))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ,
        ‖reflectionInverseMellinIntegrand C A r T ((σ : ℂ) + y * I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = M * T ^ σ := by
      simp only [reflectionInverseMellinIntegrand_norm C A r hT, add_re, ofReal_re,
        mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
      rw [integral_const_mul]
      dsimp [M]
      ring

theorem reflectionInverseMellinLine_eq_mellinInv (C A : ℝ) (r : ℕ) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) :
    reflectionInverseMellinLine C A r σ T = mellinInv σ (reflectionGammaQuotient C A r) T⁻¹ := by
  rw [reflectionInverseMellinLine, mellinInv]
  simp only [Complex.real_smul, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  unfold reflectionInverseMellinIntegrand
  dsimp only
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hT.le, Complex.cpow_neg,
    inv_inv]

theorem reflectionInverseMellinLine_fourier (C A : ℝ) (r : ℕ) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) :
    reflectionInverseMellinLine C A r σ T =
      (T : ℂ) ^ (σ : ℂ) *
        𝓕⁻ (fun y : ℝ => reflectionGammaQuotient C A r ((σ : ℂ) + (2 * Real.pi * y) * I))
          (Real.log T) := by
  rw [reflectionInverseMellinLine_eq_mellinInv C A r σ hT,
    mellinInv_eq_fourierInv σ _ (inv_pos.mpr hT), Real.log_inv, neg_neg,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hT.le, Complex.cpow_neg, inv_inv]
  simp only [smul_eq_mul]

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.ReflectionKernelConstruction
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped FourierTransform
noncomputable section

def reflectionGammaJet (C A : ℝ) (r j : ℕ) (z : ℂ) : ℂ :=
  z ^ j * reflectionGammaQuotient C A r z

theorem reflectionGammaJet_entire (C : ℝ) {A : ℝ} (hA : 0 < A) (r j : ℕ) :
    Differentiable ℂ (reflectionGammaJet C A r j) :=
  (differentiable_id.pow j).mul (reflectionGammaQuotient_entire C hA r)

/-- A factorial majorant absorbs every polynomial without a Stirling theorem. -/
theorem reflectionComplex_power_strip_bound (j : ℕ) (l u : ℝ) (z : ℂ)
    (hl : l ≤ z.re) (hu : z.re ≤ u) :
    ‖z ^ j‖ ≤ (j.factorial : ℝ) * Real.exp (|l| + |u|) * Real.exp |z.im| := by
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) j)
  have hre : |z.re| ≤ |l| + |u| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self u, neg_abs_le l, abs_nonneg l, abs_nonneg u]
  rw [norm_pow]
  calc
    _ ≤ Real.exp ‖z‖ * j.factorial := hp
    _ ≤ Real.exp (|l| + |u| + |z.im|) * j.factorial := by
      gcongr
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

theorem reflectionGammaJet_strip_gaussian (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (l u : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖reflectionGammaJet C A r j z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2) := by
  obtain ⟨B, hB, hb⟩ := reflectionGammaQuotient_strip_bound C hA r l u
  let D : ℝ := (j.factorial : ℝ) * Real.exp (|l| + |u|) * B
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * Real.exp ((2 * Real.pi * r + 1) ^ 2 / 2), by positivity,
    fun z hl hu => ?_⟩
  rw [reflectionGammaJet, norm_mul]
  calc
    _ ≤ ((j.factorial : ℝ) * Real.exp (|l| + |u|) * Real.exp |z.im|) *
        (B * Real.exp (-z.im ^ 2 + (2 * Real.pi * r) * |z.im|)) :=
      mul_le_mul (reflectionComplex_power_strip_bound j l u z hl hu) (hb z hl hu)
        (norm_nonneg _) (by positivity)
    _ = D * Real.exp (-z.im ^ 2 + (2 * Real.pi * r + 1) * |z.im|) := by
      dsimp [D]
      rw [show -z.im ^ 2 + (2 * Real.pi * r + 1) * |z.im| =
        |z.im| + (-z.im ^ 2 + (2 * Real.pi * r) * |z.im|) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ D * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2 + (2 * Real.pi * r + 1) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (reflectionGamma_absorb_linear _ _)) hD.le
    _ = _ := by rw [Real.exp_add]; ring

theorem reflectionGammaJet_integrable_line (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (σ : ℝ) :
    Integrable (fun y : ℝ => reflectionGammaJet C A r j ((σ : ℂ) + y * I)) := by
  obtain ⟨B, _, hb⟩ := reflectionGammaJet_strip_gaussian C hA r j σ σ
  have hc : Continuous (fun y : ℝ => reflectionGammaJet C A r j ((σ : ℂ) + y * I)) :=
    (reflectionGammaJet_entire C hA r j).continuous.comp (by fun_prop)
  apply ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).const_mul B).mono'
    hc.aestronglyMeasurable
  exact ae_of_all _ (fun y => by simpa using hb ((σ : ℂ) + y * I) (by simp) (by simp))

def reflectionKernelJetIntegrand (C A : ℝ) (r j : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (T : ℂ) ^ z * reflectionGammaJet C A r j z

theorem reflectionKernelJetIntegrand_entire (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) :
    Differentiable ℂ (reflectionKernelJetIntegrand C A r j T) :=
  (differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hT.ne'))).mul
    (reflectionGammaJet_entire C hA r j)

theorem reflectionKernelJetIntegrand_norm (C A : ℝ) (r j : ℕ) {T : ℝ}
    (hT : 0 < T) (z : ℂ) :
    ‖reflectionKernelJetIntegrand C A r j T z‖ =
      T ^ z.re * ‖reflectionGammaJet C A r j z‖ := by
  rw [reflectionKernelJetIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hT]

theorem reflectionKernelJetIntegrand_strip_gaussian (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) (l u : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖reflectionKernelJetIntegrand C A r j T z‖ ≤
        B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2) := by
  obtain ⟨B, hB, hb⟩ := reflectionGammaJet_strip_gaussian C hA r j l u
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Real.continuous_const_rpow hT.ne').continuousOn
  refine ⟨(max M 1) * B, mul_pos
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hB, fun z hl hu => ?_⟩
  have hm : T ^ z.re ≤ max M 1 :=
    ((le_abs_self _).trans (hM _ ⟨hl, hu⟩)).trans (le_max_left _ _)
  rw [reflectionKernelJetIntegrand_norm C A r j hT]
  exact (mul_le_mul hm (hb z hl hu) (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem reflectionKernelJetIntegrand_integrable (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) (σ : ℝ) :
    Integrable (fun y : ℝ => reflectionKernelJetIntegrand C A r j T ((σ : ℂ) + y * I)) := by
  have hc : Continuous (fun y : ℝ => reflectionKernelJetIntegrand C A r j T
    ((σ : ℂ) + y * I)) :=
    (reflectionKernelJetIntegrand_entire C hA hT r j).continuous.comp (by fun_prop)
  apply ((reflectionGammaJet_integrable_line C hA r j σ).norm.const_mul (T ^ σ)).mono'
    hc.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [reflectionKernelJetIntegrand_norm C A r j hT]
  simp

def reflectionKernelJetLine (C A : ℝ) (r j : ℕ) (σ T : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ y : ℝ, reflectionKernelJetIntegrand C A r j T ((σ : ℂ) + y * I)

theorem reflectionKernelJetLine_independent (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) (σ τ : ℝ) :
    reflectionKernelJetLine C A r j σ T = reflectionKernelJetLine C A r j τ T := by
  have heq : ∀ l u : ℝ, l ≤ u →
      reflectionKernelJetLine C A r j l T = reflectionKernelJetLine C A r j u T := by
    intro l u hlu
    obtain ⟨B, _, hb⟩ := reflectionKernelJetIntegrand_strip_gaussian C hA hT r j l u
    unfold reflectionKernelJetLine
    rw [reflectionVertical_integral_eq hlu (reflectionKernelJetIntegrand_entire C hA hT r j)
      hb (reflectionKernelJetIntegrand_integrable C hA hT r j l)
      (reflectionKernelJetIntegrand_integrable C hA hT r j u)]
  rcases le_total σ τ with h | h
  · exact heq σ τ h
  · exact (heq τ σ h).symm

def reflectionKernelJet (C A : ℝ) (r j : ℕ) (T : ℝ) : ℂ :=
  reflectionKernelJetLine C A r j 0 T

theorem reflectionKernelJet_zero (C A : ℝ) (r : ℕ) :
    reflectionKernelJet C A r 0 = reflectionKernel C A r := by
  ext T
  simp [reflectionKernelJet, reflectionKernelJetLine, reflectionKernelJetIntegrand,
    reflectionGammaJet, reflectionKernel, reflectionInverseMellinLine,
    reflectionInverseMellinIntegrand]

theorem reflectionKernelJet_eq_line (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) (σ : ℝ) :
    reflectionKernelJet C A r j T = reflectionKernelJetLine C A r j σ T :=
  reflectionKernelJetLine_independent C hA hT r j 0 σ

theorem reflectionKernelJet_power_bound (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (σ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionKernelJet C A r j T‖ ≤ M * T ^ σ := by
  let M : ℝ := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖reflectionGammaJet C A r j ((σ : ℂ) + y * I)‖
  refine ⟨M, mul_nonneg (by positivity) (integral_nonneg (fun y => norm_nonneg _)),
    fun T hT => ?_⟩
  rw [reflectionKernelJet_eq_line C hA hT r j σ, reflectionKernelJetLine, norm_mul,
    Complex.norm_of_nonneg (by positivity : 0 ≤ (1 / (2 * Real.pi) : ℝ))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ,
        ‖reflectionKernelJetIntegrand C A r j T ((σ : ℂ) + y * I)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = M * T ^ σ := by
      simp only [reflectionKernelJetIntegrand_norm C A r j hT, add_re, ofReal_re,
        mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
      rw [integral_const_mul]
      dsimp [M]; ring

theorem reflectionKernelJet_endpoint_bound (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (N : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionKernelJet C A r j T‖ ≤ M * min (T ^ N) (T ^ (-N)) := by
  obtain ⟨M₁, hM₁, hb₁⟩ := reflectionKernelJet_power_bound C hA r j N
  obtain ⟨M₂, hM₂, hb₂⟩ := reflectionKernelJet_power_bound C hA r j (-N)
  refine ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _), fun T hT => ?_⟩
  rw [mul_min_of_nonneg _ _ (le_trans hM₁ (le_max_left _ _))]
  exact le_min ((hb₁ T hT).trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Real.rpow_nonneg hT.le _)))
    ((hb₂ T hT).trans (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hT.le _)))

theorem reflectionKernelJetLine_fourier (C A : ℝ) (r j : ℕ) (σ : ℝ)
    {T : ℝ} (hT : 0 < T) :
    reflectionKernelJetLine C A r j σ T = (T : ℂ) ^ (σ : ℂ) *
      𝓕⁻ (fun y : ℝ => reflectionGammaJet C A r j ((σ : ℂ) + (2 * Real.pi * y) * I))
        (Real.log T) := by
  have heq : reflectionKernelJetLine C A r j σ T =
      mellinInv σ (reflectionGammaJet C A r j) T⁻¹ := by
    rw [reflectionKernelJetLine, mellinInv]
    simp only [Complex.real_smul, smul_eq_mul]
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro y
    unfold reflectionKernelJetIntegrand
    dsimp only
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hT.le, Complex.cpow_neg, inv_inv]
  rw [heq, mellinInv_eq_fourierInv σ _ (inv_pos.mpr hT), Real.log_inv, neg_neg,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hT.le, Complex.cpow_neg, inv_inv]
  simp only [smul_eq_mul]

end
end SimultaneousPrimitiveRoots

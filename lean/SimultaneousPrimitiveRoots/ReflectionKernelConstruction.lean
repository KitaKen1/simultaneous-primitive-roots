module

public import SimultaneousPrimitiveRoots.ReflectionInverseMellinLine
public import SimultaneousPrimitiveRoots.PositiveMultiplicativeMeasure
public import PNTAnd.ResidueCalcOnRectangles
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Filter
open scoped Topology FourierTransform
noncomputable section

theorem reflectionGaussian_tendsto :
    Tendsto (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2))
  simpa only [Function.comp_def, neg_mul] using h

theorem reflectionHorizontal_norm_le {f : ℂ → ℂ} {l u B : ℝ} (hlu : l ≤ u)
    (hb : ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖f z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2)) (y : ℝ) :
    ‖PNTAnd.HIntegral f l u y‖ ≤
      (B * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) * |u - l| := by
  unfold PNTAnd.HIntegral
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hxoc : x ∈ Ioc l u := by simpa only [uIoc_of_le hlu] using hx
  have hx' : x ∈ Icc l u := ⟨hxoc.1.le, hxoc.2⟩
  simpa using hb ((x : ℂ) + y * I) (by simpa using hx'.1) (by simpa using hx'.2)

theorem reflectionHorizontal_tendsto {f : ℂ → ℂ} {l u B : ℝ} (hlu : l ≤ u)
    (hb : ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖f z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2)) :
    Tendsto (fun y : ℝ => PNTAnd.HIntegral f l u y) atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => PNTAnd.HIntegral f l u (-y)) atTop (𝓝 0) := by
  have hm : Tendsto (fun y : ℝ =>
      (B * Real.exp (-(1 / 2 : ℝ) * y ^ 2)) * |u - l|) atTop (𝓝 0) := by
    simpa using (reflectionGaussian_tendsto.const_mul B).mul_const |u - l|
  constructor
  · exact squeeze_zero_norm (fun y => reflectionHorizontal_norm_le hlu hb y) hm
  · apply squeeze_zero_norm _ hm
    intro y
    simpa only [neg_sq] using reflectionHorizontal_norm_le hlu hb (-y)

/-- The finite rectangular identity and actual improper limits give line
independence. No infinite contour-shifting identity is assumed. -/
theorem reflectionVertical_integral_eq {f : ℂ → ℂ} {l u B : ℝ} (hlu : l ≤ u)
    (hf : Differentiable ℂ f)
    (hb : ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖f z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2))
    (hl : Integrable (fun y : ℝ => f ((l : ℂ) + y * I)))
    (hu : Integrable (fun y : ℝ => f ((u : ℂ) + y * I))) :
    (∫ y : ℝ, f ((l : ℂ) + y * I)) = ∫ y : ℝ, f ((u : ℂ) + y * I) := by
  obtain ⟨hH, hHneg⟩ := reflectionHorizontal_tendsto hlu hb
  have hVl := intervalIntegral_tendsto_integral hl tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
  have hVu := intervalIntegral_tendsto_integral hu tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
  have hrect (Y : ℝ) : PNTAnd.HIntegral f l u (-Y) - PNTAnd.HIntegral f l u Y +
      I * (∫ y : ℝ in -Y..Y, f ((u : ℂ) + y * I)) -
      I * (∫ y : ℝ in -Y..Y, f ((l : ℂ) + y * I)) = 0 := by
    have hr := PNTAnd.HolomorphicOn.vanishesOnRectangle (U := univ)
      (z := (l : ℂ) - Y * I) (w := (u : ℂ) + Y * I)
      hf.differentiableOn (fun _ _ => mem_univ _)
    simpa [PNTAnd.RectangleIntegral, PNTAnd.VIntegral, smul_eq_mul] using hr
  have hlim : Tendsto (fun Y : ℝ =>
      PNTAnd.HIntegral f l u (-Y) - PNTAnd.HIntegral f l u Y +
      I * (∫ y : ℝ in -Y..Y, f ((u : ℂ) + y * I)) -
      I * (∫ y : ℝ in -Y..Y, f ((l : ℂ) + y * I))) atTop
      (𝓝 ((0 - 0) + I * (∫ y : ℝ, f ((u : ℂ) + y * I)) -
        I * (∫ y : ℝ, f ((l : ℂ) + y * I)))) :=
    ((hHneg.sub hH).add (hVu.const_mul I)).sub (hVl.const_mul I)
  have heqfun : (fun Y : ℝ =>
      PNTAnd.HIntegral f l u (-Y) - PNTAnd.HIntegral f l u Y +
      I * (∫ y : ℝ in -Y..Y, f ((u : ℂ) + y * I)) -
      I * (∫ y : ℝ in -Y..Y, f ((l : ℂ) + y * I))) = fun _ => 0 := funext hrect
  rw [heqfun] at hlim
  have heq := tendsto_nhds_unique hlim
    (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
  have hzero : I * ((∫ y : ℝ, f ((u : ℂ) + y * I)) -
      ∫ y : ℝ, f ((l : ℂ) + y * I)) = 0 := by
    simpa only [sub_self, zero_add, mul_sub] using heq
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left I_ne_zero)).symm

theorem reflectionInverseMellinLine_independent (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r : ℕ) (σ τ : ℝ) :
    reflectionInverseMellinLine C A r σ T = reflectionInverseMellinLine C A r τ T := by
  have heq : ∀ l u : ℝ, l ≤ u →
      reflectionInverseMellinLine C A r l T = reflectionInverseMellinLine C A r u T := by
    intro l u hlu
    obtain ⟨B, _, hb⟩ := reflectionInverseMellinIntegrand_strip_gaussian C hA hT r l u
    unfold reflectionInverseMellinLine
    rw [reflectionVertical_integral_eq hlu
      (reflectionInverseMellinIntegrand_entire C hA hT r) hb
      (reflectionInverseMellinIntegrand_integrable C hA hT r l)
      (reflectionInverseMellinIntegrand_integrable C hA hT r u)]
  rcases le_total σ τ with h | h
  · exact heq σ τ h
  · exact (heq τ σ h).symm

/-- Fixing the line at zero now gives one constructed kernel; equality to
every other line has been proved rather than hidden in this definition. -/
def reflectionKernel (C A : ℝ) (r : ℕ) (T : ℝ) : ℂ :=
  reflectionInverseMellinLine C A r 0 T

theorem reflectionKernel_eq_line (C : ℝ) {A T : ℝ} (hA : 0 < A) (hT : 0 < T)
    (r : ℕ) (σ : ℝ) :
    reflectionKernel C A r T = reflectionInverseMellinLine C A r σ T :=
  reflectionInverseMellinLine_independent C hA hT r 0 σ

theorem reflectionKernel_power_bound (C : ℝ) {A : ℝ} (hA : 0 < A) (r : ℕ) (σ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionKernel C A r T‖ ≤ M * T ^ σ := by
  obtain ⟨M, hM, hb⟩ := reflectionInverseMellinLine_bound C hA r σ
  exact ⟨M, hM, fun T hT => by rw [reflectionKernel_eq_line C hA hT r σ]; exact hb T hT⟩

theorem reflectionKernel_endpoint_bound (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (N : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionKernel C A r T‖ ≤ M * min (T ^ N) (T ^ (-N)) := by
  obtain ⟨M₁, hM₁, hb₁⟩ := reflectionKernel_power_bound C hA r N
  obtain ⟨M₂, hM₂, hb₂⟩ := reflectionKernel_power_bound C hA r (-N)
  refine ⟨max M₁ M₂, le_trans hM₁ (le_max_left _ _), fun T hT => ?_⟩
  rw [mul_min_of_nonneg _ _ (le_trans hM₁ (le_max_left _ _))]
  exact le_min ((hb₁ T hT).trans (mul_le_mul_of_nonneg_right
    (le_max_left _ _) (Real.rpow_nonneg hT.le _)))
    ((hb₂ T hT).trans (mul_le_mul_of_nonneg_right
      (le_max_right _ _) (Real.rpow_nonneg hT.le _)))

theorem reflectionGammaQuotient_fourierLine_integrable (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r : ℕ) (σ : ℝ) :
    Integrable (fun y : ℝ => reflectionGammaQuotient C A r
      ((σ : ℂ) + (2 * Real.pi * y) * I)) := by
  simpa only [ofReal_mul, ofReal_ofNat] using
    (reflectionGammaQuotient_integrable_line C hA r σ).comp_mul_left'
      (by positivity : (2 * Real.pi : ℝ) ≠ 0)

theorem reflectionKernel_continuousOn (C : ℝ) {A : ℝ} (hA : 0 < A) (r : ℕ) :
    ContinuousOn (reflectionKernel C A r) (Ioi 0) := by
  let f : ℝ → ℂ := fun y => reflectionGammaQuotient C A r ((0 : ℂ) + (2 * Real.pi * y) * I)
  have hf : Integrable f := reflectionGammaQuotient_fourierLine_integrable C hA r 0
  have hF : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  have hi : Continuous (𝓕⁻ f) := by
    change Continuous (fun x : ℝ => 𝓕⁻ f x)
    simp only [Real.fourierInv_eq_fourier_neg]
    exact hF.comp continuous_neg
  have hc : ContinuousOn (fun T : ℝ => 𝓕⁻ f (Real.log T)) (Ioi 0) :=
    hi.continuousOn.comp (Real.continuousOn_log.mono (fun _ hT => ne_of_gt hT))
      (fun _ _ => mem_univ _)
  apply hc.congr
  intro T hT
  rw [reflectionKernel, reflectionInverseMellinLine_fourier C A r 0 hT,
    Complex.ofReal_zero, Complex.cpow_zero, one_mul]

theorem reflectionKernel_decay (C : ℝ) {A : ℝ} (hA : 0 < A) (r : ℕ) :
    ReflectionKernelDecay (reflectionKernel C A r) :=
  ⟨reflectionKernel_continuousOn C hA r, fun N _ => reflectionKernel_endpoint_bound C hA r N⟩

theorem reflectionKernel_moment_integrable (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (σ : ℝ) :
    Integrable (fun T => T ^ σ * ‖reflectionKernel C A r T‖)
      artinPositiveMultiplicativeMeasure :=
  reflectionKernelDecay_moment_integrable (reflectionKernel_decay C hA r) σ

end
end SimultaneousPrimitiveRoots

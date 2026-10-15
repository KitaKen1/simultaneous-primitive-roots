module

public import SimultaneousPrimitiveRoots.ReflectionKernelJets
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Filter
open scoped Topology FourierTransform ContDiff
noncomputable section

def reflectionGammaJetFourierLine (C A : ℝ) (r j : ℕ) (y : ℝ) : ℂ :=
  reflectionGammaJet C A r j ((2 * Real.pi * y) * I)

theorem reflectionGammaJetFourierLine_moment_integrable (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r j n : ℕ) :
    Integrable (fun y : ℝ => ‖y‖ ^ n * ‖reflectionGammaJetFourierLine C A r j y‖) := by
  obtain ⟨B, _, hb⟩ := reflectionGammaJet_strip_gaussian C hA r j 0 0
  have hbound (y : ℝ) : ‖reflectionGammaJetFourierLine C A r j y‖ ≤
      B * Real.exp (-(2 * Real.pi ^ 2) * y ^ 2) := by
    have h := hb ((2 * Real.pi * y) * I) (by simp) (by simp)
    have him : ((2 * Real.pi * y : ℂ) * I).im = 2 * Real.pi * y := by simp
    rw [him, show -(1 / 2 : ℝ) * (2 * Real.pi * y) ^ 2 =
      -(2 * Real.pi ^ 2) * y ^ 2 by ring] at h
    exact h
  have hg : Integrable (fun y : ℝ => y ^ n * Real.exp (-(2 * Real.pi ^ 2) * y ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq
      (b := 2 * Real.pi ^ 2) (by positivity) (s := (n : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc : Continuous (reflectionGammaJetFourierLine C A r j) :=
    (reflectionGammaJet_entire C hA r j).continuous.comp (by fun_prop)
  apply (hg.norm.const_mul B).mono' (by fun_prop)
  apply ae_of_all
  intro y
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ‖y‖ ^ n * (B * Real.exp (-(2 * Real.pi ^ 2) * y ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound y) (by positivity)
    _ = _ := by rw [norm_mul, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le]; ring

theorem reflectionGammaJetFourierLine_power_integrable (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r j n : ℕ) :
    Integrable (fun y : ℝ => y ^ n • reflectionGammaJetFourierLine C A r j y) := by
  have hc : Continuous (reflectionGammaJetFourierLine C A r j) :=
    (reflectionGammaJet_entire C hA r j).continuous.comp (by fun_prop)
  apply (reflectionGammaJetFourierLine_moment_integrable C hA r j n).mono'
    (by fun_prop)
  exact ae_of_all _ (fun y => by simp)

theorem reflectionKernelJet_fourier (C A : ℝ) (r j : ℕ) {T : ℝ} (hT : 0 < T) :
    reflectionKernelJet C A r j T =
      𝓕⁻ (reflectionGammaJetFourierLine C A r j) (Real.log T) := by
  rw [reflectionKernelJet, reflectionKernelJetLine_fourier C A r j 0 hT]
  simp only [Complex.ofReal_zero, Complex.cpow_zero, one_mul, zero_add]
  rfl

theorem reflectionKernelJet_contDiffOn (C : ℝ) {A : ℝ} (hA : 0 < A) (r j : ℕ) :
    ContDiffOn ℝ ∞ (reflectionKernelJet C A r j) (Ioi 0) := by
  have hF : ContDiff ℝ ∞ (𝓕 (reflectionGammaJetFourierLine C A r j)) :=
    Real.contDiff_fourier (N := ⊤)
      (fun n _ => reflectionGammaJetFourierLine_moment_integrable C hA r j n)
  have hi : ContDiff ℝ ∞ (fun u : ℝ => 𝓕⁻ (reflectionGammaJetFourierLine C A r j) u) := by
    simp only [Real.fourierInv_eq_fourier_neg]
    exact hF.comp contDiff_neg
  have hc := hi.contDiffOn.comp
    (Real.contDiffOn_log.mono (fun _ hT => ne_of_gt hT)) (fun _ _ => mem_univ _)
  apply hc.congr
  intro T hT
  exact reflectionKernelJet_fourier C A r j hT

theorem reflectionKernel_contDiffOn (C : ℝ) {A : ℝ} (hA : 0 < A) (r : ℕ) :
    ContDiffOn ℝ ∞ (reflectionKernel C A r) (Ioi 0) := by
  rw [← reflectionKernelJet_zero C A r]
  exact reflectionKernelJet_contDiffOn C hA r 0

theorem reflectionKernelJet_decay (C : ℝ) {A : ℝ} (hA : 0 < A) (r j : ℕ) :
    ReflectionKernelDecay (reflectionKernelJet C A r j) :=
  ⟨(reflectionKernelJet_contDiffOn C hA r j).continuousOn,
    fun N _ => reflectionKernelJet_endpoint_bound C hA r j N⟩

theorem reflectionKernelJet_moment_integrable (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (σ : ℝ) :
    Integrable (fun T => T ^ σ * ‖reflectionKernelJet C A r j T‖)
      artinPositiveMultiplicativeMeasure :=
  reflectionKernelDecay_moment_integrable (reflectionKernelJet_decay C hA r j) σ

theorem reflectionGammaJetFourierLine_succ (C A : ℝ) (r j : ℕ) (y : ℝ) :
    reflectionGammaJetFourierLine C A r (j + 1) y =
      (2 * Real.pi * I * y) * reflectionGammaJetFourierLine C A r j y := by
  simp only [reflectionGammaJetFourierLine, reflectionGammaJet, pow_succ]
  ring

theorem reflectionKernelJet_fourierInv_hasDerivAt (C : ℝ) {A : ℝ}
    (hA : 0 < A) (r j : ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => 𝓕⁻ (reflectionGammaJetFourierLine C A r j) v)
      (𝓕⁻ (reflectionGammaJetFourierLine C A r (j + 1)) u) u := by
  have hf : Integrable (reflectionGammaJetFourierLine C A r j) := by
    simpa using reflectionGammaJetFourierLine_power_integrable C hA r j 0
  have hf' : Integrable (fun y : ℝ => y • reflectionGammaJetFourierLine C A r j y) := by
    simpa using reflectionGammaJetFourierLine_power_integrable C hA r j 1
  have h := Real.hasDerivAt_fourier hf hf' (-u)
  have heq : (fun y : ℝ => (-2 * Real.pi * I * y) • reflectionGammaJetFourierLine C A r j y) =
      -(reflectionGammaJetFourierLine C A r (j + 1)) := by
    ext y
    rw [Pi.neg_apply, reflectionGammaJetFourierLine_succ]
    simp only [smul_eq_mul]
    ring
  have hneg : 𝓕 (-reflectionGammaJetFourierLine C A r (j + 1)) (-u) =
      -(𝓕 (reflectionGammaJetFourierLine C A r (j + 1)) (-u)) := by
    simp only [Real.fourier_eq, Pi.neg_apply, smul_neg, integral_neg]
  rw [heq, hneg] at h
  have hi := h.scomp u (hasDerivAt_id u).neg
  simpa only [Function.comp_def, Real.fourierInv_eq_fourier_neg, Pi.neg_apply,
    neg_smul, one_smul, neg_neg] using hi

theorem reflectionKernelJet_hasDerivAt (C : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) (r j : ℕ) :
    HasDerivAt (reflectionKernelJet C A r j)
      ((T⁻¹ : ℝ) • reflectionKernelJet C A r (j + 1) T) T := by
  have h := (reflectionKernelJet_fourierInv_hasDerivAt C hA r j (Real.log T)).scomp T
    (Real.hasDerivAt_log hT.ne')
  rw [← reflectionKernelJet_fourier C A r (j + 1) hT] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with t ht
  exact reflectionKernelJet_fourier C A r j ht

def reflectionEulerDeriv (f : ℝ → ℂ) (T : ℝ) : ℂ := (T : ℂ) * deriv f T

def reflectionEulerIterate : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, f => f
  | j + 1, f => reflectionEulerDeriv (reflectionEulerIterate j f)

/-- The polynomial-weighted contour integrals are the actual iterates of
T*d/dT, proved by differentiation rather than defined to be those iterates. -/
theorem reflectionKernel_eulerIterate_eq (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) {T : ℝ} (hT : 0 < T) :
    reflectionEulerIterate j (reflectionKernel C A r) T = reflectionKernelJet C A r j T := by
  induction j generalizing T with
  | zero => simp [reflectionEulerIterate, reflectionKernelJet_zero]
  | succ j ih =>
    have heq : reflectionEulerIterate j (reflectionKernel C A r) =ᶠ[𝓝 T]
        reflectionKernelJet C A r j := by
      filter_upwards [eventually_gt_nhds hT] with t ht
      exact ih ht
    have hd := (reflectionKernelJet_hasDerivAt C hA hT r j).congr_of_eventuallyEq heq
    rw [reflectionEulerIterate, reflectionEulerDeriv, hd.deriv]
    simp only [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hT.ne'), one_mul]

theorem reflectionKernel_eulerIterate_endpoint_bound (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r j : ℕ) (N : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖reflectionEulerIterate j (reflectionKernel C A r) T‖ ≤ M * min (T ^ N) (T ^ (-N)) := by
  obtain ⟨M, hM, hb⟩ := reflectionKernelJet_endpoint_bound C hA r j N
  exact ⟨M, hM, fun T hT => by rw [reflectionKernel_eulerIterate_eq C hA r j hT]; exact hb T hT⟩

theorem reflectionKernel_eulerIterate_contDiffOn (C : ℝ) {A : ℝ} (hA : 0 < A) (r j : ℕ) :
    ContDiffOn ℝ ∞ (reflectionEulerIterate j (reflectionKernel C A r)) (Ioi 0) := by
  apply (reflectionKernelJet_contDiffOn C hA r j).congr
  intro T hT
  exact reflectionKernel_eulerIterate_eq C hA r j hT

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.MellinProbeContinuation
public import Mathlib.Analysis.MellinInversion

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Asymptotics Set Complex
open scoped Topology FourierTransform
noncomputable section

def probeLogPullback (f : ℝ → ℂ) (β σ u : ℝ) : ℂ :=
  (Real.exp ((σ - β) * u) : ℂ) * f (Real.exp (-u))

/-- Actual Mellin integrability gives actual integrability after logarithmic
change of variables. No integral is assigned a value before convergence. -/
theorem mellinConvergent_integrable_logPullback {f : ℝ → ℂ} {r : ℝ}
    (hf : MellinConvergent f (r : ℂ)) :
    Integrable (fun u : ℝ => (Real.exp (-r * u) : ℂ) * f (Real.exp (-u))) := by
  have hd : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) univ u := by
    intro u _
    exact mul_neg_one (Real.exp (-u)) ▸
      ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt
  have him : (Real.exp ∘ Neg.neg) '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : InjOn (Real.exp ∘ Neg.neg) (univ : Set ℝ) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← him,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj] at hf
  have hid (u : ℝ) :
      |-Real.exp (-u)| • ((Real.exp (-u) : ℂ) ^ ((r : ℂ) - 1) • f (Real.exp (-u))) =
        (Real.exp (-r * u) : ℂ) * f (Real.exp (-u)) := by
    rw [abs_neg, Real.abs_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    simp only [smul_eq_mul, real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_mul, ← Real.exp_add]
    rw [show -u + -u * (r - 1) = -r * u by ring]
  simpa only [Function.comp_apply, hid, integrableOn_univ] using hf

theorem probeLogPullback_integrable {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) (hσ : α + β < σ) :
    Integrable (probeLogPullback f β σ) := by
  have hc := probeMellinTransform_convergent hf (s := (σ : ℂ)) (by simpa using hσ)
  have hc' : MellinConvergent f ((β - σ : ℝ) : ℂ) := by simpa using hc
  change Integrable (fun u : ℝ => (Real.exp ((σ - β) * u) : ℂ) * f (Real.exp (-u)))
  simpa only [neg_sub] using mellinConvergent_integrable_logPullback hc'

theorem probeMellinTransform_vertical_eq_fourierInv (f : ℝ → ℂ) (β σ τ : ℝ) :
    probeMellinTransform f β ((σ : ℂ) + τ * I) =
      𝓕⁻ (probeLogPullback f β σ) (τ / (2 * Real.pi)) := by
  rw [probeMellinTransform, mellin_eq_fourier, Real.fourierInv_eq_fourier_neg]
  simp only [sub_re, ofReal_re, add_re, mul_re, I_re, ofReal_im,
    I_im, mul_zero, sub_zero, add_zero, sub_im, add_im,
    mul_im, mul_one, zero_add, zero_sub, neg_div]
  have heq : (fun u : ℝ => Real.exp (-(β - σ) * u) • f (Real.exp (-u))) =
      probeLogPullback f β σ := by
    funext u
    simp only [probeLogPullback, neg_sub, real_smul]
  rw [heq]

/-- Fourier inversion identifies the actual convergent Mellin transform on
the original vertical line. Integrability of the Fourier transform follows
from the probe estimates, rather than being a further input. -/
theorem probeMellinTransform_eq_on_vertical {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) (hσ : α + β < σ) {A : ℂ → ℂ}
    (hcont : Continuous (fun y : ℝ => A ((σ : ℂ) + (2 * Real.pi * y) * I)))
    (hA : Integrable (fun y : ℝ => A ((σ : ℂ) + (2 * Real.pi * y) * I)))
    (hrep : ∀ u : ℝ, probeLogPullback f β σ u =
      𝓕 (fun y : ℝ => A ((σ : ℂ) + (2 * Real.pi * y) * I)) u)
    (τ : ℝ) : probeMellinTransform f β ((σ : ℂ) + τ * I) =
      A ((σ : ℂ) + τ * I) := by
  have heq := funext hrep
  have hFA : Integrable (𝓕 (fun y : ℝ => A ((σ : ℂ) + (2 * Real.pi * y) * I))) := by
    rw [← heq]
    exact probeLogPullback_integrable hf hσ
  rw [probeMellinTransform_vertical_eq_fourierInv, heq,
    hA.fourierInv_fourier_eq hFA hcont.continuousAt]
  congr 1
  push_cast
  field_simp

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.MellinProbeFourier
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Asymptotics Set Complex Metric
open scoped Topology FourierTransform
noncomputable section

/-- Agreement on a single vertical line is enough: that line has a punctured
accumulation point inside the domain of holomorphy. -/
theorem analyticOnNhd_eqOn_of_vertical {c σ : ℝ} (hσ : c < σ) {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {s : ℂ | c < s.re})
    (hG : AnalyticOnNhd ℂ G {s : ℂ | c < s.re})
    (heq : ∀ τ : ℝ, F ((σ : ℂ) + τ * I) = G ((σ : ℂ) + τ * I)) :
    EqOn F G {s : ℂ | c < s.re} := by
  apply hF.eqOn_of_preconnected_of_mem_closure hG
    (convex_halfSpace_re_gt c).isPreconnected
    (z₀ := (σ : ℂ)) (by simpa using hσ)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  refine ⟨(σ : ℂ) + (ε / 2 : ℝ) * I, ⟨heq (ε / 2), ?_⟩, ?_⟩
  · simp only [mem_singleton_iff, add_eq_left, mul_eq_zero, ofReal_eq_zero,
      I_ne_zero, or_false]
    exact ne_of_gt (half_pos hε)
  · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I,
      norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε), mul_one]
    linarith

theorem nonvanishing_of_mellin_probe_vertical {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) (hσ : α + β < σ) {L N : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | α + β < s.re})
    (hne : ∀ s : ℂ, α + β < s.re → N s ≠ 0)
    (heq : ∀ τ : ℝ, probeMellinTransform f β ((σ : ℂ) + τ * I) *
      L ((σ : ℂ) + τ * I) = N ((σ : ℂ) + τ * I))
    {s : ℂ} (hs : α + β < s.re) : L s ≠ 0 := by
  have hid := analyticOnNhd_eqOn_of_vertical hσ
    ((probeMellinTransform_analyticOnNhd hf).mul hL) hN heq
  have hid' : probeMellinTransform f β s * L s = N s := hid hs
  intro hz
  rw [hz, mul_zero] at hid'
  exact hne s hs hid'.symm

/-- The final zero detection step, using a Fourier representation of the
actual probe and the actual reciprocal N/L on the original line. -/
theorem nonvanishing_of_fourier_probe {f : ℝ → ℂ} {α β σ : ℝ}
    (hf : MellinProbeBounds f α) (hσ : α + β < σ) {L N : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hN : AnalyticOnNhd ℂ N {s : ℂ | α + β < s.re})
    (hne : ∀ s : ℂ, α + β < s.re → N s ≠ 0)
    (hline : ∀ τ : ℝ, L ((σ : ℂ) + τ * I) ≠ 0)
    (hcont : Continuous (fun y : ℝ =>
      N ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)))
    (hA : Integrable (fun y : ℝ =>
      N ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)))
    (hrep : ∀ u : ℝ, probeLogPullback f β σ u =
      𝓕 (fun y : ℝ =>
        N ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)) u)
    {s : ℂ} (hs : α + β < s.re) : L s ≠ 0 := by
  apply nonvanishing_of_mellin_probe_vertical hf hσ hL hN hne (s := s) (hs := hs)
  intro τ
  rw [probeMellinTransform_eq_on_vertical (A := fun z => N z / L z) hf hσ hcont hA hrep τ]
  exact div_mul_cancel₀ _ (hline τ)

/-- Gaussian factors cannot cancel a zero of the denominator. -/
theorem gaussian_probe_numerator_ne_zero {H : ℂ → ℂ} {s c : ℂ}
    (hH : H s ≠ 0) : Complex.exp ((s - c) ^ 2) * H s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) hH

/-- The numerical saving of the final Mellin step is absolute. -/
theorem researchProbe_halfplane :
    (7 / 15 - 1 / 20000 : ℝ) + 8 / 15 = 1 - 1 / 20000 := by norm_num

theorem researchProbe_contains_target_strip {s : ℂ} (hs : 1 - (1 / 1000000 : ℝ) < s.re) :
    (7 / 15 - 1 / 20000 : ℝ) + 8 / 15 < s.re := by
  rw [researchProbe_halfplane]
  linarith

end
end SimultaneousPrimitiveRoots

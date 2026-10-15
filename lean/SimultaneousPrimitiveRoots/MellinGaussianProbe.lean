module

public import SimultaneousPrimitiveRoots.MellinProbeNonvanishing
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Asymptotics Set Complex
open scoped Topology FourierTransform
noncomputable section

def gaussianProbeNumerator (H : ℂ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - (c : ℂ)) ^ 2) * H s

theorem gaussianProbeNumerator_analyticOnNhd {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) (c : ℝ) :
    AnalyticOnNhd ℂ (gaussianProbeNumerator H c) U :=
  (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp).mul hH

theorem gaussianProbeLine_norm (σ c τ : ℝ) :
    ‖Complex.exp ((((σ : ℂ) + τ * I) - (c : ℂ)) ^ 2)‖ =
      Real.exp ((σ - c) ^ 2) * Real.exp (-τ ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [sq, mul_re, sub_re, add_re, ofReal_re, I_re, ofReal_im,
    I_im, mul_zero, sub_zero, add_zero, sub_im, add_im, mul_im,
    mul_one, zero_add]
  ring

theorem gaussianProbeReciprocal_continuous_on_line {H L : ℂ → ℂ} {d σ : ℝ}
    (hσ : d < σ) (hH : AnalyticOnNhd ℂ H {s : ℂ | d < s.re})
    (hL : AnalyticOnNhd ℂ L {s : ℂ | d < s.re})
    (hline : ∀ τ : ℝ, L ((σ : ℂ) + τ * I) ≠ 0) (c : ℝ) :
    Continuous (fun y : ℝ => gaussianProbeNumerator H c
      ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hs : ((σ : ℂ) + (2 * Real.pi * y) * I) ∈ {s : ℂ | d < s.re} := by
    simpa using hσ
  have hn : L ((σ : ℂ) + (2 * Real.pi * y) * I) ≠ 0 := by
    simpa only [ofReal_mul, ofReal_ofNat] using hline (2 * Real.pi * y)
  exact (((gaussianProbeNumerator_analyticOnNhd hH c) _ hs).continuousAt.div
    (hL _ hs).continuousAt hn).comp
      (f := fun v : ℝ => (σ : ℂ) + (2 * Real.pi * v) * I)
      (show ContinuousAt (fun v : ℝ => (σ : ℂ) + (2 * Real.pi * v) * I) y by fun_prop)

/-- The actual reciprocal on the convergence line is Gaussian integrable
as soon as its unweighted factor H/L is bounded. -/
theorem gaussianProbeReciprocal_integrable_on_line {H L : ℂ → ℂ} {d σ M : ℝ}
    (hσ : d < σ) (hH : AnalyticOnNhd ℂ H {s : ℂ | d < s.re})
    (hL : AnalyticOnNhd ℂ L {s : ℂ | d < s.re})
    (hline : ∀ τ : ℝ, L ((σ : ℂ) + τ * I) ≠ 0)
    (hbound : ∀ τ : ℝ, ‖H ((σ : ℂ) + τ * I) / L ((σ : ℂ) + τ * I)‖ ≤ M)
    (c : ℝ) : Integrable (fun y : ℝ => gaussianProbeNumerator H c
      ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)) := by
  have hmaj := (integrable_exp_neg_mul_sq
    (b := (2 * Real.pi) ^ 2) (by positivity)).const_mul (Real.exp ((σ - c) ^ 2) * M)
  have hcont := gaussianProbeReciprocal_continuous_on_line hσ hH hL hline c
  have hmeas := hcont.aestronglyMeasurable (μ := volume)
  apply hmaj.mono' hmeas
  apply ae_of_all
  intro y
  have hnorm : ‖Complex.exp ((((σ : ℂ) + (2 * Real.pi * y) * I) - (c : ℂ)) ^ 2)‖ =
      Real.exp ((σ - c) ^ 2) * Real.exp (-(2 * Real.pi * y) ^ 2) := by
    simpa only [ofReal_mul, ofReal_ofNat] using gaussianProbeLine_norm σ c (2 * Real.pi * y)
  have hby : ‖H ((σ : ℂ) + (2 * Real.pi * y) * I) /
      L ((σ : ℂ) + (2 * Real.pi * y) * I)‖ ≤ M := by
    simpa only [ofReal_mul, ofReal_ofNat] using hbound (2 * Real.pi * y)
  rw [gaussianProbeNumerator, mul_div_assoc, norm_mul, hnorm]
  calc
    _ ≤ (Real.exp ((σ - c) ^ 2) * Real.exp (-(2 * Real.pi * y) ^ 2)) * M :=
      mul_le_mul_of_nonneg_left hby (by positivity)
    _ = (Real.exp ((σ - c) ^ 2) * M) * Real.exp (-(2 * Real.pi) ^ 2 * y ^ 2) := by
      rw [mul_pow]
      ring_nf

/-- Gaussian Fourier probe endpoint bounds force zero exclusion. The proof
constructs the Mellin continuation and verifies both Fourier integrability
conditions; it does not assume the desired zero-free strip. -/
theorem nonvanishing_of_gaussian_fourier_probe {f : ℝ → ℂ} {α β σ M c : ℝ}
    (hf : MellinProbeBounds f α) (hσ : α + β < σ) {L H : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | α + β < s.re})
    (hne : ∀ s : ℂ, α + β < s.re → H s ≠ 0)
    (hline : ∀ τ : ℝ, L ((σ : ℂ) + τ * I) ≠ 0)
    (hbound : ∀ τ : ℝ, ‖H ((σ : ℂ) + τ * I) / L ((σ : ℂ) + τ * I)‖ ≤ M)
    (hrep : ∀ u : ℝ, probeLogPullback f β σ u =
      𝓕 (fun y : ℝ => gaussianProbeNumerator H c
        ((σ : ℂ) + (2 * Real.pi * y) * I) / L ((σ : ℂ) + (2 * Real.pi * y) * I)) u)
    {s : ℂ} (hs : α + β < s.re) : L s ≠ 0 := by
  exact nonvanishing_of_fourier_probe hf hσ hL
    (gaussianProbeNumerator_analyticOnNhd hH c)
    (fun z hz => gaussian_probe_numerator_ne_zero (hne z hz)) hline
    (gaussianProbeReciprocal_continuous_on_line hσ hH hL hline c)
    (gaussianProbeReciprocal_integrable_on_line hσ hH hL hline hbound c) hrep hs

end
end SimultaneousPrimitiveRoots

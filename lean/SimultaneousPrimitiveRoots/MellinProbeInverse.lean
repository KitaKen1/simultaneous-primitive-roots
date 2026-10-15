module

public import SimultaneousPrimitiveRoots.MellinGaussianProbe

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Asymptotics Set Complex
open scoped Topology FourierTransform
noncomputable section

/-- The actual vertical integral defining the probe: x^(-β) times the
inverse Mellin integral at 1/x. Its positive argument is essential. -/
def inverseMellinProbe (A : ℂ → ℂ) (β σ : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-(β : ℂ)) * mellinInv σ A x⁻¹

theorem inverseMellinProbe_logPullback (A : ℂ → ℂ) (β σ u : ℝ) :
    probeLogPullback (inverseMellinProbe A β σ) β σ u =
      𝓕 (fun y : ℝ => A ((σ : ℂ) + (2 * Real.pi * y) * I)) u := by
  rw [probeLogPullback, inverseMellinProbe, ← Real.exp_neg, neg_neg,
    mellinInv_eq_fourierInv σ A (Real.exp_pos u), Real.log_exp,
    Real.fourierInv_eq_fourier_neg, neg_neg]
  simp only [smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-u)).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos (-u)).le,
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Real.log_exp,
    Complex.ofReal_exp]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  have he : (((σ - β) * u : ℝ) : ℂ) +
      ((-u : ℝ) : ℂ) * -(β : ℂ) + (u : ℂ) * -(σ : ℂ) = 0 := by
    push_cast
    ring
  rw [he, Complex.exp_zero, one_mul]

/-- A direct vertical-integral definition supplies the Fourier
representation; no transform-identification assumption is left. -/
theorem nonvanishing_of_gaussian_inverseMellin_probe {α β σ M c : ℝ}
    {L H : ℂ → ℂ}
    (hf : MellinProbeBounds
      (inverseMellinProbe (fun z => gaussianProbeNumerator H c z / L z) β σ) α)
    (hσ : α + β < σ)
    (hL : AnalyticOnNhd ℂ L {s : ℂ | α + β < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | α + β < s.re})
    (hne : ∀ s : ℂ, α + β < s.re → H s ≠ 0)
    (hline : ∀ τ : ℝ, L ((σ : ℂ) + τ * I) ≠ 0)
    (hbound : ∀ τ : ℝ, ‖H ((σ : ℂ) + τ * I) / L ((σ : ℂ) + τ * I)‖ ≤ M)
    {s : ℂ} (hs : α + β < s.re) : L s ≠ 0 := by
  exact nonvanishing_of_gaussian_fourier_probe hf hσ hL hH hne hline hbound
    (inverseMellinProbe_logPullback _ β σ) hs

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.Counting
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics

/-- Absorb a signed little-o remainder in the positive main-term gap. -/
theorem positiveDyadicLowerBound_of_asymptotic_gap
    {A : Finset ℕ} {κ ε : ℝ} {r : ℝ → ℝ} (hgap : ε < κ)
    (hr : r =o[atTop] (fun x : ℝ => x / Real.log x))
    (hcount : ∀ᶠ x : ℝ in atTop,
      (κ - ε) * (x / Real.log x) + r x ≤ primeCount A x) :
    PositiveDyadicLowerBound A := by
  have hc : 0 < (κ - ε) / 2 := by linarith
  apply positiveDyadicLowerBound_of_eventually hc
  filter_upwards [hr.bound hc, hcount, eventually_ge_atTop (2 : ℝ)] with x he hb hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x / Real.log x := (div_pos hxpos hlog).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale] at he
  have hlow := (abs_le.mp he).1
  nlinarith

/-- Explicit parameter choice used to leave a positive gap after the exception bound. -/
theorem parameter_gap {θ φ C T : ℝ}
    (hθ : 0 < θ) (hφ : 0 < φ) (hT : 0 < T)
    (hlarge : 4 * C * φ ≤ θ * T) :
    C / (2 * T ^ 2 + 1) ≤ θ / (4 * φ * T) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right hlarge hT.le
  nlinarith [mul_pos hθ (sq_pos_of_pos hT)]

theorem positive_parameter_difference {θ φ C T : ℝ}
    (hθ : 0 < θ) (hφ : 0 < φ) (hT : 0 < T)
    (hlarge : 4 * C * φ ≤ θ * T) :
    C / (2 * T ^ 2 + 1) < θ / (2 * φ * T) := by
  have h := parameter_gap hθ hφ hT hlarge
  have hp : 0 < θ / (4 * φ * T) := by positivity
  have heq : θ / (2 * φ * T) = 2 * (θ / (4 * φ * T)) := by ring
  linarith

end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.KummerQuotientFiniteFormula
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter MeasureTheory
open scoped Topology
noncomputable section

/-- Exactly the two right-line tails in the finite contour remainder. -/
def gaussianRightTailRemainder (H : ℂ → ℂ) (d : ℂ) (x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    (Complex.I * (∫ y : ℝ in Set.Iic (-T),
      gaussianFullQuotientIntegrand H d x ((2 : ℂ) + y * Complex.I)) +
    Complex.I * (∫ y : ℝ in Set.Ici T,
      gaussianFullQuotientIntegrand H d x ((2 : ℂ) + y * Complex.I)))

/-- Integrability is proved for this actual quotient before invoking the tail
limit, so the statement does not rely on an undefined integral being zero. -/
theorem kummerFullQuotient_right_tails_tendsto {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x
      ((2 : ℂ) + y * Complex.I)) ∧
    Tendsto (gaussianRightTailRemainder H ((q : ℂ) - 1) x) atTop (𝓝 0) := by
  have hi := kummerFullQuotientSignedLogDerivative_integrable hH hx (σ := 2) (by norm_num)
  refine ⟨hi, ?_⟩
  have hl := tendsto_integral_Iic_zero (μ := volume)
    (f := fun y : ℝ => gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x
      ((2 : ℂ) + y * Complex.I)) tendsto_neg_atTop_atBot
  have hr := tendsto_integral_Ici_zero (μ := volume)
    (f := fun y : ℝ => gaussianFullQuotientIntegrand H ((q : ℂ) - 1) x
      ((2 : ℂ) + y * Complex.I)) (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  unfold gaussianRightTailRemainder
  simpa only [id_eq, mul_zero, add_zero] using
    (hl.const_mul Complex.I |>.add (hr.const_mul Complex.I)).const_mul
      (1 / (2 * Real.pi * Complex.I))

theorem kummerFullQuotient_right_tail_norm_eventually_le {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ‖gaussianRightTailRemainder H ((q : ℂ) - 1) x T‖ ≤ ε := by
  have hh := (kummerFullQuotient_right_tails_tendsto hH hx).2.norm
  exact Filter.Eventually.mono (hh.eventually (gt_mem_nhds (by simpa using hε)))
    (fun T hT => hT.le)

theorem gaussianFiniteContourRemainder_split_right_tails
    (H : ℂ → ℂ) (d : ℂ) (x σ T : ℝ) :
    gaussianFiniteContourRemainder H d x σ T =
      PNTAnd.VIntegral' (gaussianFullQuotientIntegrand H d x) σ (-T) T -
        PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 (-T) +
        PNTAnd.HIntegral' (gaussianFullQuotientIntegrand H d x) σ 2 T +
        gaussianRightTailRemainder H d x T := rfl

end
end SimultaneousPrimitiveRoots

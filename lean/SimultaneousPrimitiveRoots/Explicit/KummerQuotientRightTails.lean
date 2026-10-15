module

public import SimultaneousPrimitiveRoots.KummerQuotientRightTails
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientRectangle
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteFormula

/-! Generalization of `SimultaneousPrimitiveRoots.KummerQuotientRightTails` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Filter MeasureTheory
open scoped Topology
noncomputable section

/-- Integrability is proved for this actual quotient before invoking the tail
limit, so the statement does not rely on an undefined integral being zero. -/
theorem kummerFullQuotient_right_tails_tendsto {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
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
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ‖gaussianRightTailRemainder H ((q : ℂ) - 1) x T‖ ≤ ε := by
  have hh := (kummerFullQuotient_right_tails_tendsto hH hx).2.norm
  exact Filter.Eventually.mono (hh.eventually (gt_mem_nhds (by simpa using hε)))
    (fun T hT => hT.le)

end
end SimultaneousPrimitiveRoots.Explicit

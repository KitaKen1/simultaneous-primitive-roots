module

public import SimultaneousPrimitiveRoots.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity

/-! Generalization of `SimultaneousPrimitiveRoots.ZetaQuotientCenter` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField IsDedekindDomain Metric
noncomputable section
open Classical

/-- The center term is now bounded unconditionally in the field degree. The
actual entire extension and its boundary norm bound remain required inputs. -/
theorem numberFieldEntireFullQuotientContinuation_jensen_degree_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) |R|, ‖H z‖ ≤ M) :
    (((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) |r|
      then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) ≤
        (Real.log M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log (R / r) := by
  have hc := numberFieldFullQuotientContinuation_log_norm_two_lower K L
    (numberFieldEntireFullQuotientContinuation_positive K L hH)
  have hp : 0 < ‖H 2‖ := norm_pos_iff.mpr
    (numberFieldFullQuotientContinuation_ne_zero_two K L
      (numberFieldEntireFullQuotientContinuation_positive K L hH))
  have hden : 0 < Real.log (R / r) := by
    rw [← Real.log_abs]
    apply Real.log_pos
    rw [abs_div]
    exact (lt_div_iff₀ hr).mpr (by simpa using hrR)
  apply (numberFieldEntireFullQuotientContinuation_jensen_multiplicity_le K L hH hr hrR hM hb).trans
  apply div_le_div_of_nonneg_right _ hden.le
  rw [Real.log_div (by linarith : M ≠ 0) hp.ne']
  linarith

end
end SimultaneousPrimitiveRoots.Explicit

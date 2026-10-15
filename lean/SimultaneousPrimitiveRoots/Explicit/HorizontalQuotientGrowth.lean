module

public import SimultaneousPrimitiveRoots.HorizontalQuotientGrowth
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.QuotientDiskLogDerivative
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.FiniteZeroSeparation
public import SimultaneousPrimitiveRoots.Explicit.QuotientHorizontalLogDerivative

/-! Generalization of `SimultaneousPrimitiveRoots.HorizontalQuotientGrowth` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Metric Filter
open scoped Topology
noncomputable section

theorem numberFieldEntireFullQuotientContinuation_exists_horizontal_polynomial_bound
    (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
    {H : ℂ → ℂ} (hH : EntireZeroData K E H)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 ≤ N)
    (hgrowth : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp (B * (U + 3) ^ 2)) :
    ∃ T : ℝ, N < T ∧ T < N + 1 ∧
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T →
        H s ≠ 0 ∧ ‖deriv H s / H s‖ ≤
          horizontalQuotientGrowthConstant B (Module.finrank ℚ E : ℝ) * (N + 5) ^ 5 := by
  have hb : ∀ z ∈ sphere (2 : ℂ) (4 * (N + 5)),
      ‖H z‖ ≤ Real.exp (B * (2 * N + 11) ^ 2) := by
    intro z hz
    have hh := hgrowth (2 * N + 8) (by linarith) z
    have hr : 2 * (2 * N + 8 + 2) = 4 * (N + 5) := by ring
    have hm : 2 * N + 8 + 3 = 2 * N + 11 := by ring
    rw [hr, hm] at hh
    exact hh hz
  obtain ⟨T, hl, hr, hh⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_horizontal_logDeriv_bound K E hH hN
      (by positivity : 0 ≤ B * (2 * N + 11) ^ 2) hb
  refine ⟨T, hl, hr, ?_⟩
  intro s hs hs2 hi
  have ht := hh s hs hs2 hi
  exact ⟨ht.1, ht.2.trans (horizontal_logDeriv_bound_le_polynomial hN hB (Nat.cast_nonneg _))⟩

end
end SimultaneousPrimitiveRoots.Explicit

module

public import SimultaneousPrimitiveRoots.QuotientHorizontalLogDerivative
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

/-! Generalization of `SimultaneousPrimitiveRoots.QuotientHorizontalLogDerivative` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Metric Classical
noncomputable section


/-- Distinct actual zeros are bounded by the multiplicity-labelled carrier;
no zero with positive analytic order is dropped. -/
theorem numberFieldEntireFullQuotientContinuation_distinct_ball_zeros_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (D : ℝ) :
    (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
      (isCompact_closedBall (2 : ℂ) D)).toFinset.card ≤
        Nat.card (fullQuotientBallZeroIndex H D) := by
  let Z := {s : ℂ // s ∈ closedBall (2 : ℂ) D ∧ H s = 0}
  let hf := numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
    (isCompact_closedBall (2 : ℂ) D)
  let : Fintype ↥{s : ℂ | s ∈ closedBall (2 : ℂ) D ∧ H s = 0} := hf.fintype
  let : Finite (fullQuotientBallZeroIndex H D) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH D
  let f : Z → fullQuotientBallZeroIndex H D := fun s => ⟨s, ⟨0,
    (numberFieldEntireFullQuotientContinuation_multiplicity_pos_iff K L hH s).mpr s.property.2⟩⟩
  have hi : Function.Injective f := by
    intro s t heq
    exact congrArg (fun j : fullQuotientBallZeroIndex H D => j.1) heq
  rw [hf.card_toFinset, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective f hi

theorem numberFieldEntireFullQuotientContinuation_distinct_ball_zeros_jensen_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D M : ℝ} (hD : 0 < D) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M) :
    ((numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
      (isCompact_closedBall (2 : ℂ) (D / 2))).toFinset.card : ℝ) ≤
        (M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := by
  have hj := numberFieldEntireFullQuotientContinuation_jensen_degree_le K L hH
    (r := D / 2) (R := D) (by rw [abs_of_pos (by positivity)]; positivity)
    (by rw [abs_of_pos (by positivity), abs_of_pos hD]; linarith)
    (Real.one_le_exp_iff.mpr hM) (by simpa only [abs_of_pos hD] using hb)
  rw [Real.log_exp, abs_of_pos (by positivity),
    show D / (D / 2) = 2 by field_simp,
    ← numberFieldEntireFullQuotientContinuation_ball_card_eq_multiplicity_sum K L hH] at hj
  apply le_trans _ hj
  exact_mod_cast numberFieldEntireFullQuotientContinuation_distinct_ball_zeros_le K L hH (D / 2)

/-- Both actual horizontal edges acquire one common logarithmic-derivative
bound from growth on the outer disk. The chosen height depends on N and H. -/
theorem numberFieldEntireFullQuotientContinuation_exists_horizontal_logDeriv_bound
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {N M : ℝ} (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) (4 * (N + 5)), ‖H z‖ ≤ Real.exp M) :
    ∃ T : ℝ, N < T ∧ T < N + 1 ∧
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → |s.im| = T →
        H s ≠ 0 ∧ ‖deriv H s / H s‖ ≤
          (diskLogDerivativeConstant + 16 * (N + 5) *
            (1 + (M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) /
              Real.log (3 / 2)) *
            (1 + M + 4 * (Module.finrank ℚ L : ℝ)) / (4 * (N + 5)) := by
  let D : ℝ := 4 * (N + 5)
  have hD : 0 < D := by dsimp [D]; positivity
  let F := (numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
    (isCompact_closedBall (2 : ℂ) (D / 2))).toFinset
  let r : ℝ := 1 / (4 * ((F.card : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨T, hNT, hTN, hsep⟩ :=
    numberFieldEntireFullQuotientContinuation_exists_height_card_gap K L hH
      (isCompact_closedBall (2 : ℂ) (D / 2)) N
  have hc := numberFieldEntireFullQuotientContinuation_distinct_ball_zeros_jensen_le K L hH hD hM hb
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  refine ⟨T, hNT, hTN, ?_⟩
  intro s hsl hsr hi
  have hs : ‖s - 2‖ ≤ D / 4 := horizontal_strip_point_mem_quarter_disk hN hNT hTN ⟨hsl, hsr⟩ hi
  have hdist : ∀ ρ ∈ closedBall (2 : ℂ) (D / 2), H ρ = 0 → r ≤ ‖s - ρ‖ := by
    intro ρ hρ hn
    apply (hsep ρ hρ hn).trans
    simpa only [hi] using abs_height_difference_le_complex_distance s ρ
  have hn : H s ≠ 0 := by
    intro hn
    have hh := hdist s (by rw [mem_closedBall, dist_eq_norm]; linarith) hn
    exact (not_le_of_gt hr) (by simpa only [sub_self, norm_zero] using hh)
  have heq : (r / D) * D = r := div_mul_cancel₀ r hD.ne'
  have hbound := numberFieldEntireFullQuotientContinuation_logDeriv_le_of_separation K L hH
    hD hM (div_pos hr hD) hb hs (by simpa only [heq] using hdist)
  refine ⟨hn, hbound.trans ?_⟩
  apply div_le_div_of_nonneg_right _ hD.le
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ 1 + M + 4 * (Module.finrank ℚ L : ℝ))
  apply add_le_add_right _ diskLogDerivativeConstant
  have heq' : 1 / (r / D * Real.log (3 / 2)) =
      (4 * D * ((F.card : ℝ) + 1)) / Real.log (3 / 2) := by
    dsimp [r]
    field_simp
  rw [heq']
  apply div_le_div_of_nonneg_right _ hlog.le
  have hc' : (F.card : ℝ) ≤ (M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := hc
  calc 4 * D * ((F.card : ℝ) + 1)
      ≤ 4 * D * (1 + (M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hc']
    _ = 16 * (N + 5) * (1 + (M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) := by
      dsimp only [D]; ring

end
end SimultaneousPrimitiveRoots.Explicit

module

public import SimultaneousPrimitiveRoots.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter

/-! Generalization of `SimultaneousPrimitiveRoots.ZetaQuotientZeroCount` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Classical
noncomputable section

theorem numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (r : ℝ) :
    Finite (fullQuotientBallZeroIndex H r) := by
  have hc := numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
    (isCompact_closedBall (2 : ℂ) r)
  let : Fintype {s : ℂ // s ∈ closedBall (2 : ℂ) r ∧ H s = 0} := hc.fintype
  unfold fullQuotientBallZeroIndex
  infer_instance

/-- Exact cardinality with multiplicities, not just the number of distinct
zeros. No infinite-cardinality-to-zero shortcut is used. -/
theorem numberFieldEntireFullQuotientContinuation_ball_card_eq_multiplicity_sum
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (r : ℝ) :
    (Nat.card (fullQuotientBallZeroIndex H r) : ℝ) =
      (((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) r
        then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) := by
  have hc := numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
    (isCompact_closedBall (2 : ℂ) r)
  let : Fintype {s : ℂ // s ∈ closedBall (2 : ℂ) r ∧ H s = 0} := hc.fintype
  have hcard : Nat.card (fullQuotientBallZeroIndex H r) =
      ∑ s : {s : ℂ // s ∈ closedBall (2 : ℂ) r ∧ H s = 0},
        fullQuotientZeroMultiplicity H s := by
    unfold fullQuotientBallZeroIndex
    rw [Nat.card_sigma]
    simp only [Nat.card_fin]
  have hi : (Nat.card (fullQuotientBallZeroIndex H r) : ℤ) =
      ∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) r
        then (fullQuotientZeroMultiplicity H s : ℤ) else 0 := by
    have hcast : (Nat.card (fullQuotientBallZeroIndex H r) : ℤ) =
        ∑ s : {s : ℂ // s ∈ closedBall (2 : ℂ) r ∧ H s = 0},
          (fullQuotientZeroMultiplicity H s : ℤ) := by exact_mod_cast hcard
    rw [hcast, ← finsum_eq_sum_of_fintype,
      finsum_subtype_eq_finsum_cond
        (f := fun s : ℂ => (fullQuotientZeroMultiplicity H s : ℤ))
        (p := fun s : ℂ => s ∈ closedBall (2 : ℂ) r ∧ H s = 0)]
    apply finsum_congr
    intro s
    rw [finsum_eq_if]
    by_cases hz : H s = 0
    · simp [hz]
    · have hm : fullQuotientZeroMultiplicity H s = 0 :=
        (numberFieldEntireFullQuotientContinuation_multiplicity_zero_iff K L hH s).mpr hz
      simp [hz, hm]
  exact_mod_cast hi

theorem numberFieldEntireFullQuotientContinuation_finite_heightZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (T : ℝ) :
    Finite (fullQuotientHeightZeroIndex H T) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 2)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 2)
  exact Finite.of_injective (fullQuotientHeightToBall H T)
    (fullQuotientHeightToBall_injective H T)

theorem numberFieldEntireFullQuotientContinuation_zeroCount_le_ball_card (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (T : ℝ) :
    fullQuotientZeroCount H T ≤ Nat.card (fullQuotientBallZeroIndex H (T + 2)) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 2)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 2)
  exact Nat.card_le_card_of_injective (fullQuotientHeightToBall H T)
    (fullQuotientHeightToBall_injective H T)

/-- A genuine height count of the actual critical-strip, multiplicity-labelled
zeros follows from a disk boundary norm estimate. The latter is still an input. -/
theorem numberFieldEntireFullQuotientContinuation_zeroCount_jensen_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {T M : ℝ} (ht : 0 ≤ T) (hm : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)), ‖H z‖ ≤ M) :
    (fullQuotientZeroCount H T : ℝ) ≤
      (Real.log M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := by
  have hr : 0 < T + 2 := by linarith
  have hR : 0 < 2 * (T + 2) := by positivity
  have heq : (2 * (T + 2)) / (T + 2) = 2 := by field_simp
  have hj := numberFieldEntireFullQuotientContinuation_jensen_degree_le K L hH
    (r := T + 2) (R := 2 * (T + 2)) (by simpa only [abs_of_pos hr] using hr)
    (by rw [abs_of_pos hr, abs_of_pos hR]; linarith) hm
    (by simpa only [abs_of_pos hR] using hb)
  rw [abs_of_pos hr, heq] at hj
  rw [← numberFieldEntireFullQuotientContinuation_ball_card_eq_multiplicity_sum K L hH] at hj
  apply le_trans _ hj
  exact_mod_cast numberFieldEntireFullQuotientContinuation_zeroCount_le_ball_card K L hH T

end
end SimultaneousPrimitiveRoots.Explicit

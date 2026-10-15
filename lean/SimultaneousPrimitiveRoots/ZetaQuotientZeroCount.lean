module

public import SimultaneousPrimitiveRoots.KummerQuotientCenter
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Complex.Norm

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- All actual zeros in a compact disk, repeated by their finite natural
multiplicity. Finiteness is supplied by the actual analytic continuation. -/
def fullQuotientBallZeroIndex (H : ℂ → ℂ) (r : ℝ) :=
  Σ s : {s : ℂ // s ∈ closedBall (2 : ℂ) r ∧ H s = 0},
    Fin (fullQuotientZeroMultiplicity H s)

def fullQuotientHeightZeroIndex (H : ℂ → ℂ) (T : ℝ) :=
  {i : fullQuotientZeroIndex H // |(fullQuotientIndexedZero H i).im| ≤ T}

def fullQuotientZeroCount (H : ℂ → ℂ) (T : ℝ) : ℕ :=
  Nat.card (fullQuotientHeightZeroIndex H T)

theorem numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (r : ℝ) :
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
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (r : ℝ) :
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

theorem criticalStrip_height_mem_ball {s : ℂ} {T : ℝ}
    (hs : 0 ≤ s.re ∧ s.re ≤ 1) (ht : |s.im| ≤ T) :
    s ∈ closedBall (2 : ℂ) (T + 2) := by
  rw [mem_closedBall, dist_eq_norm]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (s - 2)
  have hre : |s.re - 2| = 2 - s.re := by
    rw [abs_of_nonpos (by linarith [hs.2])]
    ring
  norm_num [Complex.sub_re, Complex.sub_im] at hnorm
  rw [hre] at hnorm
  linarith [hs.1]

def fullQuotientHeightToBall (H : ℂ → ℂ) (T : ℝ) :
    fullQuotientHeightZeroIndex H T → fullQuotientBallZeroIndex H (T + 2) :=
  fun i => ⟨⟨i.1.1, criticalStrip_height_mem_ball
    (fullQuotientIndexedZero_strip H i.1) i.2, i.1.1.property.2.2⟩, i.1.2⟩

theorem fullQuotientHeightToBall_injective (H : ℂ → ℂ) (T : ℝ) :
    Function.Injective (fullQuotientHeightToBall H T) := by
  rintro ⟨⟨⟨s, hs⟩, k⟩, hi⟩ ⟨⟨⟨t, ht⟩, l⟩, hj⟩ heq
  have hst : s = t := congrArg (fun j : fullQuotientBallZeroIndex H (T + 2) => j.1.val) heq
  subst t
  have hkl : k = l := by
    dsimp [fullQuotientHeightToBall] at heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  subst l
  rfl

theorem numberFieldEntireFullQuotientContinuation_finite_heightZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (T : ℝ) :
    Finite (fullQuotientHeightZeroIndex H T) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 2)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 2)
  exact Finite.of_injective (fullQuotientHeightToBall H T)
    (fullQuotientHeightToBall_injective H T)

theorem numberFieldEntireFullQuotientContinuation_zeroCount_le_ball_card (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (T : ℝ) :
    fullQuotientZeroCount H T ≤ Nat.card (fullQuotientBallZeroIndex H (T + 2)) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 2)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 2)
  exact Nat.card_le_card_of_injective (fullQuotientHeightToBall H T)
    (fullQuotientHeightToBall_injective H T)

/-- A genuine height count of the actual critical-strip, multiplicity-labelled
zeros follows from a disk boundary norm estimate. The latter is still an input. -/
theorem numberFieldEntireFullQuotientContinuation_zeroCount_jensen_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
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
end SimultaneousPrimitiveRoots

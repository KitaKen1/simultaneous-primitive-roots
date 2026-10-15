module

public import SimultaneousPrimitiveRoots.GaussianZeroCounting

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- Actual zeros in the bounded negative strip, with all natural multiplicity labels.
No assertion that these zeros are trivial or real is required. -/
def fullQuotientLeftZeroIndex (H : ℂ → ℂ) :=
  Σ s : {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}, Fin (fullQuotientZeroMultiplicity H s)

def fullQuotientLeftIndexedZero (H : ℂ → ℂ) (i : fullQuotientLeftZeroIndex H) : ℂ := i.1

def fullQuotientLeftHeightZeroIndex (H : ℂ → ℂ) (T : ℝ) :=
  {i : fullQuotientLeftZeroIndex H // |(fullQuotientLeftIndexedZero H i).im| ≤ T}

def fullQuotientLeftZeroCount (H : ℂ → ℂ) (T : ℝ) : ℕ :=
  Nat.card (fullQuotientLeftHeightZeroIndex H T)

theorem fullQuotientLeftIndexedZero_is_zero (H : ℂ → ℂ) (i : fullQuotientLeftZeroIndex H) :
    H (fullQuotientLeftIndexedZero H i) = 0 := i.1.property.2.2

theorem fullQuotientLeftIndexedZero_strip (H : ℂ → ℂ) (i : fullQuotientLeftZeroIndex H) :
    -1 ≤ (fullQuotientLeftIndexedZero H i).re ∧ (fullQuotientLeftIndexedZero H i).re < 0 :=
  ⟨i.1.property.1, i.1.property.2.1⟩

theorem numberFieldEntireFullQuotientContinuation_countable_leftZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) :
    Countable (fullQuotientLeftZeroIndex H) := by
  have hc : {s : ℂ | -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}.Countable :=
    (numberFieldEntireFullQuotientContinuation_countable_zeros K L hH).mono
      (fun _ hs => hs.2.2)
  let : Countable {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0} := hc.to_subtype
  unfold fullQuotientLeftZeroIndex
  infer_instance

theorem leftStrip_height_mem_ball {s : ℂ} {T : ℝ}
    (hs : -1 ≤ s.re ∧ s.re < 0) (ht : |s.im| ≤ T) :
    s ∈ closedBall (2 : ℂ) (T + 3) := by
  rw [mem_closedBall, dist_eq_norm]
  have hnorm := Complex.norm_le_abs_re_add_abs_im (s - 2)
  have hre : |s.re - 2| = 2 - s.re := by
    rw [abs_of_nonpos (by linarith [hs.2])]
    ring
  norm_num [Complex.sub_re, Complex.sub_im] at hnorm
  rw [hre] at hnorm
  linarith [hs.1]

def fullQuotientLeftHeightToBall (H : ℂ → ℂ) (T : ℝ) :
    fullQuotientLeftHeightZeroIndex H T → fullQuotientBallZeroIndex H (T + 3) :=
  fun i => ⟨⟨i.1.1, leftStrip_height_mem_ball
    (fullQuotientLeftIndexedZero_strip H i.1) i.2, i.1.1.property.2.2⟩, i.1.2⟩

theorem fullQuotientLeftHeightToBall_injective (H : ℂ → ℂ) (T : ℝ) :
    Function.Injective (fullQuotientLeftHeightToBall H T) := by
  rintro ⟨⟨⟨s, hs⟩, k⟩, hi⟩ ⟨⟨⟨t, ht⟩, l⟩, hj⟩ heq
  have hst : s = t := congrArg (fun j : fullQuotientBallZeroIndex H (T + 3) => j.1.val) heq
  subst t
  have hkl : k = l := by
    dsimp [fullQuotientLeftHeightToBall] at heq
    exact eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  subst l
  rfl

theorem numberFieldEntireFullQuotientContinuation_finite_leftHeightZeroIndex (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (T : ℝ) :
    Finite (fullQuotientLeftHeightZeroIndex H T) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 3)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 3)
  exact Finite.of_injective (fullQuotientLeftHeightToBall H T)
    (fullQuotientLeftHeightToBall_injective H T)

theorem numberFieldEntireFullQuotientContinuation_leftZeroCount_le_ball_card (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H) (T : ℝ) :
    fullQuotientLeftZeroCount H T ≤ Nat.card (fullQuotientBallZeroIndex H (T + 3)) := by
  let : Finite (fullQuotientBallZeroIndex H (T + 3)) :=
    numberFieldEntireFullQuotientContinuation_finite_ballZeroIndex K L hH (T + 3)
  exact Nat.card_le_card_of_injective (fullQuotientLeftHeightToBall H T)
    (fullQuotientLeftHeightToBall_injective H T)

/-- A genuine height count of the actual negative-strip, multiplicity-labelled
zeros follows from a disk boundary norm estimate. The latter is still an input. -/
theorem numberFieldEntireFullQuotientContinuation_leftZeroCount_jensen_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {T M : ℝ} (ht : 0 ≤ T) (hm : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) (2 * (T + 3)), ‖H z‖ ≤ M) :
    (fullQuotientLeftZeroCount H T : ℝ) ≤
      (Real.log M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := by
  have hr : 0 < T + 3 := by linarith
  have hR : 0 < 2 * (T + 3) := by positivity
  have heq : (2 * (T + 3)) / (T + 3) = 2 := by field_simp
  have hj := numberFieldEntireFullQuotientContinuation_jensen_degree_le K L hH
    (r := T + 3) (R := 2 * (T + 3)) (by simpa only [abs_of_pos hr] using hr)
    (by rw [abs_of_pos hr, abs_of_pos hR]; linarith) hm
    (by simpa only [abs_of_pos hR] using hb)
  rw [abs_of_pos hr, heq] at hj
  rw [← numberFieldEntireFullQuotientContinuation_ball_card_eq_multiplicity_sum K L hH] at hj
  apply le_trans _ hj
  exact_mod_cast numberFieldEntireFullQuotientContinuation_leftZeroCount_le_ball_card K L hH T


/-- The extra unit of left-strip width costs at most a factor two in the
existing Gaussian counting series. The boundary growth is still an input. -/
theorem numberFieldEntireFullQuotientContinuation_leftGaussianMass_of_boundary_growth
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp (B * (T + 3) ^ 2)) :
    Summable (fun i : fullQuotientLeftZeroIndex H =>
      Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientLeftZeroIndex H,
        Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)) ≤
          2 * ((B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) *
            gaussianZeroCountingConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ (Module.finrank ℚ L : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ 2 * ((B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) := by positivity
  apply gaussianHeightMass_of_quadratic_count (fullQuotientLeftIndexedZero H) hC
    (fun n => numberFieldEntireFullQuotientContinuation_finite_leftHeightZeroIndex K L hH _) 
  intro n
  have ht : 0 ≤ (n : ℝ) + 1 := by positivity
  have hshift : 0 ≤ (n : ℝ) + 1 + 1 := by positivity
  have hm : 1 ≤ Real.exp (B * ((n : ℝ) + 5) ^ 2) := by
    simpa using Real.exp_le_exp.mpr (mul_nonneg hB (sq_nonneg ((n : ℝ) + 5)))
  have hb' : ∀ z ∈ sphere (2 : ℂ) (2 * ((n : ℝ) + 1 + 3)),
      ‖H z‖ ≤ Real.exp (B * ((n : ℝ) + 5) ^ 2) := by
    simpa only [show (n : ℝ) + 1 + 1 + 2 = (n : ℝ) + 1 + 3 by ring,
      show (n : ℝ) + 1 + 1 + 3 = (n : ℝ) + 5 by ring] using hb ((n : ℝ) + 1 + 1) hshift
  have h := numberFieldEntireFullQuotientContinuation_leftZeroCount_jensen_le
    K L hH ht hm hb'
  rw [Real.log_exp] at h
  apply h.trans
  rw [show 2 * ((B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) *
      ((n : ℝ) + 4) ^ 2 =
      (2 * (B + 4 * (Module.finrank ℚ L : ℝ)) * ((n : ℝ) + 4) ^ 2) / Real.log 2 by ring]
  apply div_le_div_of_nonneg_right _ hlog.le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpoly : ((n : ℝ) + 5) ^ 2 ≤ 2 * ((n : ℝ) + 4) ^ 2 := by nlinarith
  have hp : 1 ≤ 2 * ((n : ℝ) + 4) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpoly hB
  have hdeg := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * (Module.finrank ℚ L : ℝ) by positivity)
  nlinarith

end
end SimultaneousPrimitiveRoots

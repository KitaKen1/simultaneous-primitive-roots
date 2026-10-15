module

public import SimultaneousPrimitiveRoots.AbelSmoothing
public import SimultaneousPrimitiveRoots.GaussianCyclotomicCounting
public import SimultaneousPrimitiveRoots.ResearchNoteBounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset Filter Asymptotics
open scoped Topology

noncomputable section
open Classical

def gaussianAbelConstant : ℝ := 6 * Real.exp ((Real.log 2) ^ 2 + 1)

theorem gaussianAbelConstant_pos : 0 < gaussianAbelConstant := by
  unfold gaussianAbelConstant
  positivity

theorem artinGaussianWeight_le_rationalKernel {x : ℝ} (hx : 1 ≤ x) (p : ℕ) :
    artinGaussianWeight ((p : ℝ) / x) ≤ gaussianAbelConstant * rationalSmoothingKernel x p := by
  have hx0 : 0 < x := by linarith
  let D : ℝ := Real.exp ((Real.log 2) ^ 2 + 1)
  have hD : 0 < D := Real.exp_pos _
  have hden : 0 < (x + (p : ℝ)) * (x + (p : ℝ) + 1) := by positivity
  change _ ≤ 6 * D * (x ^ 2 / ((x + (p : ℝ)) * (x + (p : ℝ) + 1)))
  rw [← mul_div_assoc, le_div_iff₀ hden]
  by_cases hpx : (p : ℝ) ≤ x
  · have hw : artinGaussianWeight ((p : ℝ) / x) ≤ D := by
      unfold artinGaussianWeight D
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (Real.log ((p : ℝ) / x))]
    have hd : (x + (p : ℝ)) * (x + (p : ℝ) + 1) ≤ 6 * x ^ 2 := by
      calc
        _ ≤ (2 * x) * (3 * x) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ D * ((x + (p : ℝ)) * (x + (p : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hw hden.le
      _ ≤ D * (6 * x ^ 2) := mul_le_mul_of_nonneg_left hd hD.le
      _ = _ := by ring
  · have hp0 : 0 < (p : ℝ) := by linarith
    have hw := artinGaussianWeight_le_rpow (div_pos hp0 hx0) (2 : ℝ)
    have heq : ((p : ℝ) / x) ^ (-2 : ℝ) = x ^ 2 / (p : ℝ) ^ 2 := by
      rw [Real.rpow_neg (div_pos hp0 hx0).le, Real.rpow_two]
      field_simp
    norm_num only [show (2 : ℝ) ^ 2 / 4 = 1 by norm_num, heq] at hw
    change artinGaussianWeight ((p : ℝ) / x) ≤ D * (x ^ 2 / (p : ℝ) ^ 2) at hw
    have hd : (x + (p : ℝ)) * (x + (p : ℝ) + 1) ≤ 6 * (p : ℝ) ^ 2 := by
      calc
        _ ≤ (2 * (p : ℝ)) * (3 * (p : ℝ)) :=
          mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ (D * (x ^ 2 / (p : ℝ) ^ 2)) * ((x + (p : ℝ)) * (x + (p : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hw hden.le
      _ ≤ (D * (x ^ 2 / (p : ℝ) ^ 2)) * (6 * (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp

def progressionChebyshevTerm (q p : ℕ) : ℝ :=
  if p.Prime ∧ q ∣ p - 1 then Real.log p else 0

def progressionChebyshevPrefix (q N : ℕ) : ℝ :=
  ∑ p ∈ range N, progressionChebyshevTerm q p

theorem progressionChebyshevTerm_nonneg (q p : ℕ) :
    0 ≤ progressionChebyshevTerm q p := by
  unfold progressionChebyshevTerm
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

theorem progressionChebyshevTerm_le_nat (q p : ℕ) :
    progressionChebyshevTerm q p ≤ (p : ℝ) := by
  unfold progressionChebyshevTerm
  split_ifs with hp
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.1.pos
    exact (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  · positivity

theorem progressionChebyshevPrefix_le_square (q N : ℕ) :
    progressionChebyshevPrefix q N ≤ (N : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _p ∈ range N, (N : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply (progressionChebyshevTerm_le_nat q p).trans
      exact_mod_cast (mem_range.mp hp).le
    _ = _ := by simp; ring

theorem gaussianProgressionPrimeTerm_eq_chebyshev (q : ℕ) (x : ℝ) (p : ℕ) :
    gaussianProgressionPrimeTerm q x p =
      progressionChebyshevTerm q p * artinGaussianWeight ((p : ℝ) / x) := by
  simp only [gaussianProgressionPrimeTerm, progressionChebyshevTerm]
  split_ifs <;> simp

/-- An unsmoothed AP sieve input. No proof of this proposition is assumed
implicitly: the modulus q and cutoff N are both quantified here. -/
def ProgressionChebyshevUpperBound (C : ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → ∀ N : ℕ, q ^ 2 ≤ N →
    progressionChebyshevPrefix q N ≤ C * (N : ℝ) / ((q : ℝ) - 1)

theorem progressionChebyshevPrefix_le_with_error {C : ℝ} (hC : 0 ≤ C)
    (hAP : ProgressionChebyshevUpperBound C) {q : ℕ} (hq : q.Prime) (N : ℕ) :
    progressionChebyshevPrefix q N ≤
      (C / ((q : ℝ) - 1)) * N + (q : ℝ) ^ 4 := by
  have hq1 : 0 < (q : ℝ) - 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  by_cases hN : q ^ 2 ≤ N
  · apply (hAP q hq N hN).trans
    rw [div_mul_eq_mul_div]
    exact le_add_of_nonneg_right (by positivity)
  · have hNq : (N : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast (not_le.mp hN).le
    have hNsq : (N : ℝ) ^ 2 ≤ (q : ℝ) ^ 4 := by
      simpa [← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hNq 2
    exact (progressionChebyshevPrefix_le_square q N).trans
      (hNsq.trans (le_add_of_nonneg_left (by positivity)))

theorem gaussianProgressionPrimeTrace_le_of_chebyshev {C : ℝ} (hC : 0 ≤ C)
    (hAP : ProgressionChebyshevUpperBound C) {q : ℕ} (hq : q.Prime)
    {x : ℝ} (hx : 1 ≤ x) :
    ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x ≤
      gaussianAbelConstant * C * x + gaussianAbelConstant * (q : ℝ) ^ 5 := by
  have hx0 : 0 < x := by linarith
  have hq1 : 0 < (q : ℝ) - 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
    linarith
  have hprefix := progressionChebyshevPrefix_le_with_error hC hAP hq
  have hrange : ∀ N, ∑ p ∈ range N, gaussianProgressionPrimeTerm q x p ≤
      gaussianAbelConstant * ((C / ((q : ℝ) - 1)) * x + (q : ℝ) ^ 4) := by
    intro N
    calc
      _ ≤ ∑ p ∈ range N, gaussianAbelConstant *
          (progressionChebyshevTerm q p * rationalSmoothingKernel x p) := by
        apply sum_le_sum
        intro p _
        rw [gaussianProgressionPrimeTerm_eq_chebyshev]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left (artinGaussianWeight_le_rationalKernel hx p)
            (progressionChebyshevTerm_nonneg q p)
      _ = gaussianAbelConstant * (∑ p ∈ range N,
          progressionChebyshevTerm q p * rationalSmoothingKernel x p) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rationalSmoothing_sum_range_le hx0 (by positivity) (by positivity) _ hprefix N)
        gaussianAbelConstant_pos.le
  have hsum := Real.tsum_le_of_sum_range_le (gaussianProgressionPrimeTerm_nonneg q x) hrange
  change gaussianProgressionPrimeTrace q x ≤ _ at hsum
  apply (mul_le_mul_of_nonneg_left hsum hq1.le).trans
  have heq : ((q : ℝ) - 1) * (gaussianAbelConstant *
      ((C / ((q : ℝ) - 1)) * x + (q : ℝ) ^ 4)) =
      gaussianAbelConstant * C * x + gaussianAbelConstant * ((q : ℝ) - 1) * (q : ℝ) ^ 4 := by
    field_simp
  rw [heq]
  nlinarith [gaussianAbelConstant_pos, pow_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) 4]

def gaussianProgressionSmoothingError (η x : ℝ) : ℝ :=
  (32 * gaussianAbelConstant) * x ^ (5 * η)

theorem gaussianProgressionSmoothingError_isLittleO {η : ℝ} (hη : η < 1 / 5) :
    gaussianProgressionSmoothingError η =o[atTop] (fun x : ℝ => x) :=
  sublinear_power_isLittleO_id _ (by linarith)

theorem uniformGaussianProgressionUpperBound_of_chebyshev {η C : ℝ}
    (hη : η < 1 / 5) (hC : 0 ≤ C) (hAP : ProgressionChebyshevUpperBound C) :
    UniformGaussianProgressionUpperBound η (gaussianAbelConstant * C + 1) := by
  have he := (gaussianProgressionSmoothingError_isLittleO hη).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with x hex hx
  intro q hq hcut
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hx0 : 0 < x := by linarith
  have hqx : (q : ℝ) ≤ 2 * x ^ η :=
    (by exact_mod_cast hcut : (q : ℝ) ≤ Nat.floor (2 * x ^ η)).trans (Nat.floor_le (by positivity))
  have hp : (q : ℝ) ^ 5 ≤ (2 * x ^ η) ^ (5 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hqx 5
  have heq : (2 * x ^ η) ^ (5 : ℕ) = 32 * x ^ (5 * η) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
    norm_num
    congr 1
    ring
  have herr : gaussianAbelConstant * (q : ℝ) ^ 5 ≤ gaussianProgressionSmoothingError η x := by
    unfold gaussianProgressionSmoothingError
    apply (mul_le_mul_of_nonneg_left hp gaussianAbelConstant_pos.le).trans_eq
    rw [heq]
    ring
  have herrx : gaussianProgressionSmoothingError η x ≤ x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, one_mul] at hex
    exact (le_abs_self _).trans hex
  exact (gaussianProgressionPrimeTrace_le_of_chebyshev hC hAP hq hx).trans
    (by nlinarith [herr.trans herrx])

theorem uniformCyclotomicGaussianUpperBound_of_chebyshev {η C : ℝ}
    (hη : η < 1 / 5) (hC : 0 ≤ C) (hAP : ProgressionChebyshevUpperBound C) :
    UniformCyclotomicGaussianUpperBound η (gaussianAbelConstant * C + 3) := by
  have h := uniformCyclotomicGaussianUpperBound_of_progression (by linarith : η < 1 / 2)
    (uniformGaussianProgressionUpperBound_of_chebyshev hη hC hAP)
  simpa only [show gaussianAbelConstant * C + 1 + 2 = gaussianAbelConstant * C + 3 by ring] using h

theorem dyadicProgressionPrimes_card_mul_log_le_chebyshev (q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ((dyadicProgressionPrimes q x).card : ℝ) * Real.log x ≤
      progressionChebyshevPrefix q (Nat.floor (2 * x) + 1) := by
  have hx0 : 0 < x := by linarith
  calc
    _ = ∑ _p ∈ dyadicProgressionPrimes q x, Real.log x := by simp
    _ ≤ ∑ p ∈ dyadicProgressionPrimes q x, progressionChebyshevTerm q p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨_, hprime, hpx, _, hd⟩ := mem_filter.mp hp
      rw [progressionChebyshevTerm, if_pos ⟨hprime, hd⟩]
      exact Real.log_le_log hx0 hpx.le
    _ ≤ progressionChebyshevPrefix q (Nat.floor (2 * x) + 1) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_filter.mp hp).1
      · intro p _ _
        exact progressionChebyshevTerm_nonneg q p

theorem dyadicProgressionPrimes_card_le_of_chebyshev {C : ℝ} (hC : 0 ≤ C)
    (hAP : ProgressionChebyshevUpperBound C) {q : ℕ} (hq : q.Prime)
    {x : ℝ} (hx : 2 ≤ x) (hqpow : (q : ℝ) ^ 5 ≤ x) :
    ((dyadicProgressionPrimes q x).card : ℝ) ≤
      (6 * C + 1) * (x / Real.log x) * (1 / (q : ℝ)) := by
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  let N := Nat.floor (2 * x) + 1
  have hN : (N : ℝ) ≤ 3 * x := by
    dsimp [N]
    push_cast
    have hf := Nat.floor_le (by linarith : 0 ≤ 2 * x)
    linarith
  have hcoef : (q : ℝ) * (C / ((q : ℝ) - 1)) ≤ 2 * C := by
    rw [← mul_div_assoc, div_le_iff₀ hq1]
    nlinarith
  have hcount := dyadicProgressionPrimes_card_mul_log_le_chebyshev q hx1
  have hmain : ((dyadicProgressionPrimes q x).card : ℝ) * ((q : ℝ) * Real.log x) ≤
      (6 * C + 1) * x := by
    calc
      _ = (q : ℝ) * (((dyadicProgressionPrimes q x).card : ℝ) * Real.log x) := by ring
      _ ≤ (q : ℝ) * progressionChebyshevPrefix q N := mul_le_mul_of_nonneg_left hcount hq0.le
      _ ≤ (q : ℝ) * ((C / ((q : ℝ) - 1)) * N + (q : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left (progressionChebyshevPrefix_le_with_error hC hAP hq N) hq0.le
      _ = ((q : ℝ) * (C / ((q : ℝ) - 1))) * N + (q : ℝ) ^ 5 := by ring
      _ ≤ (2 * C) * (3 * x) + x :=
        add_le_add (mul_le_mul hcoef hN (Nat.cast_nonneg N) (by positivity)) hqpow
      _ = _ := by ring
  apply ((le_div_iff₀ (mul_pos hq0 hlog)).2 hmain).trans_eq
  ring

theorem moving_fifth_power_eventually_le {η : ℝ} (hη : η < 1 / 5) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, q ≤ Nat.floor (2 * x ^ η) → (q : ℝ) ^ 5 ≤ x := by
  have hsmall := (sublinear_power_isLittleO_id (32 : ℝ) (by linarith : 5 * η < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hxsmall hx
  intro q hcut
  have hqx : (q : ℝ) ≤ 2 * x ^ η :=
    (by exact_mod_cast hcut : (q : ℝ) ≤ Nat.floor (2 * x ^ η)).trans (Nat.floor_le (by positivity))
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hqx 5
  have heq : (2 * x ^ η) ^ (5 : ℕ) = 32 * x ^ (5 * η) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hx.le]
    norm_num
    congr 1
    ring
  rw [heq] at hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, one_mul] at hxsmall
  exact hp.trans ((le_abs_self _).trans hxsmall)

theorem uniformProgressionUpperBound_of_chebyshev {η C : ℝ}
    (hη : η < 1 / 5) (hC : 0 ≤ C) (hAP : ProgressionChebyshevUpperBound C) :
    UniformProgressionUpperBound η (6 * C + 1) := by
  filter_upwards [moving_fifth_power_eventually_le hη, eventually_ge_atTop (2 : ℝ)]
    with x hpow hx
  intro q hq hcut
  exact dyadicProgressionPrimes_card_le_of_chebyshev hC hAP hq hx (hpow q hcut)

theorem progression_upper_bounds_of_chebyshev {η C : ℝ}
    (hη : η < 1 / 5) (hC : 0 ≤ C) (hAP : ProgressionChebyshevUpperBound C) :
    UniformProgressionUpperBound η (6 * C + 1) ∧
      UniformGaussianProgressionUpperBound η (gaussianAbelConstant * C + 1) ∧
      UniformCyclotomicGaussianUpperBound η (gaussianAbelConstant * C + 3) :=
  ⟨uniformProgressionUpperBound_of_chebyshev hη hC hAP,
    uniformGaussianProgressionUpperBound_of_chebyshev hη hC hAP,
    uniformCyclotomicGaussianUpperBound_of_chebyshev hη hC hAP⟩

end

end SimultaneousPrimitiveRoots

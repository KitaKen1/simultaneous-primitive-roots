module

public import SimultaneousPrimitiveRoots.GaussianProgressionSmoothing

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Finset

noncomputable section
open Classical

def progressionPrefixPrimes (q N : ℕ) : Finset ℕ :=
  (range N).filter fun p => p.Prime ∧ q ∣ p - 1

theorem progressionChebyshevPrefix_eq_sum_primes (q N : ℕ) :
    progressionChebyshevPrefix q N = ∑ p ∈ progressionPrefixPrimes q N, Real.log p := by
  simp only [progressionChebyshevPrefix, progressionChebyshevTerm, progressionPrefixPrimes,
    sum_filter]

theorem progressionChebyshevPrefix_le_card_log (q N : ℕ) :
    progressionChebyshevPrefix q N ≤ ((progressionPrefixPrimes q N).card : ℝ) * Real.log N := by
  rw [progressionChebyshevPrefix_eq_sum_primes]
  calc
    _ ≤ ∑ _p ∈ progressionPrefixPrimes q N, Real.log N := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hprime, _⟩ := mem_filter.mp hp
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
      exact Real.log_le_log hp0 (by exact_mod_cast (mem_range.mp hpN).le)
    _ = _ := by simp

theorem progression_log_ratio_half {q N : ℕ} (hq : q.Prime) (hN : q ^ 2 ≤ N) :
    0 < Real.log ((N : ℝ) / q) ∧ Real.log N ≤ 2 * Real.log ((N : ℝ) / q) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : 0 < (q : ℝ) := by linarith
  have hNq : (q : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by nlinarith
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hl : 2 * Real.log (q : ℝ) ≤ Real.log N := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      Real.log_le_log (pow_pos hq0 2) hNq
  rw [Real.log_div hN0.ne' hq0.ne']
  constructor <;> linarith

/-- A classical AP Brun--Titchmarsh input at cutoffs N≥q². This definition
does not assert the estimate, and the interval-prime bound without a modulus
in the inspected external libraries cannot be substituted for it. -/
def ProgressionBrunTitchmarshUpperBound : Prop :=
  ∀ q : ℕ, q.Prime → ∀ N : ℕ, q ^ 2 ≤ N →
    ((progressionPrefixPrimes q N).card : ℝ) ≤
      2 * (N : ℝ) / (((q : ℝ) - 1) * Real.log ((N : ℝ) / q))

theorem progressionChebyshevUpperBound_of_brunTitchmarsh
    (hBT : ProgressionBrunTitchmarshUpperBound) : ProgressionChebyshevUpperBound 4 := by
  intro q hq N hN
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  obtain ⟨hlpos, hlhalf⟩ := progression_log_ratio_half hq hN
  calc
    _ ≤ ((progressionPrefixPrimes q N).card : ℝ) * Real.log N :=
      progressionChebyshevPrefix_le_card_log q N
    _ ≤ (2 * (N : ℝ) / (((q : ℝ) - 1) * Real.log ((N : ℝ) / q))) * Real.log N :=
      mul_le_mul_of_nonneg_right (hBT q hq N hN) hlogN
    _ = (2 * (N : ℝ) / ((q : ℝ) - 1)) *
        (Real.log N / Real.log ((N : ℝ) / q)) := by
      field_simp [hq1.ne', hlpos.ne']
    _ ≤ (2 * (N : ℝ) / ((q : ℝ) - 1)) * 2 :=
      mul_le_mul_of_nonneg_left ((div_le_iff₀ hlpos).2 hlhalf) (by positivity)
    _ = _ := by ring

theorem progression_upper_bounds_of_brunTitchmarsh {η : ℝ} (hη : η < 1 / 5)
    (hBT : ProgressionBrunTitchmarshUpperBound) :
    UniformProgressionUpperBound η 25 ∧
      UniformGaussianProgressionUpperBound η (4 * gaussianAbelConstant + 1) ∧
      UniformCyclotomicGaussianUpperBound η (4 * gaussianAbelConstant + 3) := by
  have h := progression_upper_bounds_of_chebyshev hη (by norm_num : (0 : ℝ) ≤ 4)
    (progressionChebyshevUpperBound_of_brunTitchmarsh hBT)
  simpa only [show (6 : ℝ) * 4 + 1 = 25 by norm_num, mul_comm gaussianAbelConstant 4] using h

theorem fixed_progression_upper_bounds_of_brunTitchmarsh
    (hBT : ProgressionBrunTitchmarshUpperBound) :
    UniformProgressionUpperBound (1 / 4000000) 25 ∧
      UniformGaussianProgressionUpperBound (1 / 4000000) (4 * gaussianAbelConstant + 1) ∧
      UniformCyclotomicGaussianUpperBound (1 / 4000000) (4 * gaussianAbelConstant + 3) :=
  progression_upper_bounds_of_brunTitchmarsh (by norm_num) hBT

theorem sparseBadPowerResidueBound_of_brunTitchmarsh {η : ℝ} (hη : η < 1 / 5)
    (hBT : ProgressionBrunTitchmarshUpperBound) (A : Finset ℕ) (B : Set ℕ) (Q : ℝ → ℕ) :
    SparseBadPowerResidueBound A η 25 B Q :=
  sparseBadPowerResidueBound_of_progression (progression_upper_bounds_of_brunTitchmarsh hη hBT).1 A B Q

end

end SimultaneousPrimitiveRoots

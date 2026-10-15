module

public import SimultaneousPrimitiveRoots.RealProgressionSieve

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Finset Filter Asymptotics
noncomputable section
open Classical

/-- The rounded mass has a square-root sieve level. Its error is independent of q. -/
theorem progressionPrefixPrimes_card_sqrt_sieve_le {q M : ℕ} (hq : q.Prime)
    (N : ℕ) (hM : 2 ≤ M) (hNM : (N : ℝ) / q ≤ M) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤ 8 * (M : ℝ) / Real.log M +
      4 * (M : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log M) ^ 3 := by
  have hM1 : 1 < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  have hM0 : 0 < (M : ℝ) := by linarith
  let y := (M : ℝ) ^ (1 / 2 : ℝ)
  have hy : 1 < y := Real.one_lt_rpow hM1 (by norm_num)
  have hlog : Real.log y = (1 / 2) * Real.log M := Real.log_rpow hM0 _
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmain : 4 * (N : ℝ) / ((q : ℝ) * Real.log y) ≤ 8 * (M : ℝ) / Real.log M := by
    calc
      _ = 4 * ((N : ℝ) / q) / Real.log y := by ring
      _ ≤ 4 * (M : ℝ) / Real.log y :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hNM (by norm_num)) hlogy.le
      _ = _ := by rw [hlog]; ring
  have hb : 1 ≤ (1 + Real.log y) ^ 3 := one_le_pow₀ (by linarith)
  have herr : y * (1 + Real.log y) ^ 3 + y + 2 ≤ 4 * y * (1 + Real.log y) ^ 3 := by
    have ht : y ≤ y * (1 + Real.log y) ^ 3 := by nlinarith
    nlinarith
  have h := progressionPrefixPrimes_card_real_sieve_le hq y N hy
  rw [← hlog]
  change ((progressionPrefixPrimes q N).card : ℝ) ≤
    8 * (M : ℝ) / Real.log M + 4 * y * (1 + Real.log y) ^ 3
  linarith

theorem progressionSieveError_isBigO :
    (fun M : ℕ => (4 : ℝ) * (M : ℝ) ^ (1 / 2 : ℝ) *
      (1 + (1 / 2) * Real.log M) ^ 3) =O[atTop]
      (fun M : ℕ => (M : ℝ) / Real.log M) := by
  have h := PrimeUpperBound._lemma1.const_mul_left (4 / 3 : ℝ)
  apply h.congr_left
  intro M
  ring

theorem progressionSieveError_eventually_le : ∃ D : ℝ, 0 < D ∧ ∃ M₀ : ℕ,
    ∀ M : ℕ, M₀ ≤ M → 2 ≤ M →
      4 * (M : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log M) ^ 3 ≤
        D * (M : ℝ) / Real.log M := by
  obtain ⟨D, hD, hbound⟩ := progressionSieveError_isBigO.exists_pos
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hbound.bound
  refine ⟨D, hD, M₀, ?_⟩
  intro M hM₀' hM
  have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
  have herr : 0 ≤ 4 * (M : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log M) ^ 3 := by
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg herr,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg M) hlog), mul_div_assoc] using hM₀ M hM₀'

theorem progressionPrefixPrimes_card_le_mass_add_one {q : ℕ} (hq : q.Prime) (N : ℕ) :
    ((progressionPrefixPrimes q N).card : ℝ) ≤ (N : ℝ) / q + 1 := by
  have hcard : ((progressionPrefixPrimes q N).card : ℝ) ≤
      (progressionDivisorSupport q 1 N).card := by
    exact_mod_cast card_le_card (progressionPrefixPrimes_subset_support q N)
  have h := progressionDivisorSupport_card_le_mass_add_one hq (by norm_num : 0 < 1) N
  simpa [progressionSieveDensity, div_eq_mul_inv] using hcard.trans h

/-- A uniform AP Chebyshev bound with an unspecified absolute constant suffices. -/
theorem exists_progressionChebyshevUpperBound :
    ∃ C : ℝ, 0 ≤ C ∧ ProgressionChebyshevUpperBound C := by
  obtain ⟨D, hD, M₀, herr⟩ := progressionSieveError_eventually_le
  let K := max M₀ 2
  let C := max (4 * (8 + D)) (4 * Real.log K)
  have hC : 0 ≤ C := le_trans (by linarith : 0 ≤ 4 * (8 + D)) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq N hN
  let T : ℝ := (N : ℝ) / q
  let M : ℕ := Nat.ceil T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : 0 < (q : ℝ) := by linarith
  have hNq : (q : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hTq : (q : ℝ) ≤ T := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hT2 : 2 ≤ T := hq2.trans hTq
  have hT0 : 0 < T := by linarith
  have hTM : T ≤ (M : ℝ) := Nat.le_ceil T
  have hM2 : 2 ≤ M := by exact_mod_cast hT2.trans hTM
  have hM1 : 1 < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  have hM0 : 0 < (M : ℝ) := by linarith
  have hMlog : 0 < Real.log M := Real.log_pos hM1
  have hMT : (M : ℝ) ≤ 2 * T := Nat.ceil_le_two_mul (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hloghalf : Real.log N ≤ 2 * Real.log T := (progression_log_ratio_half hq hN).2
  have htheta : progressionChebyshevPrefix q N ≤ C * T := by
    by_cases hMK : K ≤ M
    · have hM₀ : M₀ ≤ M := (le_max_left _ _).trans hMK
      have hcount := progressionPrefixPrimes_card_sqrt_sieve_le hq N hM2 hTM
      have herrM := herr M hM₀ hM2
      have hcount' : ((progressionPrefixPrimes q N).card : ℝ) ≤
          (8 + D) * (M : ℝ) / Real.log M := by
        calc
          _ ≤ 8 * (M : ℝ) / Real.log M + D * (M : ℝ) / Real.log M := by linarith
          _ = _ := by ring
      have hlogNM : Real.log N ≤ 2 * Real.log M :=
        hloghalf.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hT0 hTM) (by norm_num))
      calc
        _ ≤ ((progressionPrefixPrimes q N).card : ℝ) * Real.log N :=
          progressionChebyshevPrefix_le_card_log q N
        _ ≤ ((8 + D) * (M : ℝ) / Real.log M) * (2 * Real.log M) := by
          gcongr
        _ = 2 * (8 + D) * (M : ℝ) := by field_simp
        _ ≤ 4 * (8 + D) * T := by nlinarith
        _ ≤ C * T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT0.le
    · have hMK' : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hMK))
      have hTK : T ≤ (K : ℝ) := hTM.trans hMK'
      have hlogNK : Real.log N ≤ 2 * Real.log K :=
        hloghalf.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hT0 hTK) (by norm_num))
      have hcount : ((progressionPrefixPrimes q N).card : ℝ) ≤ 2 * T := by
        have h := progressionPrefixPrimes_card_le_mass_add_one hq N
        change ((progressionPrefixPrimes q N).card : ℝ) ≤ T + 1 at h
        linarith
      calc
        _ ≤ ((progressionPrefixPrimes q N).card : ℝ) * Real.log N :=
          progressionChebyshevPrefix_le_card_log q N
        _ ≤ (2 * T) * (2 * Real.log K) := by gcongr
        _ = 4 * Real.log K * T := by ring
        _ ≤ C * T := mul_le_mul_of_nonneg_right (le_max_right _ _) hT0.le
  calc
    _ ≤ C * ((N : ℝ) / q) := htheta
    _ = C * (N : ℝ) / q := by ring
    _ ≤ C * (N : ℝ) / ((q : ℝ) - 1) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg N))
        (by linarith) (by linarith)

end
end SimultaneousPrimitiveRoots

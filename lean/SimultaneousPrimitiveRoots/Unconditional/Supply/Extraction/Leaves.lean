module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements
public import SimultaneousPrimitiveRoots.Hooley.PrimeReciprocalWindow

/-!
# Leaves of the prime extraction that are proved

* `primeMassBound : PrimeMassBound`: `∑_p Φ((p-1)/x) ≪_Φ x / log x` (`[P-07:0680–0681]`), from
  the Chebyshev bound `exists_chebyshev_constant` of `Hooley/PrimeReciprocalWindow.lean` (LeanPool's
  Selberg sieve). No Siegel–Walfisz input is used, so the field `primeMass` of `ExtractionLeaves`
  is discharged by `fun _ => primeMassBound`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- A set of `u < m` with `u + 1` prime has at most `π(m)` elements. -/
theorem card_shifted_primes_le (m : ℕ) (T : Finset ℕ)
    (hT : ∀ u ∈ T, u < m ∧ (u + 1).Prime) : T.card ≤ Nat.primeCounting m :=
  calc T.card = (T.image (fun u => u + 1)).card :=
        (Finset.card_image_of_injective T (add_left_injective 1)).symm
    _ ≤ Nat.primeCounting m := card_filter_prime_le_primeCounting fun q hq => by
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
        exact ⟨(hT u hu).2, Nat.succ_le_of_lt (hT u hu).1⟩

/-- **The number of primes under a cutoff** (`[P-07:0680–0681]`), from Chebyshev's bound. -/
theorem primeMassBound : PrimeMassBound := by
  intro Φ hΦ
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨BΦ, hBΦ0, hBΦ⟩ := hΦ.exists_bound
  obtain ⟨C, hC0, N, hπ⟩ := exists_chebyshev_constant
  refine ⟨BΦ * (4 * C * R), ?_⟩
  filter_upwards [eventually_ge_atTop (1 / R),
    eventually_ge_atTop (Real.exp (2 * |Real.log R|)), eventually_ge_atTop ((N : ℝ) / R),
    eventually_gt_atTop (1 : ℝ)] with x hx1 hx2 hx3 hx4
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx4
  have hLne : Real.log x ≠ 0 := hL.ne'
  have hRx : 0 < R * x := mul_pos hR0 hx0
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊R * x⌋₊ + 1 := ⟨_, rfl⟩
  have hRx1 : 1 ≤ R * x := by
    have h := (div_le_iff₀ hR0).mp hx1
    rwa [mul_comm] at h
  have hmge : R * x < (m : ℝ) := by
    rw [hm, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hmle : (m : ℝ) ≤ 2 * (R * x) := by
    rw [hm, Nat.cast_add, Nat.cast_one]
    have h := Nat.floor_le hRx.le
    linarith
  have hmN : N ≤ m := by
    have h1 : (N : ℝ) ≤ R * x := by
      have h := (div_le_iff₀ hR0).mp hx3
      rwa [mul_comm] at h
    have h2 : (N : ℝ) < (m : ℝ) := lt_of_le_of_lt h1 hmge
    exact_mod_cast h2.le
  have hlogR : -(Real.log x / 2) ≤ Real.log R := by
    have h1 : 2 * |Real.log R| ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos _) hx2
      rwa [Real.log_exp] at h
    have h2 := neg_abs_le (Real.log R)
    linarith
  have hlogm : Real.log x / 2 ≤ Real.log (m : ℝ) := by
    have h1 : Real.log (R * x) = Real.log R + Real.log x := Real.log_mul hR0.ne' hx0.ne'
    have h2 : Real.log (R * x) ≤ Real.log (m : ℝ) := Real.log_le_log hRx hmge.le
    linarith
  have hlm : 0 < Real.log (m : ℝ) := by linarith
  have hpi : (Nat.primeCounting m : ℝ) ≤ 4 * C * R * (x / Real.log x) := by
    refine (hπ m hmN).trans ?_
    rw [div_le_iff₀ hlm]
    have h1 : C * (m : ℝ) ≤ C * (2 * (R * x)) := mul_le_mul_of_nonneg_left hmle hC0
    have h0 : 0 ≤ 4 * C * R * (x / Real.log x) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hR0.le) (div_pos hx0 hL).le
    have h2 : 4 * C * R * (x / Real.log x) * (Real.log x / 2) ≤
        4 * C * R * (x / Real.log x) * Real.log (m : ℝ) := mul_le_mul_of_nonneg_left hlogm h0
    have h3 : 4 * C * R * (x / Real.log x) * (Real.log x / 2) = C * (2 * (R * x)) :=
      calc 4 * C * R * (x / Real.log x) * (Real.log x / 2)
          = 2 * C * R * x * (Real.log x / Real.log x) := by ring
        _ = C * (2 * (R * x)) := by
            rw [div_self hLne]
            ring
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℕ,
      T = (Finset.range (⌊R * x⌋₊ + 1)).filter (fun u => (u + 1).Prime) := ⟨_, rfl⟩
  have hT : (T.card : ℝ) ≤ (Nat.primeCounting m : ℝ) := by
    have h := card_shifted_primes_le m T (fun u hu => by
      rw [hTdef] at hu
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hu
      refine ⟨?_, h2⟩
      rw [hm]
      exact Finset.mem_range.mp h1)
    exact_mod_cast h
  have hinter : ((Finset.range (⌊R * x⌋₊ + 1) ∩ T).card : ℝ) ≤ (T.card : ℝ) := by
    have h : (Finset.range (⌊R * x⌋₊ + 1) ∩ T).card ≤ T.card :=
      Finset.card_le_card Finset.inter_subset_right
    exact_mod_cast h
  rw [shiftSum_eq_sum hR hx0]
  calc _ ≤ ∑ u ∈ Finset.range (⌊R * x⌋₊ + 1), (if u ∈ T then BΦ else 0) :=
        Finset.sum_le_sum fun u hu => by
          by_cases h1 : (u + 1).Prime
          · have hmemT : u ∈ T := by
              rw [hTdef]
              exact Finset.mem_filter.mpr ⟨hu, h1⟩
            rw [if_pos h1, if_pos hmemT, mul_one]
            exact hBΦ _
          · rw [if_neg h1]
            split_ifs
            · exact hBΦ0
            · exact le_rfl
    _ = ∑ _u ∈ Finset.range (⌊R * x⌋₊ + 1) ∩ T, BΦ := Finset.sum_ite_mem _ _ _
    _ = ((Finset.range (⌊R * x⌋₊ + 1) ∩ T).card : ℝ) * BΦ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (T.card : ℝ) * BΦ := mul_le_mul_of_nonneg_right hinter hBΦ0
    _ ≤ (Nat.primeCounting m : ℝ) * BΦ := mul_le_mul_of_nonneg_right hT hBΦ0
    _ ≤ 4 * C * R * (x / Real.log x) * BΦ := mul_le_mul_of_nonneg_right hpi hBΦ0
    _ = BΦ * (4 * C * R) * (x / Real.log x) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

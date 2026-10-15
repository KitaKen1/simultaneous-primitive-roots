module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements

/-!
# The mass of a dyadic band of primes, from Mertens' estimate

`dyadicPrimeMass_of_mertensReciprocal : MertensReciprocal → DyadicPrimeMass`
(`[P-02:0060–0064]`, (eq:band-mass)): for every set `T` of primes between the open band
`(exp y, exp (2y))` and the closed band `[exp y, exp (2y)]`,

`∑_{p ∈ T} 1/p = log 2 + o(1)` as `y → ∞`.

Mertens' estimate `∑_{p ≤ x} 1/p = log log x + M + O(1/log x)` at `x = exp s`, `x = exp t` gives
(`exists_reciprocal_window`), for `1 ≤ s ≤ t`,

`| ∑_{exp s < p ≤ exp t} 1/p - (log t - log s) | ≤ 2 C / s`.

The set `T` is contained in the window `(exp (y - 1), exp (2y)]` and contains the window
`(exp y, exp (2y - 1)]`, and `log u - log (u - 1) ≤ 1/(u - 1)` (`log_sub_log_pred_le`), so

`log 2 - (1 + 2C)/(y - 1) ≤ ∑_{p ∈ T} 1/p ≤ log 2 + (1 + 2C)/(y - 1)`.

The threshold is `Y₀ = 2 + (1 + 2C)/δ`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-- `log u - log (u - 1) ≤ 1 / (u - 1)` for `u > 1`. -/
theorem log_sub_log_pred_le {u : ℝ} (hu : 1 < u) :
    Real.log u - Real.log (u - 1) ≤ 1 / (u - 1) := by
  have h1 : 0 < u - 1 := by linarith
  have h0 : 0 < u := by linarith
  have h2 : Real.log (u / (u - 1)) ≤ u / (u - 1) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos h0 h1)
  rw [Real.log_div h0.ne' h1.ne'] at h2
  have hu' : u = 1 + (u - 1) := by ring
  have h3 : u / (u - 1) = 1 / (u - 1) + 1 :=
    calc u / (u - 1) = (1 + (u - 1)) / (u - 1) := congrArg (fun t : ℝ => t / (u - 1)) hu'
      _ = 1 / (u - 1) + (u - 1) / (u - 1) := add_div _ _ _
      _ = 1 / (u - 1) + 1 := by rw [div_self h1.ne']
  linarith

/-- **Mertens' estimate on a window**: for `1 ≤ s ≤ t`,
`| ∑_{exp s < p ≤ exp t} 1/p - (log t - log s) | ≤ 2 C / s`, with the constant `C` of
`MertensReciprocal`. -/
theorem exists_reciprocal_window (hM : MertensReciprocal) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, 1 ≤ s → s ≤ t →
      |(∑ p ∈ (Finset.Icc 2 ⌊Real.exp t⌋₊).filter Nat.Prime \
            (Finset.Icc 2 ⌊Real.exp s⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
          (Real.log t - Real.log s)| ≤ 2 * C / s := by
  have hM' : ∃ M C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
        Real.log (Real.log x) - M| ≤ C / Real.log x := hM
  obtain ⟨M, C, hC, hMC⟩ := hM'
  refine ⟨C, hC, fun s t hs hst => ?_⟩
  have ht : 1 ≤ t := hs.trans hst
  have hs0 : 0 < s := by linarith
  have hes : 2 ≤ Real.exp s := by
    have h := Real.add_one_le_exp s
    linarith
  have het : 2 ≤ Real.exp t := by
    have h := Real.add_one_le_exp t
    linarith
  have h1 := hMC (Real.exp s) hes
  have h2 := hMC (Real.exp t) het
  rw [Real.log_exp] at h1 h2
  have hsub : (Finset.Icc 2 ⌊Real.exp s⌋₊).filter Nat.Prime ⊆
      (Finset.Icc 2 ⌊Real.exp t⌋₊).filter Nat.Prime :=
    Finset.filter_subset_filter _
      (Finset.Icc_subset_Icc_right (Nat.floor_le_floor (Real.exp_le_exp.mpr hst)))
  have hdiff := Finset.sum_sdiff (f := fun p : ℕ => 1 / (p : ℝ)) hsub
  have hCt : C / t ≤ C / s := div_le_div_of_nonneg_left hC hs0 hst
  have e : 2 * C / s = C / s + C / s := by ring
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le, e]
  constructor
  · linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  · linarith [h1'.1, h1'.2, h2'.1, h2'.2]

/-- **The mass of a dyadic band of primes** (`[P-02:0060–0064]`, (eq:band-mass)), from Mertens'
estimate for `∑ 1/p`. -/
theorem dyadicPrimeMass_of_mertensReciprocal (hM : MertensReciprocal) : DyadicPrimeMass := by
  obtain ⟨C, hC, hwin⟩ := exists_reciprocal_window hM
  intro δ hδ
  refine ⟨2 + (1 + 2 * C) / δ, fun y hy T hT1 hT2 => ?_⟩
  have hc0 : 0 ≤ (1 + 2 * C) / δ := div_nonneg (by linarith) hδ.le
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  have hδy : (1 + 2 * C) / (y - 1) ≤ δ := by
    have h1 : (1 + 2 * C) / δ ≤ y - 1 := by linarith
    have h2 : 1 + 2 * C ≤ (y - 1) * δ := (div_le_iff₀ hδ).mp h1
    rw [div_le_iff₀ hy1, mul_comm δ (y - 1)]
    exact h2
  have e : (1 + 2 * C) / (y - 1) = 1 / (y - 1) + 2 * C / (y - 1) := add_div _ _ _
  have hlog : Real.log (2 * y) = Real.log 2 + Real.log y :=
    Real.log_mul two_ne_zero hy0.ne'
  -- upper bound: `T` is inside the window `(exp (y - 1), exp (2y)]`
  have hup : reciprocalMass T ≤ Real.log 2 + δ := by
    have hsub : T ⊆ (Finset.Icc 2 ⌊Real.exp (2 * y)⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp (y - 1)⌋₊).filter Nat.Prime := by
      intro p hp
      obtain ⟨hpp, hlo, hhi⟩ := hT1 p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, Nat.le_floor hhi⟩, hpp⟩, fun h => ?_⟩
      have h0 : p ≤ ⌊Real.exp (y - 1)⌋₊ := (Finset.mem_Icc.mp (Finset.mem_filter.mp h).1).2
      have h1 : (p : ℝ) ≤ Real.exp (y - 1) :=
        (Nat.cast_le.mpr h0).trans (Nat.floor_le (Real.exp_pos _).le)
      have h2 : Real.exp (y - 1) < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hle : reciprocalMass T ≤
        ∑ p ∈ (Finset.Icc 2 ⌊Real.exp (2 * y)⌋₊).filter Nat.Prime \
          (Finset.Icc 2 ⌊Real.exp (y - 1)⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
      unfold reciprocalMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    have hw := abs_le.mp (hwin (y - 1) (2 * y) (by linarith) (by linarith))
    have hpred : Real.log y - Real.log (y - 1) ≤ 1 / (y - 1) :=
      log_sub_log_pred_le (by linarith)
    linarith [hw.2]
  -- lower bound: `T` contains the window `(exp y, exp (2y - 1)]`
  have hlow : Real.log 2 - δ ≤ reciprocalMass T := by
    have hsub : (Finset.Icc 2 ⌊Real.exp (2 * y - 1)⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp y⌋₊).filter Nat.Prime ⊆ T := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hp3, hpp⟩ := Finset.mem_filter.mp hp1
      have hhi : (p : ℝ) ≤ Real.exp (2 * y - 1) :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp hp3).2).trans (Nat.floor_le (Real.exp_pos _).le)
      have hlt : Real.exp (2 * y - 1) < Real.exp (2 * y) := Real.exp_lt_exp.mpr (by linarith)
      have hfl : ⌊Real.exp y⌋₊ < p := by
        by_contra hcon
        rw [not_lt] at hcon
        exact hp2 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, hcon⟩, hpp⟩)
      exact hT2 p hpp (Nat.lt_of_floor_lt hfl) (lt_of_le_of_lt hhi hlt)
    have hle : (∑ p ∈ (Finset.Icc 2 ⌊Real.exp (2 * y - 1)⌋₊).filter Nat.Prime \
        (Finset.Icc 2 ⌊Real.exp y⌋₊).filter Nat.Prime, 1 / (p : ℝ)) ≤ reciprocalMass T := by
      unfold reciprocalMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
    have hw := abs_le.mp (hwin y (2 * y - 1) (by linarith) (by linarith))
    have hpred : Real.log (2 * y) - Real.log (2 * y - 1) ≤ 1 / (2 * y - 1) :=
      log_sub_log_pred_le (by linarith)
    have h1 : 1 / (2 * y - 1) ≤ 1 / (y - 1) := one_div_le_one_div_of_le hy1 (by linarith)
    have h2 : 2 * C / y ≤ 2 * C / (y - 1) :=
      div_le_div_of_nonneg_left (by linarith) hy1 (by linarith)
    linarith [hw.1]
  rw [abs_le]
  constructor
  · linarith
  · linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

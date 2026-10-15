module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CandidateAdmissibleProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound

/-!
# The success coins: the probabilities are at most one

`[P-07:0397–0399]`: "The constant `c₁ > 0` is fixed sufficiently small, depending on `j, q₀` and
the bounds for `V_g`, that these probabilities are at most one."

* `eventually_candidate_mass_ge`: every candidate group has reciprocal mass `≥ (log 2)/2` for
  large `x` (Mertens' sum on one dyadic band).
* `eventually_coinProb_le_one`: for `0 ≤ q₀ < 1`, `j ≥ 1` and
  `0 ≤ c₁ ≤ ((1 - q₀)(log 2)/2)²`, the success probabilities `s_g(u, u + 1)` of
  (ext:success-probability) are at most one for large `x`, for all `u` and all groups `g`. This
  is the first clause of `CoinFailure q₀`.
* `coinFailure_of_mass`: `CoinFailure q₀` follows from its second clause for one such `c₁`
  (`CoinFailureMass q₀`).

The second clause (the failure mass is `o(x/L)`, `[P-07:0404–0514]`) is NOT proved here; neither
is `CoinLink q₀`. The hypothesis `q₀ < 1` cannot be removed from the first clause: for `q₀ ≥ 1`
the factor `q₀^{ω - 1} ω / V_g` is unbounded in `u`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

open Filter

noncomputable section

/-- Every candidate group has reciprocal mass at least `(log 2)/2` for large `x`. -/
theorem eventually_candidate_mass_ge (hM : MertensReciprocal) :
    ∀ᶠ x : ℝ in atTop, ∀ g : (candidateGroups x).Index,
      Real.log 2 / 2 ≤ reciprocalMass ((candidateGroups x).group g) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Y₀, hY⟩ :=
    dyadicPrimeMass_of_mertensReciprocal hM (Real.log 2 / 2) (half_pos hlog2)
  have h1 : ∀ᶠ x : ℝ in atTop, Y₀ ≤ Real.log x ^ (0.28 : ℝ) :=
    ((tendsto_rpow_atTop (show (0 : ℝ) < 0.28 by norm_num)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop Y₀
  filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hY1 hL g
  have hL0 : 0 ≤ Real.log x := by linarith
  have h28 : Real.log x ^ (0.28 : ℝ) ≤ Real.log x ^ (0.4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  rcases g with i | i
  · have h := (abs_le.mp (candidateBand_mass hY hL0 hY1 i.val)).1
    have e : (candidateGroups x).group (Sum.inl i) = candidateBand 0.28 x i.val := rfl
    rw [e]
    linarith
  · have h := (abs_le.mp (candidateBand_mass hY hL0 (hY1.trans h28) i.val)).1
    have e : (candidateGroups x).group (Sum.inr i) = candidateBand 0.4 x i.val := rfl
    rw [e]
    linarith

/-- **The success probabilities are at most one** (`[P-07:0397–0399]`): the first clause of
`CoinFailure q₀`, for every `0 ≤ c₁ ≤ ((1 - q₀)(log 2)/2)²`. -/
theorem eventually_coinProb_le_one (hM : MertensReciprocal) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j) {c₁ : ℝ}
    (hc₁ : c₁ ≤ ((1 - q₀) * (Real.log 2 / 2)) ^ 2) :
    ∀ᶠ x : ℝ in atTop, ∀ (u : ℕ) (g : (candidateGroups x).Index),
      coinProb (candidateGroups x) c₁ q₀ j u g ≤ 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 < Real.log 2 / 2 := half_pos hlog2
  have h1q : 0 < 1 - q₀ := by linarith
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hqj0 : 0 ≤ q₀ / (j : ℝ) := div_nonneg hq₀ (by linarith)
  have hqj : q₀ / (j : ℝ) ≤ q₀ := div_le_self hq₀ hj1
  have hqj1 : q₀ / (j : ℝ) < 1 := lt_of_le_of_lt hqj hq₀1
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = (1 - q₀) * (Real.log 2 / 2) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact mul_pos h1q hv
  rw [← hκdef] at hc₁
  filter_upwards [eventually_candidate_mass_ge hM] with x hmass u g
  have h1 : markFactor q₀ ((candidateGroups x).group g) u ≤ 1 / κ := by
    rw [hκdef]
    exact markFactor_le_of_mass_ge hq₀ hq₀1 hv (hmass g) u
  have h2 : markFactor (q₀ / (j : ℝ)) ((candidateGroups x).group g) (u + 1) ≤ 1 / κ := by
    refine (markFactor_le_of_mass_ge hqj0 hqj1 hv (hmass g) (u + 1)).trans ?_
    rw [hκdef]
    exact one_div_le_one_div_of_le (mul_pos h1q hv)
      (mul_le_mul_of_nonneg_right (by linarith) hv.le)
  have h10 := markFactor_nonneg hq₀ ((candidateGroups x).group g) u
  have h20 := markFactor_nonneg hqj0 ((candidateGroups x).group g) (u + 1)
  have hκ0 : 0 ≤ 1 / κ := (one_div_pos.mpr hκ).le
  unfold coinProb
  by_cases hc0 : 0 ≤ c₁
  · calc c₁ * markFactor q₀ ((candidateGroups x).group g) u *
          markFactor (q₀ / (j : ℝ)) ((candidateGroups x).group g) (u + 1)
        ≤ κ ^ 2 * (1 / κ) * (1 / κ) :=
          mul_le_mul (mul_le_mul hc₁ h1 h10 (sq_nonneg κ)) h2 h20
            (mul_nonneg (sq_nonneg κ) hκ0)
      _ = κ * (1 / κ) * (κ * (1 / κ)) := by ring
      _ = 1 := by rw [mul_one_div_cancel hκ.ne', mul_one]
  · have hneg : c₁ * markFactor q₀ ((candidateGroups x).group g) u *
        markFactor (q₀ / (j : ℝ)) ((candidateGroups x).group g) (u + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hc0).le h10) h20
    linarith

/-- The second clause of `CoinFailure q₀` for one `c₁` to which `eventually_coinProb_le_one`
applies: the outcomes with fewer than `c₂ log L` successes in either family have weighted mass
`o(x/L)` (`[P-07:0404–0407]`). This is what remains of the coin step. -/
def CoinFailureMass (q₀ : ℝ) : Prop :=
  ∀ Φ : ℝ → ℝ, IsCutoff Φ → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ j : ℕ, 2 ≤ j →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ ((1 - q₀) * (Real.log 2 / 2)) ^ 2 ∧ 0 < c₂ ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ x : ℝ in atTop,
        shiftSum Φ x (fun _ => True)
            (fun u => |convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
              failedMass (candidateGroups x) c₁ c₂ q₀ j x u|) ≤
          η * (x / Real.log x)

/-- `CoinFailure q₀` from its second clause, for `0 ≤ q₀ < 1`. -/
theorem coinFailure_of_mass (hM : MertensReciprocal) {q₀ : ℝ} (hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1)
    (h : CoinFailureMass q₀) : CoinFailure q₀ := by
  intro Φ hΦ γ hγ hγ1 j hj
  obtain ⟨c₁, c₂, hc₁, hc₁', hc₂, hmass⟩ := h Φ hΦ γ hγ hγ1 j hj
  exact ⟨c₁, c₂, hc₁, hc₂,
    eventually_coinProb_le_one hM hq₀ hq₀1 (le_trans (by norm_num) hj) hc₁', hmass⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

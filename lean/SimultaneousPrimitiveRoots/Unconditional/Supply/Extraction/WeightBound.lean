module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.DyadicMass

/-!
# The array weight is bounded

`arrayWeightBounded_of_mertensReciprocal : MertensReciprocal → ArrayWeightBounded q` for
`0 ≤ q < 1` (`[P-07:0043–0045]`, `[P-03:0027–0035]`): "since `V_i = log 2 + o(1)` and
`sup_n n q^{n-1} < ∞`, these weights are bounded by a constant depending only on `K, q`, for
large `x`". This is the field `weightBounded` of `ExtractionOpenLeaves` (and of
`ExtractionLeaves`), and the hypothesis of `TwoSidedProof.corePowerBounded_one`.

* `pow_pred_mul_le`: `k q^{k-1} ≤ 1/(1-q)` for every `k` (the truncated exponent makes the left
  side `0` at `k = 0`), because `k q^{k-1} ≤ 1 + q + ⋯ + q^{k-1} = (1 - q^k)/(1 - q)`.
* `markFactor_le_of_mass_ge`: if `V_S ≥ v > 0` then `q^{ω_S(n)-1} ω_S(n)/V_S ≤ 1/((1-q) v)`.
* The band mass: `DyadicPrimeMass` at `y = L^{a_i}` with the precision `δ = (log 2)/2` gives
  `V_i ≥ (log 2)/2` once `L^{a_i} ≥ Y₀`, which holds for large `x` because `a_i > 0`.

The bound is `C = (2 / ((1 - q) log 2))^K`; it depends on `K` and `q` only, and the threshold for
`x` depends on the array, as in the statement.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- `k q^{k-1} ≤ 1/(1-q)` for `0 ≤ q < 1` and every natural `k` (`sup_n n q^{n-1} < ∞`,
`[P-07:0044]`). -/
theorem pow_pred_mul_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    q ^ (k - 1) * (k : ℝ) ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hsum : (k : ℝ) * q ^ (k - 1) ≤ ∑ i ∈ Finset.range k, q ^ i :=
    calc (k : ℝ) * q ^ (k - 1) = ∑ _i ∈ Finset.range k, q ^ (k - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range k, q ^ i :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_of_le_one hq0 hq1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
  have hgeom : (∑ i ∈ Finset.range k, q ^ i) * (1 - q) = 1 - q ^ k := geom_sum_mul_neg q k
  have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
  rw [le_div_iff₀ h1q, mul_comm (q ^ (k - 1)) (k : ℝ)]
  calc (k : ℝ) * q ^ (k - 1) * (1 - q) ≤ (∑ i ∈ Finset.range k, q ^ i) * (1 - q) :=
        mul_le_mul_of_nonneg_right hsum h1q.le
    _ = 1 - q ^ k := hgeom
    _ ≤ 1 := by linarith

/-- One group factor is at most `1/((1-q) v)` when the reciprocal mass of the group is at least
`v > 0`. -/
theorem markFactor_le_of_mass_ge {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {S : Finset ℕ} {v : ℝ}
    (hv : 0 < v) (hS : v ≤ reciprocalMass S) (n : ℕ) :
    markFactor q S n ≤ 1 / ((1 - q) * v) := by
  have h1q : 0 < 1 - q := by linarith
  have hnum : q ^ (primeHits S n - 1) * (primeHits S n : ℝ) ≤ 1 / (1 - q) :=
    pow_pred_mul_le hq0 hq1 _
  have hV : 0 < reciprocalMass S := lt_of_lt_of_le hv hS
  unfold markFactor
  calc q ^ (primeHits S n - 1) * (primeHits S n : ℝ) / reciprocalMass S
      ≤ 1 / (1 - q) / reciprocalMass S := div_le_div_of_nonneg_right hnum hV.le
    _ ≤ 1 / (1 - q) / v := div_le_div_of_nonneg_left (one_div_pos.mpr h1q).le hv hS
    _ = 1 / ((1 - q) * v) := div_div _ _ _

/-- **The array weight is bounded**, from the band masses: `|𝒲(n)| ≤ (2/((1-q) log 2))^K` once
every band mass is at least `(log 2)/2`. -/
theorem arrayWeightBounded_of_dyadicPrimeMass {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hD : DyadicPrimeMass) : ArrayWeightBounded q := by
  intro K
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hv : 0 < Real.log 2 / 2 := half_pos hlog2
  obtain ⟨Y₀, hY₀⟩ := hD (Real.log 2 / 2) hv
  refine ⟨(1 / ((1 - q) * (Real.log 2 / 2))) ^ K, fun 𝔞 => ?_⟩
  have hev : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, Y₀ ≤ Real.log x ^ 𝔞.exponent i := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hpos : (0 : ℝ) < 𝔞.exponent i := lt_trans (by norm_num) (𝔞.gt_tenth i)
    exact ((tendsto_rpow_atTop hpos).comp Real.tendsto_log_atTop).eventually_ge_atTop Y₀
  filter_upwards [hev] with x hx n
  have hmass : ∀ i : Fin K, Real.log 2 / 2 ≤ reciprocalMass (bandPrimes (𝔞.exponent i) x) := by
    intro i
    have h := hY₀ (Real.log x ^ 𝔞.exponent i) (hx i) (bandPrimes (𝔞.exponent i) x)
      (fun p hp => mem_bandPrimes.mp hp)
      (fun p hpp hlo hhi => mem_bandPrimes.mpr ⟨hpp, hlo.le, hhi.le⟩)
    have h' := (abs_le.mp h).1
    linarith
  have hnn : 0 ≤ markedWeight q 𝔞 x n := markedWeight_nonneg hq0 𝔞 x n
  rw [abs_of_nonneg hnn]
  unfold markedWeight
  calc ∏ i, markFactor q (bandPrimes (𝔞.exponent i) x) n
      ≤ ∏ _i : Fin K, 1 / ((1 - q) * (Real.log 2 / 2)) :=
        Finset.prod_le_prod (fun i _ => markFactor_nonneg hq0 _ n)
          (fun i _ => markFactor_le_of_mass_ge hq0 hq1 hv (hmass i) n)
    _ = (1 / ((1 - q) * (Real.log 2 / 2))) ^ K := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The array weight is bounded** (`[P-07:0043–0045]`), from Mertens' estimate for `∑ 1/p`.
For `0 < q < 1` this is the field `weightBounded` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem arrayWeightBounded_of_mertensReciprocal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hM : MertensReciprocal) : ArrayWeightBounded q :=
  arrayWeightBounded_of_dyadicPrimeMass hq0 hq1 (dyadicPrimeMass_of_mertensReciprocal hM)

/-- The form used by `TwoSidedProof.corePowerBounded_one`: the array weight is bounded for every
damping `0 < q < 1`. -/
theorem arrayWeightBounded_all (hM : MertensReciprocal) :
    ∀ q : ℝ, 0 < q → q < 1 → ArrayWeightBounded q :=
  fun _ hq0 hq1 => arrayWeightBounded_of_mertensReciprocal hq0.le hq1 hM

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

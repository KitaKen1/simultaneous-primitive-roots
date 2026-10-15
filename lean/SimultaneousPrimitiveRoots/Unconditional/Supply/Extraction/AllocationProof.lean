module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationSum

/-!
# The allocation step (ext:correlation-to-use)

`allocationLink d H b hb hq hq1 hq₀ hq₀1 : AllocationLink d H b q q₀` (`[P-07:0518–0615]`, with the
class of `[PUB-tex:0527–0530]`), for `b.Coprime H`, `0 < q < 1`, `0 < q₀ < 1` and every number of
slots: the field `allocation` of `ExtractionOpenLeaves d H b q q₀`.

Fix `ε, Φ, γ, K, 𝔞, j ≥ 2, c₁, c₂ > 0` and `η > 0`; let `𝒞` be the candidate groups at `x` and
`N = |𝒞| ≤ (2/log 2) log L`.

* `Allocation.abs_shiftSum_retained_le`: the retained coin mass is a signed sum of at most `4^N`
  products `∏_{g ∈ P} s_g`, `P = S ∪ T` (ext:active-term), and every `P` has at least `c₂ log L`
  groups of each kind.
* `CandidateAdmissible`: every such `P` is an admissible system for the constants `Pc`, and all
  candidate primes are primes above `W`.
* `Allocation.abs_shiftSum_coinProd_le`: for one `P`, with `n = |P|`, `D = 1/((1-q₀) v₋)`,
  `|∑ …| ≤ c₁^n (j^n x M L^{-A} + B D^{2n} (1 + j^n) L^{C₊} x L^{-A})`. The first term is `j^n`
  times `x` times the sum of Theorem 6.1^{𝔅} with `Ψ(y) = y Φ(y)` and the allocation core `G_P`
  (`AllocationIdentity`, `CoreGrowth`, `allocationCore_coreInvariant`); the second is the
  contribution of the square exceptions (`SquareExceptions` with the divisor power `k = ⌈C⌉₊`,
  `CoreBounded`, `CoreGrowth` once more for the number of factor tuples).
* The fixed costs: with `a = max(1, c₁, j, D)` every term is at most
  `a^{4N} x L^{-A} L^{C₊} (|M| + 2B)`, the `4^N` terms cost `(4a⁴)^N ≤ L^{e₀}`,
  `e₀ = (2/log 2) log(4a⁴)`, and `A = e₀ + C₊ + 2` is chosen before `M` (`[P-07:0610–0612]`:
  "Choose `A` after the fixed costs from `3^{|𝒞|}`, `j^{s_P}`, and the coefficients").

The hypothesis `0 < H` is not needed. `b.Coprime H` identifies the joint factor `𝓑_{H,b}(u, u+1)`
with the class `u + 1 ≡ b (mod H)` (`twoSidedSum_classWeight`); `0 < q < 1` and `0 < q₀ < 1` are
the hypotheses of Theorem 6.1^{𝔅}, and `q₀ < 1` also bounds the marked factors.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

open Allocation in
/-- **The allocation step** (`[P-07:0518–0615]`): Theorem 6.1^{𝔅} for the class weight, the
admissibility of the active sets, (ext:core-bound), the allocation identity, the square exceptions
and the bounded endpoint give the bound `o(x/L)` for the retained outcomes. -/
theorem allocationLink (d H b : ℕ) (hb : b.Coprime H) {q q₀ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) : AllocationLink d H b q q₀ := by
  intro h61 hCand hGrow hId hSq hCore ε hε Φ hΦ γ hγ _hγ1 K 𝔞 j hj c₁ c₂ hc₁ hc₂ η hη
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨hcandP, hadm⟩ := hCand
  obtain ⟨Pc, hPc⟩ := hadm c₂ hc₂
  obtain ⟨C, hC⟩ := hGrow γ hγ j
  obtain ⟨B, hB0, hB⟩ := hCore ε hε R hR0 K
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1q : 0 < 1 - q₀ := by linarith
  -- the fixed costs: `D` bounds one marked factor, `a` all the bases, `e₀` the total exponent
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 1 / ((1 - q₀) * Pc.vlo) := ⟨_, rfl⟩
  have hD0 : 0 < D := by
    rw [hDdef]
    exact one_div_pos.mpr (mul_pos h1q Pc.vlo_pos)
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = max 1 (max c₁ (max (j : ℝ) D)) := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [hadef]
    exact le_max_left _ _
  have hca : c₁ ≤ a := by
    rw [hadef]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hja : (j : ℝ) ≤ a := by
    rw [hadef]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hDa : D ≤ a := by
    rw [hadef]
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hbase : (1 : ℝ) ≤ 4 * a ^ 4 := by
    have h : (1 : ℝ) ≤ a ^ 4 := one_le_pow₀ ha1
    linarith
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℝ, e₀ = 2 / Real.log 2 * Real.log (4 * a ^ 4) := ⟨_, rfl⟩
  have he₀0 : 0 ≤ e₀ := by
    rw [he₀]
    exact mul_nonneg (div_nonneg zero_le_two hlog2.le) (Real.log_nonneg hbase)
  -- the saving `A` is chosen after the fixed costs, and before the constant of Theorem 6.1
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = e₀ + max C 0 + 2 := ⟨_, rfl⟩
  have hA : 0 < A := by
    have h := le_max_right C 0
    rw [hAdef]
    linarith
  obtain ⟨M, x₀, h61'⟩ := h61 ε hε q q₀ hq hq1 hq₀ hq₀1 K 𝔞 Pc C (mulCutoff Φ)
    (mulCutoff_contDiff hΦ) (mulCutoff_hasCompactSupport hΦ) (mulCutoff_tsupport_subset hΦ) A hA
  filter_upwards [hcandP, hPc, hC, hB 𝔞, hSq Φ hΦ ⌈C⌉₊ A hA, eventually_ge_atTop x₀,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop ((|M| + 2 * B) / η),
    eventually_gt_atTop (0 : ℝ)] with x hx1 hx2 hx3 hx4 hx5 hx6 hL hLη hx0 S hS
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL
  have hLA : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hLC : 0 ≤ Real.log x ^ max C 0 := Real.rpow_nonneg hL0.le _
  have hFb : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |centeredCore q 𝔞 x S u| ≤ B := fun u hu =>
    hx4 S hS u (hΦ.range_of_ne_zero hR hx0 hu).1 (hΦ.range_of_ne_zero hR hx0 hu).2
  -- the number of candidate groups
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = (candidateGroups x).numGroups := ⟨_, rfl⟩
  have hNle : (N : ℝ) ≤ 2 / Real.log 2 * Real.log (Real.log x) := by
    rw [hNdef]
    exact candidateGroups_numGroups_le hL
  have hT1 : 1 ≤ a ^ N := one_le_pow₀ ha1
  have hX0 : 0 ≤ x * (|M| * Real.log x ^ (-A)) :=
    mul_nonneg hx0.le (mul_nonneg (abs_nonneg M) hLA)
  have hY0 : 0 ≤ Real.log x ^ max C 0 * (x * Real.log x ^ (-A)) :=
    mul_nonneg hLC (mul_nonneg hx0.le hLA)
  -- one active set
  have hterm : ∀ P : Finset (candidateGroups x).Index,
      c₂ * Real.log (Real.log x) ≤ (P.toLeft.card : ℝ) →
      c₂ * Real.log (Real.log x) ≤ (P.toRight.card : ℝ) →
        |shiftSum Φ x (fun v => v ≡ b [MOD H])
          (fun u => centeredCore q 𝔞 x S u *
            convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1) *
              ∏ g ∈ P, coinProb (candidateGroups x) c₁ q₀ j u g)| ≤
          (a ^ N) ^ 4 * (x * (|M| * Real.log x ^ (-A)) +
            2 * B * (Real.log x ^ max C 0 * (x * Real.log x ^ (-A)))) := by
    intro P hPl hPr
    have hadmP := hx2 P hPl hPr
    have hPN : P.card ≤ N := by
      rw [hNdef, ← card_index]
      exact Finset.card_le_univ P
    have h := abs_shiftSum_coinProd_le hΦ hR hx0 hL hId hb hq₀.le hq₀1 𝔞 S (j := j) (c₁ := c₁)
      (Mb := |M| * Real.log x ^ (-A)) (by omega) hc₁.le hB0 hx1 hx3 hFb hx5 P hadmP
      (fun G hG => (h61' x hx6 _ hadmP S hS G hG).trans
        (mul_le_mul_of_nonneg_right (le_abs_self M) hLA))
    rw [← hDdef] at h
    exact h.trans (term_algebra (pow_le_pow_of_le hc₁.le hca ha1 hPN)
      (pow_nonneg (Nat.cast_nonneg j) _) (pow_le_pow_of_le (Nat.cast_nonneg j) hja ha1 hPN)
      (pow_nonneg hD0.le _) (pow_le_pow_of_le hD0.le hDa ha1 hPN) hT1 hX0 hY0 hB0)
  -- the sum over the active sets
  have hE0 : 0 ≤ (a ^ N) ^ 4 * (x * (|M| * Real.log x ^ (-A)) +
      2 * B * (Real.log x ^ max C 0 * (x * Real.log x ^ (-A)))) :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one hT1) _)
      (add_nonneg hX0 (mul_nonneg (mul_nonneg zero_le_two hB0) hY0))
  have hret := abs_shiftSum_retained_le hR hx0 (fun v => v ≡ b [MOD H]) (candidateGroups x)
    c₁ c₂ q₀ j
    (fun u => centeredCore q 𝔞 x S u *
      convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1)) hE0 hterm
  rw [← hNdef] at hret
  -- the choice of `A`
  have hT4 : (4 : ℝ) ^ N * (a ^ N) ^ 4 ≤ Real.log x ^ e₀ := by
    have e : (4 : ℝ) ^ N * (a ^ N) ^ 4 = (4 * a ^ 4) ^ N := by
      rw [mul_pow, pow_right_comm]
    rw [e, he₀]
    exact pow_le_rpow_log hbase hL0 hNle
  exact hret.trans
    (final_arith hx0 hL hη (abs_nonneg M) hB0 (le_max_right C 0) hAdef hT4 hLη)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

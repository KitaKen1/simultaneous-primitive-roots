module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BlockInsertion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (eq:rank-coefficient-count): the total absolute coefficient of the collections of rank `r`

Source: `verification/stage7-sources/S-02.tex`, lines 1095–1105 (`[S-02:1095–1105]`).

`rankCoefficientCount : RankCoefficientCount` is proved here: for a finite set `I` of `A_*`
addresses and every `r`,
`∑_{r(π) = r} |μ(π)| ≤ A_*^{2r}`.

The paper: "the unsigned cycle generating polynomial on `A_*` addresses is
`∏_{j=0}^{A_*-1} (1 + jt)`, where the power of `t` is the sum of cycle lengths minus the number of
cycles. Its coefficient of `t^r` is at most `(∑_j j)^r / r! ≤ A_*^{2r}`."

The left side, restricted to the collections inside a set `s` of `n` addresses, is `rankSum s r`;
it is the unsigned Stirling number of the first kind `c(n, n - r)`. The factorization of the
generating polynomial is the recursion

`rankSum (s ∪ {a}) 0 = rankSum s 0`,
`rankSum (s ∪ {a}) (r + 1) = rankSum s (r + 1) + |s| · rankSum s r`

(`rankSum_insert_zero`, `rankSum_insert_succ`; multiplication by the factor `1 + |s| t`), which is
the insertion step `sum_blockColl_insert` of `BlockInsertion.lean`: the new address is a fixed
point, or it is inserted behind one of the `|s|` old addresses, which raises the rank by one. The
bound `rankSum s r ≤ |s|^{2r}` follows by induction (`rankSum_le`):
`n^{2r+2} + n · n^{2r} ≤ (n + 1)^{2r+2}`. For `s = ∅`, `r = 0` both sides are `1`
(`0^0 = 1`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section RankCount

variable {I : Type}

/-- `∑_{π inside s, r(π) = r} |μ(π)|`: the total absolute coefficient of the collections of rank
`r` inside the set `s` of addresses. -/
def rankSum (s : Finset I) (r : ℕ) : ℤ :=
  ∑ π ∈ blockColl s, if blockRank π = r then |blockMu π| else 0

theorem rankSum_empty (r : ℕ) :
    rankSum (∅ : Finset I) r = if r = 0 then 1 else 0 := by
  have h0 : blockRank (∅ : Finset (Finset I)) = 0 := by
    unfold blockRank
    exact Finset.sum_empty
  have h1 : blockMu (∅ : Finset (Finset I)) = 1 := by
    unfold blockMu
    exact Finset.prod_empty
  unfold rankSum
  rw [blockColl_empty, Finset.sum_singleton, h0, h1, abs_one]
  by_cases hr : r = 0
  · rw [if_pos hr, if_pos hr.symm]
  · rw [if_neg hr, if_neg fun h => hr h.symm]

/-- The scalar inequality of the induction: `A n² + n A ≤ B (n + 1)²` for `0 ≤ A ≤ B`,
`n ≥ 0`. -/
theorem rank_scalar (n A B : ℤ) (hn : 0 ≤ n) (hA : 0 ≤ A) (hAB : A ≤ B) :
    A * n ^ 2 + n * A ≤ B * (n + 1) ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_right hAB (sq_nonneg (n + 1)), mul_nonneg hA hn]

variable [DecidableEq I]

/-- A new address does not change the number of collections of rank `0` (the empty
collection). -/
theorem rankSum_insert_zero {a : I} {s : Finset I} (ha : a ∉ s) :
    rankSum (insert a s) 0 = rankSum s 0 := by
  unfold rankSum
  rw [sum_blockColl_insert ha]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hX : ∀ X ∈ blockParts s π,
      (if blockRank (blockIns a π X) = 0 then |blockMu (blockIns a π X)| else 0) = 0 := by
    intro X hX
    refine if_neg ?_
    rw [blockRank_blockIns ha hπ hX]
    exact Nat.add_one_ne_zero _
  rw [Finset.sum_congr rfl hX, Finset.sum_const_zero, add_zero]

/-- **The recursion of the unsigned Stirling numbers of the first kind**: a new address is a fixed
point, or it is inserted behind one of the `|s|` old addresses, which raises the rank by one. -/
theorem rankSum_insert_succ {a : I} {s : Finset I} (ha : a ∉ s) (r : ℕ) :
    rankSum (insert a s) (r + 1) = rankSum s (r + 1) + (s.card : ℤ) * rankSum s r := by
  unfold rankSum
  rw [sum_blockColl_insert ha, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hX : ∀ X ∈ blockParts s π,
      (if blockRank (blockIns a π X) = r + 1 then |blockMu (blockIns a π X)| else 0) =
        (if blockRank π = r then |blockMu π| else 0) * ∑ i ∈ X, (1 : ℤ) := by
    intro X hX
    have hcard : ∑ i ∈ X, (1 : ℤ) = (X.card : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have habs : |blockMu (blockIns a π X)| = (X.card : ℤ) * |blockMu π| := by
      rw [blockMu_blockIns ha hπ hX, abs_mul, abs_neg, Nat.abs_cast]
    rw [hcard, habs, blockRank_blockIns ha hπ hX]
    by_cases hr : blockRank π = r
    · have hr' : blockRank π + 1 = r + 1 := by rw [hr]
      rw [if_pos hr, if_pos hr']
      ring
    · have hr' : ¬blockRank π + 1 = r + 1 := fun h => hr (by omega)
      rw [if_neg hr, if_neg hr', zero_mul]
  have hone : ∑ X ∈ blockParts s π, ∑ i ∈ X, (1 : ℤ) = (s.card : ℤ) := by
    rw [sum_blockParts hπ, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hX, ← Finset.mul_sum, hone]
  ring

/-- **(eq:rank-coefficient-count) for the addresses of a set `s`**:
`∑_{π inside s, r(π) = r} |μ(π)| ≤ |s|^{2r}`. -/
theorem rankSum_le (s : Finset I) : ∀ r : ℕ, rankSum s r ≤ (s.card : ℤ) ^ (2 * r) := by
  induction s using Finset.induction_on with
  | empty =>
    intro r
    rw [rankSum_empty, Finset.card_empty]
    by_cases hr : r = 0
    · subst hr
      simp
    · rw [if_neg hr]
      exact pow_nonneg (Nat.cast_nonneg _) _
  | insert a s ha ih =>
    intro r
    rw [Finset.card_insert_of_notMem ha]
    cases r with
    | zero =>
      rw [rankSum_insert_zero ha]
      have h := ih 0
      rw [Nat.mul_zero, pow_zero] at h ⊢
      exact h
    | succ r =>
      rw [rankSum_insert_succ ha]
      have hn : (0 : ℤ) ≤ (s.card : ℤ) := Nat.cast_nonneg _
      have h1 := ih (r + 1)
      have h2 := mul_le_mul_of_nonneg_left (ih r) hn
      have he : 2 * (r + 1) = 2 * r + 2 := by ring
      have hA : (0 : ℤ) ≤ (s.card : ℤ) ^ (2 * r) := pow_nonneg hn _
      have hAB : (s.card : ℤ) ^ (2 * r) ≤ ((s.card : ℤ) + 1) ^ (2 * r) :=
        pow_le_pow_left₀ hn (by linarith) _
      have h3 := rank_scalar (s.card : ℤ) _ _ hn hA hAB
      rw [he, pow_add] at h1
      rw [he, pow_add]
      push_cast
      exact (add_le_add h1 h2).trans h3

end RankCount

open _root_.Classical in
/-- **(eq:rank-coefficient-count)** [S-02:1095–1105]: "its total absolute coefficient, summed over
all collections of rank `r`, obeys `∑_{r(π) = r} |μ(π)| ≤ A_*^{2r}`", `A_*` the number of
addresses. The left side is the unsigned Stirling number of the first kind
`c(A_*, A_* - r)`. -/
theorem rankCoefficientCount : RankCoefficientCount := by
  intro I _ r
  have h := rankSum_le (Finset.univ : Finset I) r
  rw [Finset.card_univ] at h
  refine le_trans (le_of_eq ?_) h
  rw [Finset.sum_filter]
  unfold rankSum
  exact Finset.sum_congr blockColl_univ.symm fun π _ => by split_ifs <;> rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

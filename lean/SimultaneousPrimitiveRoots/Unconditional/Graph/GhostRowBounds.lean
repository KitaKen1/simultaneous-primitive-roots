module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.FiniteGhostReversal
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual indexed ghost weighted row sums

The positive majorant of [S, eq:ghost-row] deletes a subset of the old
zero-hit positions before it inserts an ordered prime tuple. Its weighted
row ratio uses v^(old length - deleted length + born length)/v^old length.
The finite birth cutoff below has an exact binomial/exponential-series
factorization and the bound in [S, eq:ghost-schur-ratios], independent of
the memory and cutoff. This is a
row calculation, not yet the row-to-joint identity or an infinite-space
operator norm theorem.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators
open scoped Topology

variable {I P : Type*} {R : P → Type*}

attribute [local instance] Classical.propDecidable

/-- Old zero-hit positions eligible for deletion; repeated values remain separate. -/
noncomputable def ghostZeroPositions [Fintype I] [∀ p, Zero (R p)]
    (u : I → Σ p, R p) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => (u i).2 = 0)

theorem ghost_zero_positions_card [Fintype I] [∀ p, Zero (R p)]
    (u : I → Σ p, R p) : (ghostZeroPositions u).card = ghostZeroCount u := rfl

/-- Exact auxiliary-weight ratio for deletion followed by birth. -/
theorem ghost_memory_weight_ratio (v : ℝ) (hv : v ≠ 0) (n a b : ℕ) (ha : a ≤ n) :
    v ^ (n - a + b) / v ^ n = v ^ b / v ^ a := by
  apply (div_eq_div_iff (pow_ne_zero _ hv) (pow_ne_zero _ hv)).2
  rw [← pow_add, ← pow_add]
  congr 1
  omega

/-- Birth tuples are summed with prime weights once per position, with repetitions. -/
theorem ghost_birth_tuple_mass [Fintype P] (ν : P → ℝ) (b : ℕ) :
    (∑ q : Fin b → P, ∏ i, ν (q i)) = (∑ p, ν p) ^ b :=
  (Fintype.sum_pow ν b).symm

/-- Positive ghost row ratio with all eligible deletion subsets and b < B births. -/
noncomputable def positiveGhostWeightedRow [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ)
    (u : I → Σ p, R p) (B : ℕ) : ℝ := by
  classical
  exact ∑ s ∈ (ghostZeroPositions u).powerset, ∑ b ∈ Finset.range B,
    (|D| ^ s.card * A ^ (ghostZeroCount u - s.card) * |C| ^ b /
      (b.factorial : ℝ)) * (∑ q : Fin b → P, ∏ i, ν (q i)) *
        v ^ (Fintype.card I - s.card + b) / v ^ Fintype.card I

/-- Pointwise separation of the old-memory and fresh-birth factors. -/
theorem ghost_row_term_factorization (A D C v M : ℝ) (hv : v ≠ 0)
    (n z a b : ℕ) (ha : a ≤ n) :
    (|D| ^ a * A ^ (z - a) * |C| ^ b / (b.factorial : ℝ)) * M ^ b *
      v ^ (n - a + b) / v ^ n =
        (|D| / v) ^ a * A ^ (z - a) * ((|C| * v * M) ^ b / (b.factorial : ℝ)) := by
  rw [mul_div_assoc, ghost_memory_weight_ratio v hv n a b ha, div_pow,
    mul_pow, mul_pow]
  ring

/-- The actual subset sum and ordered birth mass factor exactly, for every cutoff. -/
theorem positive_ghost_weighted_row_eq [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ) (hv : v ≠ 0)
    (u : I → Σ p, R p) (B : ℕ) :
    positiveGhostWeightedRow ν A D C v u B =
      (A + |D| / v) ^ ghostZeroCount u *
        ∑ b ∈ Finset.range B, (|C| * v * (∑ p, ν p)) ^ b / (b.factorial : ℝ) := by
  classical
  unfold positiveGhostWeightedRow
  have hcard : (ghostZeroPositions u).card ≤ Fintype.card I :=
    Finset.card_le_univ _
  calc
    _ = ∑ s ∈ (ghostZeroPositions u).powerset,
        (|D| / v) ^ s.card * A ^ (ghostZeroCount u - s.card) *
          ∑ b ∈ Finset.range B, (|C| * v * (∑ p, ν p)) ^ b / (b.factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [ghost_birth_tuple_mass]
      exact ghost_row_term_factorization A D C v _ hv _ _ _ _
        ((Finset.card_le_card (Finset.mem_powerset.mp hs)).trans hcard)
    _ = _ := by
      rw [← Finset.sum_mul, ← ghost_zero_positions_card,
        Finset.sum_pow_mul_eq_add_pow, add_comm (|D| / v) A]

/-- Positivity of the actual weighted row majorant. -/
theorem positive_ghost_weighted_row_nonneg [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hv : 0 < v) (u : I → Σ p, R p) (B : ℕ) :
    0 ≤ positiveGhostWeightedRow ν A D C v u B := by
  rw [positive_ghost_weighted_row_eq ν A D C v hv.ne' u B]
  have hM : 0 ≤ ∑ p, ν p := Finset.sum_nonneg (fun p _ => hν p)
  have hx : 0 ≤ |C| * v * (∑ p, ν p) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hv.le) hM
  exact mul_nonneg (pow_nonneg (add_nonneg hA (div_nonneg (abs_nonneg _) hv.le)) _)
    (Finset.sum_nonneg (fun b _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)))

/-- The binomial factor is at most one once the auxiliary weight is large enough. -/
theorem positive_ghost_weighted_row_le_exp [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ) (hν : ∀ p, 0 ≤ ν p)
    (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |D| / v ≤ 1)
    (u : I → Σ p, R p) (B : ℕ) :
    positiveGhostWeightedRow ν A D C v u B ≤ Real.exp (|C| * v * ∑ p, ν p) := by
  rw [positive_ghost_weighted_row_eq ν A D C v hv.ne' u B]
  have hM : 0 ≤ ∑ p, ν p := Finset.sum_nonneg (fun p _ => hν p)
  have hx : 0 ≤ |C| * v * (∑ p, ν p) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hv.le) hM
  have hpow : (A + |D| / v) ^ ghostZeroCount u ≤ 1 :=
    pow_le_one₀ (add_nonneg hA (div_nonneg (abs_nonneg _) hv.le)) hbase
  calc
    _ ≤ 1 * Real.exp (|C| * v * ∑ p, ν p) :=
      mul_le_mul hpow (Real.sum_le_exp_of_nonneg hx B)
        (Finset.sum_nonneg (fun b _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)))
        (by positivity)
    _ = _ := one_mul _

/-- One fixed auxiliary weight contracts both the forward and coefficient-swapped row.
It is chosen before the memory, prime masses and birth cutoff. -/
theorem exists_ghost_auxiliary_weight (A D C : ℝ) (hA : A < 1) :
    ∃ v : ℝ, 1 < v ∧ A + |D| / v < 1 ∧ A + |C| / v < 1 := by
  let v : ℝ := 2 + (|D| + |C|) / (1 - A)
  have hden : 0 < 1 - A := by linarith
  have hquot : 0 ≤ (|D| + |C|) / (1 - A) :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hden.le
  have hv : 1 < v := by dsimp [v]; linarith
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  have hmul : v * (1 - A) = 2 * (1 - A) + |D| + |C| := by
    dsimp [v]
    field_simp [hden.ne']
    ring
  refine ⟨v, hv, ?_, ?_⟩
  · have h : |D| / v < 1 - A := (div_lt_iff₀ hvpos).2 (by nlinarith [abs_nonneg C])
    linarith
  · have h : |C| / v < 1 - A := (div_lt_iff₀ hvpos).2 (by nlinarith [abs_nonneg D])
    linarith

/-- A common coefficient bound fixes v before any of the visits or memory lengths. -/
theorem exists_uniform_ghost_auxiliary_weight (Amax dmax cmax : ℝ)
    (hAmax : Amax < 1) (hdmax : 0 ≤ dmax) (hcmax : 0 ≤ cmax) :
    ∃ v : ℝ, 1 < v ∧ ∀ A D C : ℝ,
      A ≤ Amax → |D| ≤ dmax → |C| ≤ cmax →
        A + |D| / v < 1 ∧ A + |C| / v < 1 := by
  obtain ⟨v, hv, hD, hC⟩ := exists_ghost_auxiliary_weight Amax dmax cmax hAmax
  rw [abs_of_nonneg hdmax] at hD
  rw [abs_of_nonneg hcmax] at hC
  refine ⟨v, hv, fun A D C hA hd hc => ?_⟩
  have hvpos : 0 < v := lt_trans zero_lt_one hv
  exact ⟨(add_le_add hA (div_le_div_of_nonneg_right hd hvpos.le)).trans_lt hD,
    (add_le_add hA (div_le_div_of_nonneg_right hc hvpos.le)).trans_lt hC⟩

/-- Coefficient and total prime-mass bounds give a single exponential row constant. -/
theorem positive_ghost_weighted_row_le_uniform_exp [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax Mmax : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbase : A + |D| / v ≤ 1) (hC : |C| ≤ cmax) (hM : ∑ p, ν p ≤ Mmax)
    (u : I → Σ p, R p) (B : ℕ) :
    positiveGhostWeightedRow ν A D C v u B ≤ Real.exp (cmax * v * Mmax) := by
  apply (positive_ghost_weighted_row_le_exp ν A D C v hν hA hv hbase u B).trans
  apply Real.exp_le_exp.mpr
  have hMnonneg : 0 ≤ ∑ p, ν p := Finset.sum_nonneg (fun p _ => hν p)
  have hcmax : 0 ≤ cmax := (abs_nonneg C).trans hC
  calc
    |C| * v * (∑ p, ν p) ≤ cmax * v * (∑ p, ν p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hv.le) hMnonneg
    _ ≤ cmax * v * Mmax := mul_le_mul_of_nonneg_left hM (mul_nonneg hcmax hv.le)

/-- The actual birth sectors are summable, and their sum is the claimed exponential ratio.
This removes the birth cutoff in a single row, while retaining each old position. -/
theorem positive_ghost_weighted_birth_rows_hasSum [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ) (hv : v ≠ 0)
    (u : I → Σ p, R p) :
    HasSum (fun b : ℕ => ∑ s ∈ (ghostZeroPositions u).powerset,
      (|D| ^ s.card * A ^ (ghostZeroCount u - s.card) * |C| ^ b /
        (b.factorial : ℝ)) * (∑ q : Fin b → P, ∏ i, ν (q i)) *
          v ^ (Fintype.card I - s.card + b) / v ^ Fintype.card I)
      ((A + |D| / v) ^ ghostZeroCount u * Real.exp (|C| * v * ∑ p, ν p)) := by
  classical
  have hx : HasSum (fun b : ℕ => (|C| * v * (∑ p, ν p)) ^ b / (b.factorial : ℝ))
      (Real.exp (|C| * v * ∑ p, ν p)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (|C| * v * ∑ p, ν p)
  convert hx.mul_left ((A + |D| / v) ^ ghostZeroCount u) using 1 <;> try rfl
  funext b
  have hcard : (ghostZeroPositions u).card ≤ Fintype.card I := Finset.card_le_univ _
  calc
    _ = ∑ s ∈ (ghostZeroPositions u).powerset,
        (|D| / v) ^ s.card * A ^ (ghostZeroCount u - s.card) *
          ((|C| * v * (∑ p, ν p)) ^ b / (b.factorial : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [ghost_birth_tuple_mass]
      exact ghost_row_term_factorization A D C v _ hv _ _ _ _
        ((Finset.card_le_card (Finset.mem_powerset.mp hs)).trans hcard)
    _ = _ := by
      rw [← Finset.sum_mul, ← ghost_zero_positions_card,
        Finset.sum_pow_mul_eq_add_pow, add_comm (|D| / v) A]

/-- Finite actual row ratios tend to the exponential formula as the birth cutoff grows. -/
theorem positive_ghost_weighted_row_tendsto [Fintype I] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ) (hv : v ≠ 0)
    (u : I → Σ p, R p) :
    Filter.Tendsto (fun B : ℕ => positiveGhostWeightedRow ν A D C v u B)
      Filter.atTop (𝓝 ((A + |D| / v) ^ ghostZeroCount u *
        Real.exp (|C| * v * ∑ p, ν p))) := by
  classical
  have h := (positive_ghost_weighted_birth_rows_hasSum ν A D C v hv u).tendsto_sum_nat
  convert h using 1
  funext B
  unfold positiveGhostWeightedRow
  rw [Finset.sum_comm]

end SimultaneousPrimitiveRoots.Unconditional.Graph

module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedKernel
import Mathlib.Tactic.Ring

/-!
# Exact deletion-cardinality coefficients of ghost rows

The eligible a-position subsets are counted by choose(z,a), where z is the
number of zero positions. Repeated particle values remain distinct positions.
GhostTruncatedRows uses these identities for the full cutoff row estimate;
GhostTruncatedNorm proves its cutoff-independent complex L2 bound.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I P : Type*} {R : P → Type*} {k a b n m : ℕ}

theorem ghost_zero_subset_mem_powerset_card [Fintype I] [∀ p, Zero (R p)]
    (x : I → Σ p, R p) (s : Finset I) (a : ℕ) :
    s ∈ (ghostZeroPositions x).powersetCard a ↔
      s.card = a ∧ ∀ i ∈ s, (x i).2 = 0 := by
  classical
  rw [Finset.mem_powersetCard, ← Finset.mem_powerset, ghost_zero_subset_mem_powerset]
  exact and_comm

/-- Summing the actual deletion coefficients at one counts eligible positions exactly. -/
theorem finite_ghost_subset_coefficient_one_sum [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A : ℝ) (x : Fin (k + a) → Σ p, R p) :
    (∑ s : Finset (Fin (k + a)), finiteGhostSubsetCoefficient ν A
      (fun _ (_ : Fin (k + b) → Σ p, R p) => (1 : ℝ)) s x) =
    (Nat.choose (ghostZeroCount x) a : ℝ) * A ^ (ghostZeroCount x - a) *
      (∑ q : Fin b → P, ∏ i, ν (q i)) := by
  classical
  have hc (s : Finset (Fin (k + a))) :
      finiteGhostSubsetCoefficient ν A
        (fun _ (_ : Fin (k + b) → Σ p, R p) => (1 : ℝ)) s x =
      if s ∈ (ghostZeroPositions x).powersetCard a then
        A ^ (ghostZeroCount x - a) * (∑ q : Fin b → P, ∏ i, ν (q i)) else 0 := by
    rw [finite_ghost_subset_coefficient_one]
    have hp : s ∈ (ghostZeroPositions x).powersetCard a ↔
        s.card = a ∧ s ∈ (ghostZeroPositions x).powerset := by
      rw [Finset.mem_powersetCard, Finset.mem_powerset]
      exact and_comm
    by_cases hs : s.card = a
    · by_cases hz : s ∈ (ghostZeroPositions x).powerset
      · rw [if_pos hs, if_pos hz, if_pos (hp.mpr ⟨hs, hz⟩)]
      · rw [if_pos hs, if_neg hz, if_neg (fun h => hz (hp.mp h).2)]
    · rw [if_neg hs, if_neg (fun h => hs (hp.mp h).1)]
  simp_rw [hc]
  rw [Fintype.sum_ite_mem]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
    ghost_zero_positions_card]
  ring

/-- The exact signed row coefficient for a fixed deletion and birth count. -/
theorem finite_ghost_sector_row_one_exact [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSectorRow ν A D C (fun _ : Fin (k + b) → Σ p, R p => (1 : ℝ)) x =
    (Nat.choose (ghostZeroCount x) a : ℝ) * D ^ a * A ^ (ghostZeroCount x - a) *
      (C * ∑ p, ν p) ^ b / (b.factorial : ℝ) := by
  classical
  unfold finiteGhostSectorRow
  rw [finite_ghost_subset_coefficient_one_sum, ghost_birth_tuple_mass, mul_pow]
  ring

theorem finite_ghost_sector_counting_kernel_row_exact [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C : ℝ)
    (x : Fin (k + a) → Σ p, R p) :
    (∑ y : Fin (k + b) → Σ p, R p, finiteGhostSectorCountingKernel ν A D C x y) =
    (Nat.choose (ghostZeroCount x) a : ℝ) * D ^ a * A ^ (ghostZeroCount x - a) *
      (C * ∑ p, ν p) ^ b / (b.factorial : ℝ) := by
  have h := finite_ghost_sector_counting_kernel_reproduces ν A D C
    (fun _ : Fin (k + b) → Σ p, R p => (1 : ℝ)) (fun _ _ => rfl) x
  simpa only [mul_one, finite_ghost_sector_row_one_exact] using h

theorem ghost_zero_count_degree_equiv_symm [∀ p, Zero (R p)]
    (h : n = m) (y : Fin m → Σ p, R p) :
    ghostZeroCount ((memoryDegreeEquiv h).symm y) = ghostZeroCount y := by
  cases h
  rfl

/-- The actual degree row has the same exact coefficient in original coordinates. -/
theorem finite_ghost_degree_row_one_exact [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (k n m : ℕ) (x : Fin n → Σ p, R p) :
    finiteGhostDegreeRow ν A D C k n m (fun _ => (1 : ℝ)) x =
      if k ≤ n ∧ k ≤ m then
        (Nat.choose (ghostZeroCount x) (n - k) : ℝ) * D ^ (n - k) *
          A ^ (ghostZeroCount x - (n - k)) * (C * ∑ p, ν p) ^ (m - k) /
            ((m - k).factorial : ℝ)
      else 0 := by
  classical
  by_cases hk : k ≤ n ∧ k ≤ m
  · simp only [finiteGhostDegreeRow, dif_pos hk, if_pos hk]
    rw [finite_ghost_sector_row_one_exact, ghost_zero_count_degree_equiv_symm]
  · simp only [finiteGhostDegreeRow, dif_neg hk, if_neg hk]

end SimultaneousPrimitiveRoots.Unconditional.Graph

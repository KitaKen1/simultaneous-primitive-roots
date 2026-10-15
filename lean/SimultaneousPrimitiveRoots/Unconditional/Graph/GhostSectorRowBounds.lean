module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostCountingKernel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual finite ghost sector row and column bounds

The counting kernel's weighted row is a sub-sum of the certified positive
ghost row. Its column uses the proved factorial-mass transpose. Bounds here
are for each fixed k/a/b sector, uniformly in its sizes. Combining all sectors
on a common cutoff and extending to the infinite Fock space remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I P : Type*} {R : P → Type*} {k a b : ℕ}

attribute [local instance] Classical.propDecidable

/-- Eligibility refers to a subset of zero positions, not distinct particle values. -/
theorem ghost_zero_subset_mem_powerset [Fintype I] [∀ p, Zero (R p)]
    (x : I → Σ p, R p) (s : Finset I) :
    s ∈ (ghostZeroPositions x).powerset ↔ ∀ i ∈ s, (x i).2 = 0 := by
  classical
  simp only [Finset.mem_powerset, ghostZeroPositions, Finset.subset_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- Applying an actual subset coefficient to one retains exactly the indexed birth mass. -/
theorem finite_ghost_subset_coefficient_one [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A : ℝ) (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A (fun _ (_ : Fin (k + b) → Σ p, R p) => (1 : ℝ)) s x =
      if s.card = a then if s ∈ (ghostZeroPositions x).powerset then
        A ^ (ghostZeroCount x - a) * (∑ q : Fin b → P, ∏ i, ν (q i)) else 0 else 0 := by
  classical
  unfold finiteGhostSubsetCoefficient
  by_cases hs : s.card = a
  · rw [dif_pos hs, if_pos hs]
    by_cases hx : ∀ i ∈ s, (x i).2 = 0
    · rw [if_pos hx, if_pos ((ghost_zero_subset_mem_powerset x s).mpr hx)]
      simp only [mul_one]
    · rw [if_neg hx,
        if_neg (fun h => hx ((ghost_zero_subset_mem_powerset x s).mp h))]
  · rw [dif_neg hs, if_neg hs]

/-- A fixed deletion/birth sector is a positive sub-sum of the full indexed row ratio. -/
theorem finite_ghost_sector_row_one_le_positive [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v : ℝ) (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSectorRow ν A |D| |C| (fun _ : Fin (k + b) → Σ p, R p => 1) x *
      v ^ (k + b) / v ^ (k + a) ≤ positiveGhostWeightedRow ν A D C v x (b + 1) := by
  classical
  have hm (t : ℕ) : 0 ≤ ∑ q : Fin t → P, ∏ i, ν (q i) :=
    Finset.sum_nonneg (fun q _ => Finset.prod_nonneg (fun i _ => hν (q i)))
  let f : Finset (Fin (k + a)) → ℝ := fun s =>
    ((|D| ^ a * |C| ^ b) / (b.factorial : ℝ) *
      finiteGhostSubsetCoefficient ν A (fun _ (_ : Fin (k + b) → Σ p, R p) => 1) s x) *
        v ^ (k + b) / v ^ (k + a)
  have hrestrict : (∑ s : Finset (Fin (k + a)), f s) =
      ∑ s ∈ (ghostZeroPositions x).powerset, f s := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    dsimp only [f]
    rw [finite_ghost_subset_coefficient_one]
    by_cases hcard : s.card = a
    · rw [if_pos hcard, if_neg hs, mul_zero, zero_mul, zero_div]
    · rw [if_neg hcard, mul_zero, zero_mul, zero_div]
  unfold finiteGhostSectorRow positiveGhostWeightedRow
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  change (∑ s : Finset (Fin (k + a)), f s) ≤ _
  rw [hrestrict]
  apply Finset.sum_le_sum
  intro s hs
  have hsingle :
      ((|D| ^ s.card * A ^ (ghostZeroCount x - s.card) * |C| ^ b /
        (b.factorial : ℝ)) * (∑ q : Fin b → P, ∏ i, ν (q i)) *
          v ^ (Fintype.card (Fin (k + a)) - s.card + b) / v ^ Fintype.card (Fin (k + a))) ≤
      ∑ t ∈ Finset.range (b + 1),
        ((|D| ^ s.card * A ^ (ghostZeroCount x - s.card) * |C| ^ t /
          (t.factorial : ℝ)) * (∑ q : Fin t → P, ∏ i, ν (q i)) *
            v ^ (Fintype.card (Fin (k + a)) - s.card + t) / v ^ Fintype.card (Fin (k + a))) := by
    apply Finset.single_le_sum (a := b)
    · intro t _
      exact div_nonneg (mul_nonneg
        (mul_nonneg (div_nonneg
          (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg D) _) (pow_nonneg hA _))
            (pow_nonneg (abs_nonneg C) _)) (Nat.cast_nonneg _)) (hm t))
        (pow_nonneg hv.le _)) (pow_nonneg hv.le _)
    · exact Finset.mem_range.mpr (Nat.lt_succ_self b)
  dsimp only [f]
  rw [finite_ghost_subset_coefficient_one]
  by_cases hcard : s.card = a
  · rw [if_pos hcard, if_pos hs]
    apply le_trans (le_of_eq ?_) hsingle
    rw [hcard, Fintype.card_fin, Nat.add_sub_cancel_right]
    ring
  · rw [if_neg hcard, mul_zero, zero_mul, zero_div]
    apply Finset.sum_nonneg
    intro t _
    exact div_nonneg (mul_nonneg
      (mul_nonneg (div_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg D) _) (pow_nonneg hA _))
          (pow_nonneg (abs_nonneg C) _)) (Nat.cast_nonneg _)) (hm t))
      (pow_nonneg hv.le _)) (pow_nonneg hv.le _)

/-- The actual finite-sector counting row has the same cutoff-independent exponential bound. -/
theorem finite_ghost_sector_counting_kernel_weighted_row_le_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |D| / v ≤ 1)
    (x : Fin (k + a) → Σ p, R p) :
    (∑ y : Fin (k + b) → Σ p, R p,
      finiteGhostSectorCountingKernel ν A |D| |C| x y * v ^ (k + b) / v ^ (k + a)) ≤
        Real.exp (|C| * v * ∑ p, ν p) := by
  classical
  have hrow := finite_ghost_sector_counting_kernel_reproduces ν A |D| |C|
    (fun _ : Fin (k + b) → Σ p, R p => (1 : ℝ)) (fun _ _ => rfl) x
  simp only [mul_one] at hrow
  rw [← Finset.sum_div, ← Finset.sum_mul, hrow]
  exact (finite_ghost_sector_row_one_le_positive ν A D C v hν hA hv x).trans
    (positive_ghost_weighted_row_le_exp ν A D C v hν hA hv hbase x (b + 1))

/-- The actual finite-sector column has the swapped exponential bound in factorial measure.
Its endpoint mass is retained, including when it is zero. -/
theorem finite_ghost_sector_counting_kernel_weighted_column_le_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |C| / v ≤ 1)
    (y : Fin (k + b) → Σ p, R p) :
    (∑ x : Fin (k + a) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostSectorCountingKernel ν A |D| |C| x y * v ^ (k + a) / v ^ (k + b)) ≤
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      Real.exp (|D| * v * ∑ p, ν p) := by
  classical
  rw [← Finset.sum_div,
    finite_ghost_sector_counting_kernel_weighted_column ν A |D| |C| (fun _ => v ^ (k + a)),
    mul_div_assoc, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left
    (finite_ghost_sector_counting_kernel_weighted_row_le_exp ν A C D v hν hA hv hbase y)
  unfold factorialMemoryPointMass
  exact div_nonneg (Finset.prod_nonneg (fun i _ => hν (y i).1)) (Nat.cast_nonneg _)

/-- Common coefficient and prime-mass bounds give one row constant for all sector sizes. -/
theorem finite_ghost_sector_counting_kernel_weighted_row_le_uniform_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax Mmax : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |D| / v ≤ 1)
    (hC : |C| ≤ cmax) (hM : ∑ p, ν p ≤ Mmax) (x : Fin (k + a) → Σ p, R p) :
    (∑ y : Fin (k + b) → Σ p, R p,
      finiteGhostSectorCountingKernel ν A |D| |C| x y * v ^ (k + b) / v ^ (k + a)) ≤
        Real.exp (cmax * v * Mmax) := by
  classical
  have hrow := finite_ghost_sector_counting_kernel_reproduces ν A |D| |C|
    (fun _ : Fin (k + b) → Σ p, R p => (1 : ℝ)) (fun _ _ => rfl) x
  simp only [mul_one] at hrow
  rw [← Finset.sum_div, ← Finset.sum_mul, hrow]
  exact (finite_ghost_sector_row_one_le_positive ν A D C v hν hA hv x).trans
    (positive_ghost_weighted_row_le_uniform_exp ν A D C v cmax Mmax
      hν hA hv hbase hC hM x (b + 1))

/-- The uniform column constant uses the termination bound after transposition. -/
theorem finite_ghost_sector_counting_kernel_weighted_column_le_uniform_exp [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v dmax Mmax : ℝ)
    (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A) (hv : 0 < v) (hbase : A + |C| / v ≤ 1)
    (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) (y : Fin (k + b) → Σ p, R p) :
    (∑ x : Fin (k + a) → Σ p, R p,
      factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
        finiteGhostSectorCountingKernel ν A |D| |C| x y * v ^ (k + a) / v ^ (k + b)) ≤
    factorialMemoryPointMass (fun z : Σ p, R p => ν z.1) y *
      Real.exp (dmax * v * Mmax) := by
  classical
  rw [← Finset.sum_div,
    finite_ghost_sector_counting_kernel_weighted_column ν A |D| |C| (fun _ => v ^ (k + a)),
    mul_div_assoc, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left
    (finite_ghost_sector_counting_kernel_weighted_row_le_uniform_exp ν A C D v dmax Mmax
      hν hA hv hbase hD hM y)
  unfold factorialMemoryPointMass
  exact div_nonneg (Finset.prod_nonneg (fun i _ => hν (y i).1)) (Nat.cast_nonneg _)

/-- Taking the absolute value of the signed sector kernel exactly replaces D/C by their moduli. -/
theorem finite_ghost_sector_counting_kernel_abs [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (hν : ∀ p, 0 ≤ ν p) (hA : 0 ≤ A)
    (x : Fin (k + a) → Σ p, R p) (y : Fin (k + b) → Σ p, R p) :
    |finiteGhostSectorCountingKernel ν A D C x y| =
      finiteGhostSectorCountingKernel ν A |D| |C| x y := by
  classical
  have hQ : 0 ≤ ∑ s : Finset (Fin (k + a)),
      finiteGhostSubsetCoefficient ν A (fun _ z => symmetricMemoryPoint y z) s x := by
    apply Finset.sum_nonneg
    intro s _
    exact finite_ghost_subset_coefficient_nonneg ν A (fun _ z => symmetricMemoryPoint y z)
      hν hA (fun _ z => symmetric_memory_point_nonneg y z) s x
  unfold finiteGhostSectorCountingKernel finiteGhostSectorRow
  have hb : |(b.factorial : ℝ)| = (b.factorial : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg hQ, abs_div, abs_mul, abs_pow, abs_pow,
    hb]

end SimultaneousPrimitiveRoots.Unconditional.Graph

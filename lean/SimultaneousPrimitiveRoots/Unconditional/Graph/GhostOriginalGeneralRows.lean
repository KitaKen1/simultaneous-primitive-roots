module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostGeneralRows

/-!
# Absolutely convergent general ghost rows in the original measure

Positive factorial point masses undo the normalized kernel. Every original
weighted-square-integrable input therefore has an absolutely convergent
counting-kernel row, equal to the completed operator in original coordinates.
Only a single row is summed here; joint interchanges remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators Classical

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_original_row_term [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (hν : ∀ p, 0 < ν p) (A D C : ℝ)
    (f : InfiniteMemory (Σ p, R p) → ℂ) (x y : InfiniteMemory (Σ p, R p)) :
    ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y =
    (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ)⁻¹ *
      (normalizedInfiniteGhostKernel ν A D C x y * f y) := by
  have hx : (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (infinite_memory_point_mass_pos _ (fun z : Σ p, R p => hν z.1) x)).ne'
  unfold unweightedMemoryCoordinates normalizedInfiniteGhostKernel
  field_simp [hx]

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_original_general_row_norm_summable
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    Summable (fun y => ‖((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y‖) := by
  simp_rw [infinite_ghost_original_row_term ν hν A D C f x, norm_mul]
  simpa only [norm_mul] using
    (infinite_ghost_normalized_row_norm_summable ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f x).mul_left
        ‖(Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ)⁻¹‖

theorem infinite_ghost_original_general_row_summable
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    Summable (fun y => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y) :=
  (infinite_ghost_original_general_row_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f x).of_norm

theorem infinite_ghost_original_general_row_hasSum
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    HasSum (fun y => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y)
      (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
          hν hA hv hbaseD hbaseC hC hD hM f) x) := by
  have h := (infinite_ghost_normalized_row_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f x).hasSum.mul_left
      (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ)⁻¹
  rw [← infinite_ghost_continuous_operator_general_row ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM] at h
  convert h using 1
  · funext y
    exact infinite_ghost_original_row_term ν hν A D C f x y
  · unfold unweightedMemoryCoordinates
    rw [div_eq_mul_inv, mul_comm]

theorem infinite_ghost_original_general_row_eq_tsum
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM f) x =
      ∑' y, ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y :=
  (infinite_ghost_original_general_row_hasSum ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f x).tsum_eq.symm

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph

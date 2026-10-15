module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostContinuousOperator
public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockCoordinates
public import SimultaneousPrimitiveRoots.Unconditional.Graph.LpKernelRows
import Mathlib.Tactic.FieldSimp

/-!
# General-input ghost rows in the original factorial coordinates

The continuous completion has the actual normalized counting kernel as its
matrix. Its rows converge absolutely for every ell-two input and equal the
completed action. This identifies each single row; it does not assert an
unbounded double-sum interchange or the full conditional memory operator.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace Classical

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_finite_support_action_single [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (x y : InfiniteMemory (Σ p, R p)) (a : ℂ) :
    infiniteGhostFiniteSupportAction ν A D C (Finsupp.single y a) x =
      ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a := by
  classical
  change (Finsupp.single y a).sum
    (fun z b => ((infiniteGhostKernel ν A D C x z : ℝ) : ℂ) * b) = _
  exact Finsupp.sum_single_index (mul_zero _)

noncomputable def normalizedInfiniteGhostKernel [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (x y : InfiniteMemory (Σ p, R p)) : ℂ :=
  (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x) : ℂ) *
    ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) /
    (Real.sqrt (infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y) : ℂ)

theorem normalized_infinite_ghost_kernel_star [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (x y : InfiniteMemory (Σ p, R p)) :
    star (normalizedInfiniteGhostKernel ν A D C x y) =
      normalizedInfiniteGhostKernel ν A D C x y := by
  simp [normalizedInfiniteGhostKernel]

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_continuous_operator_matrix (x y : InfiniteMemory (Σ p, R p)) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM (lpCoordinateVector y) x =
      normalizedInfiniteGhostKernel ν A D C x y := by
  let w := fun z : Σ p, R p => ν z.1
  have hy : (Real.sqrt (infiniteMemoryPointMass w y) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (infinite_memory_point_mass_pos w (fun z => hν z.1) y)).ne'
  have he : weightedMemoryInputLinearMap w
      (Finsupp.single y (Real.sqrt (infiniteMemoryPointMass w y) : ℂ)⁻¹) =
      lpCoordinateVector y := by
    change finiteSupportWeightedLp _ (Finsupp.single y _) =
      @lp.single _ _ _ (Classical.decEq _) 2 y 1
    rw [finite_support_weighted_lp_single, mul_inv_cancel₀ hy]
  rw [← he, infinite_ghost_continuous_operator_coordinates]
  unfold weightedMemoryCoordinates
  rw [infinite_ghost_finite_support_action_single]
  simp only [normalizedInfiniteGhostKernel, div_eq_mul_inv, mul_assoc, w]

theorem infinite_ghost_normalized_row_norm_summable
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    Summable (fun y => ‖normalizedInfiniteGhostKernel ν A D C x y * f y‖) := by
  have h := lp_operator_row_norm_summable
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) f x
  simpa only [infinite_ghost_continuous_operator_matrix ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM] using h

theorem infinite_ghost_normalized_row_summable
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    Summable (fun y => normalizedInfiniteGhostKernel ν A D C x y * f y) :=
  (infinite_ghost_normalized_row_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f x).of_norm

theorem infinite_ghost_continuous_operator_general_row
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) :
    infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f x =
      ∑' y, normalizedInfiniteGhostKernel ν A D C x y * f y := by
  rw [lp_operator_apply_eq_tsum]
  simp only [infinite_ghost_continuous_operator_matrix ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM]

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph

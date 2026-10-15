module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostGeneralRows
import Mathlib.Tactic.Ring

/-!
# The reversed pure ghost completion is the complex Hilbert adjoint

The original factorial weighted transpose becomes the transpose of the
normalized real matrix. Absolutely convergent single rows identify bounded
operators by that matrix, giving the adjoint without assuming double sums.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace Classical

variable {P : Type*} {R : P → Type*}

theorem normalized_infinite_ghost_kernel_transpose [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (hν : ∀ p, 0 < ν p)
    (A D C : ℝ) (x y : InfiniteMemory (Σ p, R p)) :
    normalizedInfiniteGhostKernel ν A D C x y = normalizedInfiniteGhostKernel ν A C D y x := by
  let w := fun z : Σ p, R p => ν z.1
  have hx0 := (infinite_memory_point_mass_pos w (fun z => hν z.1) x).le
  have hy0 := (infinite_memory_point_mass_pos w (fun z => hν z.1) y).le
  have hx : (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (infinite_memory_point_mass_pos w (fun z => hν z.1) x)).ne'
  have hy : (Real.sqrt (infiniteMemoryPointMass w y) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (infinite_memory_point_mass_pos w (fun z => hν z.1) y)).ne'
  have hxs : (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ^ 2 =
      ((infiniteMemoryPointMass w x : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hx0
  have hys : (Real.sqrt (infiniteMemoryPointMass w y) : ℂ) ^ 2 =
      ((infiniteMemoryPointMass w y : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy0
  have ht : ((infiniteMemoryPointMass w x : ℝ) : ℂ) *
      ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) =
      ((infiniteMemoryPointMass w y : ℝ) : ℂ) * ((infiniteGhostKernel ν A C D y x : ℝ) : ℂ) := by
    exact_mod_cast infinite_ghost_kernel_weighted_transpose ν A D C x y
  unfold normalizedInfiniteGhostKernel
  apply (div_eq_div_iff hy hx).mpr
  calc
    _ = (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ^ 2 *
        ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) := by dsimp [w]; ring
    _ = (Real.sqrt (infiniteMemoryPointMass w y) : ℂ) ^ 2 *
        ((infiniteGhostKernel ν A C D y x : ℝ) : ℂ) := by rw [hxs, hys]; exact ht
    _ = _ := by dsimp [w]; ring

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

theorem infinite_ghost_continuous_operator_adjoint :
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM).adjoint =
    infiniteGhostContinuousOperator (R := R) ν A C D v dmax cmax Mmax
      hν hA hv hbaseC hbaseD hD hC hM := by
  apply lp_operator_eq_of_matrix
  intro x y
  rw [lp_operator_adjoint_single_coordinates,
    infinite_ghost_continuous_operator_matrix,
    normalized_infinite_ghost_kernel_star,
    normalized_infinite_ghost_kernel_transpose ν hν A D C y x,
    infinite_ghost_continuous_operator_matrix]

theorem infinite_ghost_continuous_reversed_pairing
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    inner ℂ g (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f) =
    inner ℂ (infiniteGhostContinuousOperator (R := R) ν A C D v dmax cmax Mmax
      hν hA hv hbaseC hbaseD hD hC hM g) f := by
  rw [← infinite_ghost_continuous_operator_adjoint ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM]
  exact (ContinuousLinearMap.adjoint_inner_left _ f g).symm

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph

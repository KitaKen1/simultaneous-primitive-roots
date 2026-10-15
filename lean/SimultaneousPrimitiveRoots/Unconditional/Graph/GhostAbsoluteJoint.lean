module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostInfiniteMajorant
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostOriginalPairing
public import SimultaneousPrimitiveRoots.Unconditional.Graph.LpAbsoluteJoint

/-!
# Absolute memory-pair summability and the original flat ghost pairing

The bounded positive-coefficient completion dominates the actual signed
matrix. This proves absolute summability over memory pairs, not merely after
collapsing each row. The original factorial measure is retained exactly.
Reindexing this flat joint sum into the source survivor/termination/birth
sector integral and full conditional transference are separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_original_joint_term [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (hν : ∀ p, 0 < ν p) (A D C : ℝ)
    (f g : InfiniteMemory (Σ p, R p) → ℂ) (x y : InfiniteMemory (Σ p, R p)) :
    ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
      ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y =
    star (g x) * normalizedInfiniteGhostKernel ν A D C x y * f y := by
  have h := weighted_memory_inner_coordinates (fun z : Σ p, R p => ν z.1)
    (fun z => hν z.1) (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g)
    (fun x => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y) x
  rw [weighted_unweighted_memory_coordinates _ (fun z : Σ p, R p => hν z.1)] at h
  calc
    _ = ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
        (((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
          unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y) := by ring
    _ = _ := h
    _ = _ := by
      unfold weightedMemoryCoordinates unweightedMemoryCoordinates normalizedInfiniteGhostKernel
      simp only [div_eq_mul_inv]
      ring

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_operator_matrix_majorant (x y : InfiniteMemory (Σ p, R p)) :
    ‖infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM (lpCoordinateVector y) x‖ ≤
    (infiniteGhostContinuousOperator (R := R) ν A |D| |C| v cmax dmax Mmax
      hν hA hv (by simpa only [abs_abs] using hbaseD)
      (by simpa only [abs_abs] using hbaseC)
      (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM
        (lpCoordinateVector y) x).re := by
  rw [infinite_ghost_continuous_operator_matrix, infinite_ghost_continuous_operator_matrix]
  exact normalized_infinite_ghost_kernel_norm_majorant ν hν A D C hA x y

theorem infinite_ghost_normalized_joint_norm_summable
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p) =>
      ‖star (g z.1) * normalizedInfiniteGhostKernel ν A D C z.1 z.2 * f z.2‖) := by
  have h := lp_operator_absolute_joint_summable
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (infiniteGhostContinuousOperator (R := R) ν A |D| |C| v cmax dmax Mmax
      hν hA hv (by simpa only [abs_abs] using hbaseD)
      (by simpa only [abs_abs] using hbaseC)
      (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM)
    (infinite_ghost_operator_matrix_majorant ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) f g
  simpa only [infinite_ghost_continuous_operator_matrix] using h

theorem infinite_ghost_normalized_flat_joint_pairing
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p),
      star (g z.1) * normalizedInfiniteGhostKernel ν A D C z.1 z.2 * f z.2) =
    inner ℂ g (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f) := by
  have h := lp_operator_flat_joint_pairing
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (infiniteGhostContinuousOperator (R := R) ν A |D| |C| v cmax dmax Mmax
      hν hA hv (by simpa only [abs_abs] using hbaseD)
      (by simpa only [abs_abs] using hbaseC)
      (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM)
    (infinite_ghost_operator_matrix_majorant ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) f g
  simpa only [infinite_ghost_continuous_operator_matrix] using h

theorem infinite_ghost_original_joint_norm_summable
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p) =>
      ‖((infiniteMemoryPointMass (fun a : Σ p, R p => ν a.1) z.1 : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g z.1) *
        ((infiniteGhostKernel ν A D C z.1 z.2 : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f z.2‖) := by
  simpa only [infinite_ghost_original_joint_term ν hν A D C f g] using
    infinite_ghost_normalized_joint_norm_summable ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f g

theorem infinite_ghost_original_flat_joint_pairing
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p),
      ((infiniteMemoryPointMass (fun a : Σ p, R p => ν a.1) z.1 : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g z.1) *
        ((infiniteGhostKernel ν A D C z.1 z.2 : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f z.2) =
    inner ℂ g (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f) := by
  simpa only [infinite_ghost_original_joint_term ν hν A D C f g] using
    infinite_ghost_normalized_flat_joint_pairing ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f g

theorem infinite_ghost_normalized_absolute_joint_bound
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p),
      ‖star (g z.1) * normalizedInfiniteGhostKernel ν A D C z.1 z.2 * f z.2‖) ≤
    ‖g‖ * Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) *
      ‖f‖ := by
  have h := lp_operator_absolute_joint_norm_bound
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM)
    (infiniteGhostContinuousOperator (R := R) ν A |D| |C| v cmax dmax Mmax
      hν hA hv (by simpa only [abs_abs] using hbaseD)
      (by simpa only [abs_abs] using hbaseC)
      (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM)
    (infinite_ghost_operator_matrix_majorant ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM) f g
  simp only [infinite_ghost_continuous_operator_matrix] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg g)
  exact infinite_ghost_continuous_operator_opnorm_bound (R := R) ν A |D| |C|
    v cmax dmax Mmax hν hA hv (by simpa only [abs_abs] using hbaseD)
    (by simpa only [abs_abs] using hbaseC)
    (by simpa only [abs_abs] using hC) (by simpa only [abs_abs] using hD) hM

theorem infinite_ghost_original_absolute_joint_bound
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' z : InfiniteMemory (Σ p, R p) × InfiniteMemory (Σ p, R p),
      ‖((infiniteMemoryPointMass (fun a : Σ p, R p => ν a.1) z.1 : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g z.1) *
        ((infiniteGhostKernel ν A D C z.1 z.2 : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f z.2‖) ≤
    ‖g‖ * Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) *
      ‖f‖ := by
  simpa only [infinite_ghost_original_joint_term ν hν A D C f g] using
    infinite_ghost_normalized_absolute_joint_bound ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f g

theorem infinite_ghost_original_joint_tsum_comm
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' y, ∑' x,
      ((infiniteMemoryPointMass (fun a : Σ p, R p => ν a.1) x : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g x) *
        ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f y) =
    (∑' x, ∑' y,
      ((infiniteMemoryPointMass (fun a : Σ p, R p => ν a.1) x : ℝ) : ℂ) *
        star (unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) g x) *
        ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun a : Σ p, R p => ν a.1) f y) :=
  (infinite_ghost_original_joint_norm_summable ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g).of_norm.tsum_comm

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph

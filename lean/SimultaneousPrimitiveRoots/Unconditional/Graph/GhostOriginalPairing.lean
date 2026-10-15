module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostOriginalGeneralRows
public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostContinuousAdjoint

/-!
# Reversed iterated ghost pairing in the original factorial measure

The coordinate isometry preserves the complex inner product. Each kernel
row is absolutely convergent, and both collapsed outer pairings converge
absolutely. The reversed-adjoint identity thus gives equality of these two
iterated sums. Absolute summability over pairs is not asserted here.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace

variable {Z P : Type*} {R : P → Type*}

theorem weighted_memory_inner_coordinates (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (g f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    ((infiniteMemoryPointMass w x : ℝ) : ℂ) * star (g x) * f x =
      star (weightedMemoryCoordinates w g x) * weightedMemoryCoordinates w f x := by
  have hs : (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) ^ 2 =
      ((infiniteMemoryPointMass w x : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (infinite_memory_point_mass_pos w hw x).le
  unfold weightedMemoryCoordinates
  rw [star_mul]
  have hr : star (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) =
      (Real.sqrt (infiniteMemoryPointMass w x) : ℂ) := by simp
  rw [hr, ← hs]
  ring

theorem unweighted_memory_inner_coordinates (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (g f : InfiniteMemory Z → ℂ) (x : InfiniteMemory Z) :
    ((infiniteMemoryPointMass w x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates w g x) * unweightedMemoryCoordinates w f x =
      star (g x) * f x := by
  have h := weighted_memory_inner_coordinates w hw
    (unweightedMemoryCoordinates w g) (unweightedMemoryCoordinates w f) x
  simpa only [weighted_unweighted_memory_coordinates w hw] using h

theorem original_weighted_lp_inner_norm_summable (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (g f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    Summable (fun x => ‖((infiniteMemoryPointMass w x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates w g x) * unweightedMemoryCoordinates w f x‖) := by
  simp_rw [unweighted_memory_inner_coordinates w hw g f]
  simpa only [norm_mul, norm_star] using
    lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) g f

theorem original_weighted_lp_inner_eq_tsum (w : Z → ℝ) (hw : ∀ z, 0 < w z)
    (g f : lp (fun _ : InfiniteMemory Z => ℂ) 2) :
    inner ℂ g f = ∑' x, ((infiniteMemoryPointMass w x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates w g x) * unweightedMemoryCoordinates w f x := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [unweighted_memory_inner_coordinates w hw g f]
  exact RCLike.inner_apply' (g x) (f x)

section Bounded

variable [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)

include v cmax dmax Mmax hν hA hv hbaseD hbaseC hC hD hM

theorem infinite_ghost_original_iterated_pairing
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' x, ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
      (∑' y, ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y)) =
    ∑' y, ((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y : ℝ) : ℂ) *
      star (∑' x, ((infiniteGhostKernel ν A C D y x : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y := by
  have h := infinite_ghost_continuous_reversed_pairing ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f g
  rw [original_weighted_lp_inner_eq_tsum _ (fun z : Σ p, R p => hν z.1),
    original_weighted_lp_inner_eq_tsum _ (fun z : Σ p, R p => hν z.1)] at h
  simpa only [infinite_ghost_original_general_row_eq_tsum ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM,
    infinite_ghost_original_general_row_eq_tsum ν A C D v dmax cmax Mmax
      hν hA hv hbaseC hbaseD hD hC hM] using h

theorem infinite_ghost_original_iterated_left_norm_summable
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun x => ‖((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x : ℝ) : ℂ) *
      star (unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
      (∑' y, ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y)‖) := by
  have h := original_weighted_lp_inner_norm_summable
    (fun z : Σ p, R p => ν z.1) (fun z => hν z.1) g
    (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM f)
  simpa only [infinite_ghost_original_general_row_eq_tsum ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM] using h

theorem infinite_ghost_original_iterated_right_norm_summable
    (f g : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun y => ‖((infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) y : ℝ) : ℂ) *
      star (∑' x, ((infiniteGhostKernel ν A C D y x : ℝ) : ℂ) *
        unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) g x) *
      unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1) f y‖) := by
  have h := original_weighted_lp_inner_norm_summable
    (fun z : Σ p, R p => ν z.1) (fun z => hν z.1)
    (infiniteGhostContinuousOperator (R := R) ν A C D v dmax cmax Mmax
      hν hA hv hbaseC hbaseD hD hC hM g) f
  simpa only [infinite_ghost_original_general_row_eq_tsum ν A C D v dmax cmax Mmax
    hν hA hv hbaseC hbaseD hD hC hM] using h

end Bounded

end SimultaneousPrimitiveRoots.Unconditional.Graph

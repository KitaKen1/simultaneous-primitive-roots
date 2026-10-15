module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.SymmetricFockOperator
public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockCoordinates

/-!
# The continuous ghost completion in original factorial-weighted functions

Inverse mass coordinates give an original-memory function for every input
of the continuous completion. Its original weighted square sum is summable
and satisfies the full norm bound; finite-support inputs give exactly the
original support action. Output particle-index symmetry is retained.
General-input row-series and joint/adjoint interchanges are not asserted.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_original_weighted_square_summable [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    Summable (fun x => infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      ‖unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
          hν hA hv hbaseD hbaseC hC hD hM f) x‖ ^ 2) :=
  unweighted_memory_lp_square_summable _ (fun z : Σ p, R p => hν z.1) _

theorem infinite_ghost_original_weighted_tsum_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2) :
    (∑' x, infiniteMemoryPointMass (fun z : Σ p, R p => ν z.1) x *
      ‖unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
          hν hA hv hbaseD hbaseC hC hD hM f) x‖ ^ 2) ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) * ‖f‖ ^ 2 := by
  rw [unweighted_memory_lp_tsum_square _ (fun z : Σ p, R p => hν z.1)]
  have h := infinite_ghost_continuous_operator_norm_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM f
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, Real.sq_sqrt (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le] at hs
  exact hs

theorem infinite_ghost_original_weighted_on_finite_support [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) (x : InfiniteMemory (Σ p, R p)) :
    unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM
          (weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g)) x =
    infiniteGhostFiniteSupportAction ν A D C g x := by
  unfold unweightedMemoryCoordinates
  rw [infinite_ghost_continuous_operator_coordinates]
  exact unweighted_weighted_memory_coordinates _ (fun z : Σ p, R p => hν z.1)
    (infiniteGhostFiniteSupportAction ν A D C g) x

theorem infinite_ghost_original_weighted_output_symmetric [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (f : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (x : InfiniteMemory (Σ p, R p)) (σ : Equiv.Perm (Fin x.1)) :
    unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM f) ⟨x.1, x.2 ∘ σ⟩ =
    unweightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostContinuousOperator (R := R) ν A D C v cmax dmax Mmax
        hν hA hv hbaseD hbaseC hC hD hM f) x := by
  unfold unweightedMemoryCoordinates
  rw [infinite_memory_point_mass_invariant, infinite_ghost_continuous_operator_symmetric]

end SimultaneousPrimitiveRoots.Unconditional.Graph

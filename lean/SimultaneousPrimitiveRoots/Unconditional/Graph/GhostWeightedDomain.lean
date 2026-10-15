module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.WeightedFockInput
import Mathlib.Tactic.Ring

/-!
# Original weighted finite-support domain norm for the complete ghost action

The complex linear map takes the original finite-support Fock input to its
entire ell-two output. Its bound is measured against the exact square-root
factorial-mass input embedding, not a default norm on Finsupp.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P : Type*} {R : P → Type*}

noncomputable def infiniteGhostWeightedDomainLinearMap [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax) :
    (InfiniteMemory (Σ p, R p) →₀ ℂ) →ₗ[ℂ] lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 where
  toFun := infiniteGhostFiniteSupportLpOutput ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM
  map_add' g h := by
    apply lp.ext
    funext x
    change weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C (g + h)) x =
      weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostFiniteSupportAction ν A D C g) x +
      weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostFiniteSupportAction ν A D C h) x
    unfold weightedMemoryCoordinates
    rw [infinite_ghost_finite_support_action_add, mul_add]
  map_smul' c g := by
    apply lp.ext
    funext x
    change weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
      (infiniteGhostFiniteSupportAction ν A D C (c • g)) x =
      c * weightedMemoryCoordinates (fun z : Σ p, R p => ν z.1)
        (infiniteGhostFiniteSupportAction ν A D C g) x
    unfold weightedMemoryCoordinates
    rw [infinite_ghost_finite_support_action_smul]
    ring

theorem infinite_ghost_weighted_domain_norm_sq_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    ‖infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g‖ ^ 2 ≤
    Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax) *
      ‖weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g‖ ^ 2 := by
  rw [weighted_memory_input_norm_sq _ (fun z : Σ p, R p => hν z.1)]
  exact infinite_ghost_finite_support_lp_output_norm_sq_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g

theorem infinite_ghost_weighted_domain_norm_bound [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → ℝ) (A D C v cmax dmax Mmax : ℝ)
    (hν : ∀ p, 0 < ν p) (hA : 0 ≤ A) (hv : 0 < v)
    (hbaseD : A + |D| / v ≤ 1) (hbaseC : A + |C| / v ≤ 1)
    (hC : |C| ≤ cmax) (hD : |D| ≤ dmax) (hM : ∑ p, ν p ≤ Mmax)
    (g : InfiniteMemory (Σ p, R p) →₀ ℂ) :
    ‖infiniteGhostWeightedDomainLinearMap ν A D C v cmax dmax Mmax
      hν hA hv hbaseD hbaseC hC hD hM g‖ ≤
    Real.sqrt (Real.exp (cmax * v * Mmax) * Real.exp (dmax * v * Mmax)) *
      ‖weightedMemoryInputLinearMap (fun z : Σ p, R p => ν z.1) g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
  exact infinite_ghost_weighted_domain_norm_sq_bound ν A D C v cmax dmax Mmax
    hν hA hv hbaseD hbaseC hC hD hM g

end SimultaneousPrimitiveRoots.Unconditional.Graph

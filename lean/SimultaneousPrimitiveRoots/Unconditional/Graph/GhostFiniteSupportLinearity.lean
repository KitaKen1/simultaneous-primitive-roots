module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.InfiniteMemory
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Ring

/-!
# Linear finite-support ghost action

The support formula defines a complex linear map to functions on the whole
infinite memory. The output support is unrestricted. No continuous extension
or completion is asserted by this algebraic linear map. GhostContinuousOperator
constructs that extension using the proved weighted input norm.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

variable {P : Type*} {R : P → Type*}

theorem infinite_ghost_finite_support_action_add [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (g h : InfiniteMemory (Σ p, R p) →₀ ℂ)
    (x : InfiniteMemory (Σ p, R p)) :
    infiniteGhostFiniteSupportAction ν A D C (g + h) x =
      infiniteGhostFiniteSupportAction ν A D C g x +
        infiniteGhostFiniteSupportAction ν A D C h x := by
  classical
  change (g + h).sum (fun y a => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a) =
    g.sum (fun y a => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a) +
      h.sum (fun y a => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a)
  exact Finsupp.sum_add_index (fun _ _ => mul_zero _) (fun _ _ _ _ => mul_add _ _ _)

theorem infinite_ghost_finite_support_action_smul [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) (c : ℂ) (g : InfiniteMemory (Σ p, R p) →₀ ℂ)
    (x : InfiniteMemory (Σ p, R p)) :
    infiniteGhostFiniteSupportAction ν A D C (c • g) x =
      c * infiniteGhostFiniteSupportAction ν A D C g x := by
  classical
  change (c • g).sum (fun y a => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a) =
    c * g.sum (fun y a => ((infiniteGhostKernel ν A D C x y : ℝ) : ℂ) * a)
  rw [Finsupp.sum_smul_index]
  · unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  · intro y
    exact mul_zero _

noncomputable def infiniteGhostFiniteSupportLinearMap [Fintype P] [∀ p, Zero (R p)]
    (ν : P → ℝ) (A D C : ℝ) :
    (InfiniteMemory (Σ p, R p) →₀ ℂ) →ₗ[ℂ] (InfiniteMemory (Σ p, R p) → ℂ) where
  toFun := infiniteGhostFiniteSupportAction ν A D C
  map_add' g h := funext (infinite_ghost_finite_support_action_add ν A D C g h)
  map_smul' c g := funext (fun x => infinite_ghost_finite_support_action_smul ν A D C c g x)

end SimultaneousPrimitiveRoots.Unconditional.Graph

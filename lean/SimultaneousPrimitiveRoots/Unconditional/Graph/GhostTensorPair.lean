module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostGeneralRows
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# Completed Hilbert tensor products of two actual ghost factors

Two bounded ghost maps give a map on the completed Hilbert tensor product,
with product norm bound and the exact product of their normalized counting
matrices on coordinate tensors. No finite-memory cutoff is imposed. Arbitrary
families and identification with the full source conditional operator remain
separate obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped TensorProduct ComplexInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

noncomputable def completedHilbertTensorPairOperator (T : E →L[ℂ] E) (U : F →L[ℂ] F) :
    UniformSpace.Completion (E ⊗[ℂ] F) →L[ℂ] UniformSpace.Completion (E ⊗[ℂ] F) :=
  (TensorProduct.mapL T U).completion

theorem completed_hilbert_tensor_pair_on_pure (T : E →L[ℂ] E) (U : F →L[ℂ] F)
    (e : E) (f : F) :
    completedHilbertTensorPairOperator T U (e ⊗ₜ[ℂ] f : E ⊗[ℂ] F) =
      (T e ⊗ₜ[ℂ] U f : E ⊗[ℂ] F) := by
  exact ContinuousLinearMap.completion_apply_coe (TensorProduct.mapL T U) _

theorem completed_hilbert_tensor_pair_norm_bound (T : E →L[ℂ] E) (U : F →L[ℂ] F)
    (z : UniformSpace.Completion (E ⊗[ℂ] F)) :
    ‖completedHilbertTensorPairOperator T U z‖ ≤ (‖T‖ * ‖U‖) * ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (completedHilbertTensorPairOperator T U).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih z =>
    change ‖(TensorProduct.mapL T U).completion (z : UniformSpace.Completion _)‖ ≤ _
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact ((TensorProduct.mapL T U).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le T U) (norm_nonneg z))

theorem completed_hilbert_tensor_pair_opnorm_bound (T : E →L[ℂ] E) (U : F →L[ℂ] F) :
    ‖completedHilbertTensorPairOperator T U‖ ≤ ‖T‖ * ‖U‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg T) (norm_nonneg U))
    (completed_hilbert_tensor_pair_norm_bound T U)

theorem completed_hilbert_tensor_pair_exp_bound (T : E →L[ℂ] E) (U : F →L[ℂ] F)
    (B C : ℝ) (hT : ‖T‖ ≤ Real.exp B) (hU : ‖U‖ ≤ Real.exp C) :
    ‖completedHilbertTensorPairOperator T U‖ ≤ Real.exp (B + C) := by
  calc
    _ ≤ ‖T‖ * ‖U‖ := completed_hilbert_tensor_pair_opnorm_bound T U
    _ ≤ Real.exp B * Real.exp C := mul_le_mul hT hU (norm_nonneg U) (Real.exp_pos B).le
    _ = _ := (Real.exp_add B C).symm

theorem completed_lp_tensor_pair_matrix {I J : Type*}
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (U : lp (fun _ : J => ℂ) 2 →L[ℂ] lp (fun _ : J => ℂ) 2)
    (x y : I) (a b : J) :
    inner ℂ
      ((lpCoordinateVector x ⊗ₜ[ℂ] lpCoordinateVector a) :
        UniformSpace.Completion (lp (fun _ : I => ℂ) 2 ⊗[ℂ] lp (fun _ : J => ℂ) 2))
      (completedHilbertTensorPairOperator T U
        (lpCoordinateVector y ⊗ₜ[ℂ] lpCoordinateVector b :
          lp (fun _ : I => ℂ) 2 ⊗[ℂ] lp (fun _ : J => ℂ) 2)) =
      T (lpCoordinateVector y) x * U (lpCoordinateVector b) a := by
  rw [completed_hilbert_tensor_pair_on_pure, UniformSpace.Completion.inner_coe,
    TensorProduct.inner_tmul]
  simp only [lpCoordinateVector, lp.inner_single_left, RCLike.inner_apply',
    starRingEnd_apply, star_one, one_mul]

theorem completed_ghost_tensor_pair_matrix {P Q : Type*} {R : P → Type*} {S : Q → Type*}
    [Fintype P] [∀ p, Fintype (R p)] [∀ p, Zero (R p)]
    [Fintype Q] [∀ q, Fintype (S q)] [∀ q, Zero (S q)]
    (ν : P → ℝ) (μ : Q → ℝ) (A D C B E H : ℝ)
    (T : lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 →L[ℂ]
      lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2)
    (U : lp (fun _ : InfiniteMemory (Σ q, S q) => ℂ) 2 →L[ℂ]
      lp (fun _ : InfiniteMemory (Σ q, S q) => ℂ) 2)
    (hT : ∀ x y, T (lpCoordinateVector y) x = normalizedInfiniteGhostKernel ν A D C x y)
    (hU : ∀ a b, U (lpCoordinateVector b) a = normalizedInfiniteGhostKernel μ B E H a b)
    (x y : InfiniteMemory (Σ p, R p)) (a b : InfiniteMemory (Σ q, S q)) :
    inner ℂ
      ((lpCoordinateVector x ⊗ₜ[ℂ] lpCoordinateVector a) :
        UniformSpace.Completion
          (lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 ⊗[ℂ]
            lp (fun _ : InfiniteMemory (Σ q, S q) => ℂ) 2))
      (completedHilbertTensorPairOperator T U
        (lpCoordinateVector y ⊗ₜ[ℂ] lpCoordinateVector b :
          lp (fun _ : InfiniteMemory (Σ p, R p) => ℂ) 2 ⊗[ℂ]
            lp (fun _ : InfiniteMemory (Σ q, S q) => ℂ) 2)) =
      normalizedInfiniteGhostKernel ν A D C x y * normalizedInfiniteGhostKernel μ B E H a b := by
  rw [completed_lp_tensor_pair_matrix, hT, hU]

end SimultaneousPrimitiveRoots.Unconditional.Graph

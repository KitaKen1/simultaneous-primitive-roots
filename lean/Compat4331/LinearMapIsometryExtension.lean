/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Zhouhang Zhou
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2:
Analysis/Normed/Operator/Extend.lean. The extension's linear-map field and
norm-preservation proof are retained verbatim. -/
module

public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

noncomputable section

variable {𝕜 𝕜₂ E Eₗ F : Type*}

namespace LinearMap

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂]
  [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ]
  [NormedAddCommGroup F] [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [CompleteSpace F]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ₁₂] F) {e : E →ₗ[𝕜] Eₗ}

/-- Extend a linear map `f : E →ₛₗ[σ₁₂] F` to a linear isometry `Eₗ →ₛₗᵢ[σ₁₂] F` between
Banach spaces, using a dense linear map `e : E →ₗ[𝕜] Eₗ` together with the norm equality
`‖f x‖ = ‖e x‖` for all `x : E`. -/
def extendOfIsometry (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) :
    Eₗ →ₛₗᵢ[σ₁₂] F where
  toLinearMap := f.extendOfNorm e
  norm_map' := by
    refine h_dense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro x ⟨y, rfl⟩
    norm_cast
    rw [LinearMap.extendOfNorm_eq h_dense (by use 1; simp [h_norm]), h_norm y]

@[simp]
theorem extendOfIsometry_eq (h_dense : DenseRange e) (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) :
    f.extendOfIsometry h_dense h_norm (e x) = f x :=
  LinearMap.extendOfNorm_eq h_dense ⟨1, fun x ↦ by simp [h_norm x]⟩ x

end LinearMap

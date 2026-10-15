module

public import SimultaneousPrimitiveRoots.Hecke.AveragedMellin

/-!
# The dual side of the averaged theta FE-pair

`dualEquiv` is an involution, and the dual of a `ThetaFamily` is again a `ThetaFamily` (with
covolume `covol⁻¹`). The `symm` pair of `F.fePair μ` has the same Mellin transform as
`F.dual.fePair μ`, so its `Λ` is the averaged Epstein series of the dual lattices
(`ThetaFamily.Λ_symm_eq_integral`). This is the right-hand side of the functional equation.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Matrix
open scoped Real Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem invMatrix_dualEquiv (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    invMatrix (dualEquiv A) = (fwdMatrix A)ᵀ := by
  unfold invMatrix
  have : ((dualEquiv A).symm : (d → ℝ) →ₗ[ℝ] (d → ℝ)) = Matrix.toLin' (fwdMatrix A)ᵀ := rfl
  rw [this, LinearMap.toMatrix'_toLin']

/-- **`dualEquiv` is an involution.** -/
theorem dualEquiv_dualEquiv (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : dualEquiv (dualEquiv A) = A := by
  refine LinearEquiv.ext fun v => ?_
  rw [dualEquiv_apply, invMatrix_dualEquiv, Matrix.transpose_transpose]
  unfold fwdMatrix
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem det_dualEquiv (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) :
    LinearMap.det (dualEquiv A : (d → ℝ) →ₗ[ℝ] (d → ℝ)) =
      (LinearMap.det (A : (d → ℝ) →ₗ[ℝ] (d → ℝ)))⁻¹ := by
  have h1 : ((dualEquiv A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) : (d → ℝ) →ₗ[ℝ] (d → ℝ)) =
      Matrix.toLin' (invMatrix A)ᵀ := rfl
  rw [h1, LinearMap.det_toLin', Matrix.det_transpose, invMatrix, LinearMap.det_toMatrix',
    LinearEquiv.det_coe_symm]

namespace ThetaFamily

variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]

/-- The dual family `p ↦ A_p^{-T}`. -/
def dual (F : ThetaFamily d P) : ThetaFamily d P where
  A p := dualEquiv (F.A p)
  continuous_A := F.continuous_dual
  continuous_dual v := by
    simp_rw [dualEquiv_dualEquiv]
    exact F.continuous_A v
  κ := F.κ
  κ_pos := F.κ_pos
  lower := F.lower_dual
  lower_dual p v := by
    rw [dualEquiv_dualEquiv]
    exact F.lower p v
  covol := F.covol⁻¹
  covol_pos := inv_pos.mpr F.covol_pos
  abs_det p := by
    rw [det_dualEquiv, abs_inv, F.abs_det p]

omit [OpensMeasurableSpace P] in
theorem dual_A (F : ThetaFamily d P) (p : P) : F.dual.A p = dualEquiv (F.A p) := rfl

variable (F : ThetaFamily d P) (μ : Measure P) [IsFiniteMeasure μ]

/-- The `symm` pair and the dual family's pair agree on `re s > d/2`. -/
theorem fePair_symm_Λ_eq [Nonempty d] {s : ℂ} (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    (F.fePair μ).symm.Λ s = (F.dual.fePair μ).Λ s := by
  have h1 := (F.fePair μ).symm.hasMellin (s := s) hs
  have h2 := (F.dual.fePair μ).hasMellin (s := s) hs
  rw [← h1.2, ← h2.2]
  rfl

/-- **The dual side as an averaged Epstein series.** -/
theorem Λ_symm_eq_integral [Nonempty d] {s : ℂ} (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    (F.fePair μ).symm.Λ s = ∫ p, ∑' m : d → ℤ,
      π ^ (-s) * Gamma s * 1 / ((sqNorm (dualEquiv (F.A p) (intVec m)) : ℝ) : ℂ) ^ s ∂μ := by
  rw [fePair_symm_Λ_eq F μ hs, Λ_eq_integral F.dual μ hs]
  rfl

end ThetaFamily

end SimultaneousPrimitiveRoots.Hecke

end

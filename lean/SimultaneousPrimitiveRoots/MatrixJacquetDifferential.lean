module

public import SimultaneousPrimitiveRoots.MatrixJacquetChart
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate Matrix.Norms.Elementwise
noncomputable section

theorem artinMatrixLeftMul_contDiff (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ ∞ (fun X : Matrix (Fin 2) (Fin 2) ℂ => g * X) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact (contDiff_const.mul (contDiff_apply_apply ℝ ℂ (0 : Fin 2) j)).add
    (contDiff_const.mul (contDiff_apply_apply ℝ ℂ (1 : Fin 2) j))

theorem artinMatrixRightJacquet_contDiffAt {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    ContDiffAt ℝ ∞ (fun X : Matrix (Fin 2) (Fin 2) ℂ =>
      artinMatrixJacquet c (g * (1 + X))) 0 := by
  have h : ContDiff ℝ ∞ (fun X : Matrix (Fin 2) (Fin 2) ℂ => g * (1 + X)) :=
    (artinMatrixLeftMul_contDiff g).comp (contDiff_const.add contDiff_id)
  have hf : ContDiffAt ℝ ∞ (artinMatrixJacquet c) (g * (1 + (0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    simpa using artinMatrixJacquet_contDiffAt hc hg
  exact ContDiffAt.fun_comp (f := fun X : Matrix (Fin 2) (Fin 2) ℂ => g * (1 + X))
    (g := artinMatrixJacquet c) 0 hf h.contDiffAt

/-- The real differential of the actual matrix integral, rather than a map
specified by desired basis values. -/
def artinMatrixJacquetDifferential (c : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
  (fderiv ℝ (fun X : Matrix (Fin 2) (Fin 2) ℂ =>
    artinMatrixJacquet c (g * (1 + X))) 0).toLinearMap

/-- Every genuine right curve with the same tangent has the same derivative. -/
theorem artinMatrixJacquet_curve_hasDerivAt {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0)
    {γ : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : γ 0 = 1) (hd : HasDerivAt γ X 0) :
    HasDerivAt (fun t => artinMatrixJacquet c (g * γ t))
      (artinMatrixJacquetDifferential c g X) 0 := by
  have hf := (artinMatrixRightJacquet_contDiffAt hc hg).differentiableAt
    (by simp) |>.hasFDerivAt
  have hf' : HasFDerivAt (fun Z : Matrix (Fin 2) (Fin 2) ℂ =>
      artinMatrixJacquet c (g * (1 + Z)))
      (fderiv ℝ (fun Z : Matrix (Fin 2) (Fin 2) ℂ =>
        artinMatrixJacquet c (g * (1 + Z))) 0) (γ 0 - 1) := by
    simpa only [hγ, sub_self] using hf
  have hcomp := hf'.comp_hasDerivAt 0 (hd.sub_const 1)
  have he : ((fun Z : Matrix (Fin 2) (Fin 2) ℂ =>
      artinMatrixJacquet c (g * (1 + Z))) ∘ fun t => γ t - 1) =
      fun t => artinMatrixJacquet c (g * γ t) := by
    funext t
    simp
  rw [he] at hcomp
  exact hcomp

theorem artinMatrixJacquetDifferential_cartan {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) :
    artinMatrixJacquetDifferential c (artinDiagonalMatrix y) (artinRealLieBasis 0) =
      (-4 : ℝ) • artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 (‖y‖ ^ 2) := by
  have hg : (artinDiagonalMatrix y).det ≠ 0 := by simp [artinDiagonalMatrix, hy]
  have hd : HasDerivAt artinCartanMatrix (artinRealLieBasis 0) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa [artinRealLieBasis] using artinCartanMatrix_tangent i j
  exact (artinMatrixJacquet_curve_hasDerivAt hc hg artinCartanMatrix_zero hd).unique
    (artinMatrixJacquet_cartan_hasDerivAt hc hy)

theorem artinMatrixJacquetDifferential_upper {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) (v : ℂ) :
    artinMatrixJacquetDifferential c (artinDiagonalMatrix y) (!![0, v; 0, 0]) =
      Complex.I * c * (y * v).re * artinMatrixJacquet c (artinDiagonalMatrix y) := by
  have hg : (artinDiagonalMatrix y).det ≠ 0 := by simp [artinDiagonalMatrix, hy]
  have h0 : artinUpperRootMatrix ((0 : ℂ) * v) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [artinUpperRootMatrix]
  have hd : HasDerivAt (fun t : ℝ => artinUpperRootMatrix ((t : ℂ) * v))
      (!![0, v; 0, 0]) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact hasDerivAt_const 0 1
    · simpa [artinUpperRootMatrix] using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v
    · exact hasDerivAt_const 0 0
    · exact hasDerivAt_const 0 1
  exact (artinMatrixJacquet_curve_hasDerivAt hc hg h0 hd).unique
    (artinMatrixJacquet_upper_hasDerivAt c y v)

theorem artinMatrixJacquetDifferential_compact_curve {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (a b : ℝ → ℂ)
    (hk : ∀ t, ‖a t‖ ^ 2 + ‖b t‖ ^ 2 = 1)
    (h0 : artinCompactRotation (a 0) (b 0) = 1)
    {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hd : HasDerivAt (fun t => artinCompactRotation (a t) (b t)) X 0) :
    artinMatrixJacquetDifferential c g X = 0 := by
  have he : (fun t => artinMatrixJacquet c (g * artinCompactRotation (a t) (b t))) =
      fun _ : ℝ => artinMatrixJacquet c g := by
    funext t
    exact artinMatrixJacquet_compact c g (hk t)
  have h := artinMatrixJacquet_curve_hasDerivAt hc hg h0 hd
  rw [he] at h
  exact h.unique (hasDerivAt_const 0 _)

/-- Actual right-curve covariance under compact conjugation. -/
theorem artinMatrixJacquetDifferential_compact_covariance {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0)
    {a b : ℂ} (hk : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    artinMatrixJacquetDifferential c (g * artinCompactRotation a b) X =
      artinMatrixJacquetDifferential c g
        (artinCompactRotation a b * X * (artinCompactRotation a b)⁻¹) := by
  let k := artinCompactRotation a b
  have hki : k⁻¹ * k = 1 := by
    rw [artinCompactRotation_inv hk]
    exact mul_eq_one_comm.mp (artinCompactRotation_mul_conjTranspose hk)
  have hgk : (g * k).det ≠ 0 := by
    rw [Matrix.det_mul, artinCompactRotation_det hk, mul_one]
    exact hg
  have hγ (Z : Matrix (Fin 2) (Fin 2) ℂ) :
      HasDerivAt (fun t : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℂ) + t • Z) Z 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const Z).const_add 1
  have h1 := artinMatrixJacquet_curve_hasDerivAt hc hgk (by simp) (hγ X)
  have h2 := artinMatrixJacquet_curve_hasDerivAt hc hg (by simp) (hγ (k * X * k⁻¹))
  have he : (fun t : ℝ => artinMatrixJacquet c ((g * k) * (1 + t • X))) =
      fun t : ℝ => artinMatrixJacquet c (g * (1 + t • (k * X * k⁻¹))) := by
    funext t
    have hm : (g * k) * (1 + t • X) = (g * (1 + t • (k * X * k⁻¹))) * k := by
      simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hki]
    rw [hm]
    exact artinMatrixJacquet_compact c _ hk
  rw [he] at h1
  exact h1.unique h2

end
end SimultaneousPrimitiveRoots

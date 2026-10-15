module

public import SimultaneousPrimitiveRoots.MatrixJacquetDifferential
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate Matrix.Norms.Elementwise
noncomputable section

theorem artinCompactRotation_curve_hasDerivAt {a b : ℝ → ℂ} {a' b' : ℂ}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) :
    HasDerivAt (fun t => artinCompactRotation (a t) (b t))
      (!![a', b'; -conj b', conj a']) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · simpa [artinCompactRotation, Complex.star_def] using hb.star.fun_neg
  · simpa [artinCompactRotation, Complex.star_def] using ha.star

theorem artinCompactRotation_trigonometric_normalized {d : ℂ} (hd : ‖d‖ = 1) (t : ℝ) :
    ‖(Real.cos t : ℂ)‖ ^ 2 + ‖d * (Real.sin t : ℂ)‖ ^ 2 = 1 := by
  simp only [norm_mul, hd, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [add_comm] using Real.sin_sq_add_cos_sq t

theorem artinMatrixJacquetDifferential_iH_zero {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    artinMatrixJacquetDifferential c g (artinRealLieBasis 1) = 0 := by
  have ha : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) Complex.I 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul Complex.I).cexp)
  have hk : ∀ t : ℝ, ‖Complex.exp (Complex.I * (t : ℂ))‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2 = 1 := by
    intro t
    simp [Complex.norm_exp, Complex.mul_re]
  have h0 : artinCompactRotation (Complex.exp (Complex.I * (0 : ℂ))) 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [artinCompactRotation]
  have hd := artinCompactRotation_curve_hasDerivAt ha (hasDerivAt_const 0 (0 : ℂ))
  have hd' : HasDerivAt (fun t : ℝ =>
      artinCompactRotation (Complex.exp (Complex.I * (t : ℂ))) 0) (artinRealLieBasis 1) 0 := by
    simpa [artinRealLieBasis] using hd
  exact artinMatrixJacquetDifferential_compact_curve hc hg _ _ hk h0 hd'

theorem artinMatrixJacquetDifferential_offdiag_compact_zero {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) {d : ℂ} (hd : ‖d‖ = 1) :
    artinMatrixJacquetDifferential c g (!![0, d; -conj d, 0]) = 0 := by
  have ha : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) 0 0 := by
    simpa using (Real.hasDerivAt_cos (0 : ℝ)).ofReal_comp
  have hb : HasDerivAt (fun t : ℝ => d * (Real.sin t : ℂ)) d 0 := by
    simpa using ((Real.hasDerivAt_sin (0 : ℝ)).ofReal_comp.const_mul d)
  have h0 : artinCompactRotation (Real.cos 0 : ℂ) (d * (Real.sin 0 : ℂ)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [artinCompactRotation]
  exact artinMatrixJacquetDifferential_compact_curve hc hg _ _
    (artinCompactRotation_trigonometric_normalized hd) h0
    (by simpa using artinCompactRotation_curve_hasDerivAt ha hb)

theorem artinMatrixJacquetDifferential_EF_zero {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    artinMatrixJacquetDifferential c g (artinRealLieBasis 2 - artinRealLieBasis 4) = 0 := by
  have he : artinRealLieBasis 2 - artinRealLieBasis 4 = (!![0, 1; -conj (1 : ℂ), 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [artinRealLieBasis]
  rw [he]
  exact artinMatrixJacquetDifferential_offdiag_compact_zero hc hg (by simp)

theorem artinMatrixJacquetDifferential_iEF_zero {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    artinMatrixJacquetDifferential c g (artinRealLieBasis 3 + artinRealLieBasis 5) = 0 := by
  have he : artinRealLieBasis 3 + artinRealLieBasis 5 =
      (!![0, Complex.I; -conj Complex.I, 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [artinRealLieBasis]
  rw [he]
  exact artinMatrixJacquetDifferential_offdiag_compact_zero hc hg (by simp)

/-- The actual differential on all traceless matrices, with compact directions
proved to vanish by genuine compact curves. -/
theorem artinMatrixJacquetDifferential_traceless_formula {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) (x v z : ℂ) :
    artinMatrixJacquetDifferential c (artinDiagonalMatrix y) (artinTracelessMatrix x v z) =
      x.re • ((-4 : ℝ) • artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 (‖y‖ ^ 2)) +
        (v.re + z.re) • (Complex.I * c * y.re * artinMatrixJacquet c (artinDiagonalMatrix y)) +
        (v.im - z.im) • (Complex.I * c * (y * Complex.I).re *
          artinMatrixJacquet c (artinDiagonalMatrix y)) := by
  have hg : (artinDiagonalMatrix y).det ≠ 0 := by simp [artinDiagonalMatrix, hy]
  rw [artinRealLinear_compact_reduction (artinMatrixJacquetDifferential c (artinDiagonalMatrix y))
    (artinMatrixJacquetDifferential_iH_zero hc hg)
    (artinMatrixJacquetDifferential_EF_zero hc hg)
    (artinMatrixJacquetDifferential_iEF_zero hc hg)]
  rw [artinMatrixJacquetDifferential_cartan hc hy]
  have hE : artinMatrixJacquetDifferential c (artinDiagonalMatrix y) (artinRealLieBasis 2) =
      Complex.I * c * y.re * artinMatrixJacquet c (artinDiagonalMatrix y) := by
    simpa [artinRealLieBasis] using artinMatrixJacquetDifferential_upper hc hy 1
  have hiE : artinMatrixJacquetDifferential c (artinDiagonalMatrix y) (artinRealLieBasis 3) =
      Complex.I * c * (y * Complex.I).re * artinMatrixJacquet c (artinDiagonalMatrix y) := by
    simpa [artinRealLieBasis] using artinMatrixJacquetDifferential_upper hc hy Complex.I
  rw [hE, hiE]

theorem artinMatrixJacquetDifferential_rotated_formula {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) {a b : ℂ} (hk : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x v z : ℂ) :
    artinMatrixJacquetDifferential c (artinDiagonalMatrix y * artinCompactRotation a b)
      (artinTracelessMatrix x v z) =
      (artinRotatedDiagonal a b x v z).re •
        ((-4 : ℝ) • artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 (‖y‖ ^ 2)) +
      ((artinRotatedUpper a b x v z).re + (artinRotatedLower a b x v z).re) •
        (Complex.I * c * y.re * artinMatrixJacquet c (artinDiagonalMatrix y)) +
      ((artinRotatedUpper a b x v z).im - (artinRotatedLower a b x v z).im) •
        (Complex.I * c * (y * Complex.I).re * artinMatrixJacquet c (artinDiagonalMatrix y)) := by
  have hg : (artinDiagonalMatrix y).det ≠ 0 := by simp [artinDiagonalMatrix, hy]
  rw [artinMatrixJacquetDifferential_compact_covariance hc hg hk,
    artinCompactRotation_ad_coordinates hk]
  exact artinMatrixJacquetDifferential_traceless_formula hc hy _ _ _

end
end SimultaneousPrimitiveRoots

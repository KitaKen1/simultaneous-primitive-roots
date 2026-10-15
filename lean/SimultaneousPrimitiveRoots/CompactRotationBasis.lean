module

public import SimultaneousPrimitiveRoots.SphericalBesselProfiles
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots
open Complex Matrix
open scoped BigOperators ComplexConjugate ContDiff
noncomputable section

/-- An actual complex matrix; normalization is imposed separately. -/
def artinCompactRotation (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![a, b; -conj b, conj a]

def artinTracelessMatrix (x y z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x, y; z, -x]

def artinRotatedDiagonal (a b x y z : ℂ) : ℂ :=
  (a * conj a - b * conj b) * x + a * conj b * y + b * conj a * z

def artinRotatedUpper (a b x y z : ℂ) : ℂ :=
  -2 * a * b * x + a ^ 2 * y - b ^ 2 * z

def artinRotatedLower (a b x y z : ℂ) : ℂ :=
  -2 * conj a * conj b * x - conj b ^ 2 * y + conj a ^ 2 * z

theorem artinCompactRotation_conjTranspose (a b : ℂ) :
    (artinCompactRotation a b)ᴴ = !![conj a, -b; conj b, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [artinCompactRotation, Matrix.conjTranspose_apply]

theorem artinCompactRotation_mul_conjTranspose {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    artinCompactRotation a b * (artinCompactRotation a b)ᴴ = 1 := by
  have hc : a * conj a + b * conj b = 1 := by
    rw [Complex.mul_conj', Complex.mul_conj', ← Complex.ofReal_pow,
      ← Complex.ofReal_pow, ← Complex.ofReal_add, h]
    rfl
  rw [artinCompactRotation_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [artinCompactRotation, Matrix.mul_apply, Fin.sum_univ_two] using hc
  · simp [artinCompactRotation, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [artinCompactRotation, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simpa [artinCompactRotation, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm, mul_comm] using hc

theorem artinCompactRotation_inv {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    (artinCompactRotation a b)⁻¹ = (artinCompactRotation a b)ᴴ :=
  Matrix.inv_eq_right_inv (artinCompactRotation_mul_conjTranspose h)

theorem artinCompactRotation_det {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : (artinCompactRotation a b).det = 1 := by
  simp only [artinCompactRotation, Matrix.det_fin_two_of, mul_neg, sub_neg_eq_add]
  rw [Complex.mul_conj', Complex.mul_conj', ← Complex.ofReal_pow,
    ← Complex.ofReal_pow, ← Complex.ofReal_add, h]
  rfl

theorem artinCompactRotation_mem_specialUnitaryGroup {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    artinCompactRotation a b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, artinCompactRotation_det h⟩
  exact Matrix.mem_unitaryGroup_iff.mpr (artinCompactRotation_mul_conjTranspose h)

theorem artinCompactRotation_conjugate_coordinates (a b x y z : ℂ) :
    artinCompactRotation a b * artinTracelessMatrix x y z *
      (artinCompactRotation a b)ᴴ =
    artinTracelessMatrix (artinRotatedDiagonal a b x y z)
      (artinRotatedUpper a b x y z) (artinRotatedLower a b x y z) := by
  rw [artinCompactRotation_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinCompactRotation, artinTracelessMatrix, artinRotatedDiagonal,
      artinRotatedUpper, artinRotatedLower, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem artinCompactRotation_ad_coordinates {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x y z : ℂ) :
    artinCompactRotation a b * artinTracelessMatrix x y z *
      (artinCompactRotation a b)⁻¹ =
    artinTracelessMatrix (artinRotatedDiagonal a b x y z)
      (artinRotatedUpper a b x y z) (artinRotatedLower a b x y z) := by
  rw [artinCompactRotation_inv h]
  exact artinCompactRotation_conjugate_coordinates a b x y z

theorem artinTracelessMatrix_trace (x y z : ℂ) :
    (artinTracelessMatrix x y z).trace = 0 := by
  simp [artinTracelessMatrix, Matrix.trace_fin_two_of]

theorem artinMatrix_eq_traceless {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X.trace = 0) : X = artinTracelessMatrix (X 0 0) (X 0 1) (X 1 0) := by
  have hd : X 1 1 = -X 0 0 := by
    rw [Matrix.trace_fin_two] at hX
    exact eq_neg_of_add_eq_zero_right hX
  ext i j
  fin_cases i <;> fin_cases j <;> simp [artinTracelessMatrix, hd]

/-- H, iH, E, iE, F, iF, with scalar combinations taken over the reals. -/
def artinRealLieBasis : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, -1], !![I, 0; 0, -I], !![0, 1; 0, 0],
    !![0, I; 0, 0], !![0, 0; 1, 0], !![0, 0; I, 0]]

def artinRealLieCoordinates (x y z : ℂ) : Fin 6 → ℝ :=
  ![x.re, x.im, y.re, y.im, z.re, z.im]

theorem artinTracelessMatrix_real_expansion (x y z : ℂ) :
    artinTracelessMatrix x y z =
      ∑ i : Fin 6, artinRealLieCoordinates x y z i • artinRealLieBasis i := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinTracelessMatrix, artinRealLieCoordinates, artinRealLieBasis,
      Fin.sum_univ_succ, Complex.ext_iff]

theorem artinRealLieBasis_coefficients_eq_zero (c : Fin 6 → ℝ)
    (h : ∑ i : Fin 6, c i • artinRealLieBasis i = 0) : ∀ i, c i = 0 := by
  have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 0) h
  have h01 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 0 1) h
  have h10 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X 1 0) h
  simp [Fin.sum_univ_succ, artinRealLieBasis, Complex.ext_iff] at h00 h01 h10
  intro i
  fin_cases i
  · exact h00.1
  · exact h00.2
  · exact h01.1
  · exact h01.2
  · exact h10.1
  · exact h10.2

theorem artinRealLieBasis_linearIndependent : LinearIndependent ℝ artinRealLieBasis :=
  Fintype.linearIndependent_iff.mpr artinRealLieBasis_coefficients_eq_zero

theorem artinCompactRotation_ad_real_expansion {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x y z : ℂ) :
    artinCompactRotation a b * artinTracelessMatrix x y z *
      (artinCompactRotation a b)⁻¹ =
      ∑ i : Fin 6, artinRealLieCoordinates (artinRotatedDiagonal a b x y z)
        (artinRotatedUpper a b x y z) (artinRotatedLower a b x y z) i •
          artinRealLieBasis i := by
  rw [artinCompactRotation_ad_coordinates h]
  exact artinTracelessMatrix_real_expansion _ _ _

theorem artinCompactRotation_norm_entries {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) : ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  constructor <;> nlinarith [sq_nonneg ‖a‖, sq_nonneg ‖b‖, norm_nonneg a, norm_nonneg b]

theorem artinUnitProduct_mul_norm_le {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x : ℂ) : ‖a * b * x‖ ≤ ‖x‖ := by
  calc
    _ = (‖a‖ * ‖b‖) * ‖x‖ := by rw [norm_mul, norm_mul]
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
      (by simpa using mul_le_mul ha hb (norm_nonneg b) (by norm_num : (0 : ℝ) ≤ 1))
      (norm_nonneg x)
    _ = ‖x‖ := one_mul _

theorem artinRotatedDiagonal_norm_le {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x y z : ℂ) :
    ‖artinRotatedDiagonal a b x y z‖ ≤ 2 * ‖x‖ + ‖y‖ + ‖z‖ := by
  have hac : ‖conj a‖ ≤ 1 := by simpa using ha
  have hbc : ‖conj b‖ ≤ 1 := by simpa using hb
  have h1 := artinUnitProduct_mul_norm_le ha hac x
  have h2 := artinUnitProduct_mul_norm_le hb hbc x
  have h3 := artinUnitProduct_mul_norm_le ha hbc y
  have h4 := artinUnitProduct_mul_norm_le hb hac z
  have he : artinRotatedDiagonal a b x y z =
      a * conj a * x - b * conj b * x + a * conj b * y + b * conj a * z := by
    unfold artinRotatedDiagonal
    ring
  rw [he]
  have ht1 := norm_sub_le (a * conj a * x) (b * conj b * x)
  have ht2 := norm_add_le (a * conj a * x - b * conj b * x) (a * conj b * y)
  have ht3 := norm_add_le (a * conj a * x - b * conj b * x + a * conj b * y)
    (b * conj a * z)
  linarith

theorem artinRotatedUpper_norm_le {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x y z : ℂ) :
    ‖artinRotatedUpper a b x y z‖ ≤ 2 * ‖x‖ + ‖y‖ + ‖z‖ := by
  have h1 : ‖-2 * a * b * x‖ ≤ 2 * ‖x‖ := by
    have he : -2 * a * b * x = -(2 : ℂ) * (a * b * x) := by ring
    rw [he, norm_mul]
    rw [show ‖-(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left (artinUnitProduct_mul_norm_le ha hb x)
      (by norm_num : (0 : ℝ) ≤ 2)
  have h2 : ‖a ^ 2 * y‖ ≤ ‖y‖ := by
    simpa only [pow_two] using artinUnitProduct_mul_norm_le ha ha y
  have h3 : ‖b ^ 2 * z‖ ≤ ‖z‖ := by
    simpa only [pow_two] using artinUnitProduct_mul_norm_le hb hb z
  have ht1 := norm_add_le (-2 * a * b * x) (a ^ 2 * y)
  have ht2 := norm_sub_le (-2 * a * b * x + a ^ 2 * y) (b ^ 2 * z)
  unfold artinRotatedUpper
  linarith

theorem artinRotatedLower_norm_le {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (x y z : ℂ) :
    ‖artinRotatedLower a b x y z‖ ≤ 2 * ‖x‖ + ‖y‖ + ‖z‖ := by
  have he : artinRotatedLower a b x y z = artinRotatedUpper (conj a) (conj b) x z y := by
    unfold artinRotatedLower artinRotatedUpper
    ring
  rw [he]
  have h := artinRotatedUpper_norm_le (a := conj a) (b := conj b)
    (by simpa using ha) (by simpa using hb) x z y
  linarith

theorem artinCompactRotation_real_coefficients_bound {a b : ℂ}
    (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x y z : ℂ) (i : Fin 6) :
    |artinRealLieCoordinates (artinRotatedDiagonal a b x y z)
      (artinRotatedUpper a b x y z) (artinRotatedLower a b x y z) i| ≤
        2 * ‖x‖ + ‖y‖ + ‖z‖ := by
  obtain ⟨ha, hb⟩ := artinCompactRotation_norm_entries h
  have hd := artinRotatedDiagonal_norm_le ha hb x y z
  have hu := artinRotatedUpper_norm_le ha hb x y z
  have hl := artinRotatedLower_norm_le ha hb x y z
  fin_cases i
  · exact (Complex.abs_re_le_norm _).trans hd
  · exact (Complex.abs_im_le_norm _).trans hd
  · exact (Complex.abs_re_le_norm _).trans hu
  · exact (Complex.abs_im_le_norm _).trans hu
  · exact (Complex.abs_re_le_norm _).trans hl
  · exact (Complex.abs_im_le_norm _).trans hl

/-- Compact directions are hypotheses on the actual real-linear map, not an
unproved representation identity. No complex-linearity assumption is used. -/
theorem artinRealLinear_compact_reduction {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] V)
    (hH : L (artinRealLieBasis 1) = 0)
    (hEF : L (artinRealLieBasis 2 - artinRealLieBasis 4) = 0)
    (hiEF : L (artinRealLieBasis 3 + artinRealLieBasis 5) = 0) (x y z : ℂ) :
    L (artinTracelessMatrix x y z) =
      x.re • L (artinRealLieBasis 0) + (y.re + z.re) • L (artinRealLieBasis 2) +
        (y.im - z.im) • L (artinRealLieBasis 3) := by
  have hF : L (artinRealLieBasis 4) = L (artinRealLieBasis 2) := by
    rw [map_sub, sub_eq_zero] at hEF
    exact hEF.symm
  have hiF : L (artinRealLieBasis 5) = -L (artinRealLieBasis 3) := by
    rw [map_add] at hiEF
    exact eq_neg_of_add_eq_zero_right hiEF
  rw [artinTracelessMatrix_real_expansion, map_sum]
  simp [Fin.sum_univ_succ, artinRealLieCoordinates, map_smul, hH, hF, hiF,
    add_smul, sub_smul]
  abel

theorem artinRealLinear_rotated_compact_reduction {V : Type*}
    [AddCommGroup V] [Module ℝ V] (L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] V)
    (hH : L (artinRealLieBasis 1) = 0)
    (hEF : L (artinRealLieBasis 2 - artinRealLieBasis 4) = 0)
    (hiEF : L (artinRealLieBasis 3 + artinRealLieBasis 5) = 0)
    {a b : ℂ} (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x y z : ℂ) :
    L (artinCompactRotation a b * artinTracelessMatrix x y z *
      (artinCompactRotation a b)⁻¹) =
      (artinRotatedDiagonal a b x y z).re • L (artinRealLieBasis 0) +
      ((artinRotatedUpper a b x y z).re + (artinRotatedLower a b x y z).re) •
        L (artinRealLieBasis 2) +
      ((artinRotatedUpper a b x y z).im - (artinRotatedLower a b x y z).im) •
        L (artinRealLieBasis 3) := by
  rw [artinCompactRotation_ad_coordinates h]
  exact artinRealLinear_compact_reduction L hH hEF hiEF _ _ _

def artinCompactRotationParameter :=
  {p : ℂ × ℂ // ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 1}

def artinCompactRotationCoefficients (x y z : ℂ) (p : artinCompactRotationParameter)
    (i : Fin 6) : ℂ :=
  (artinRealLieCoordinates (artinRotatedDiagonal p.val.1 p.val.2 x y z)
    (artinRotatedUpper p.val.1 p.val.2 x y z)
    (artinRotatedLower p.val.1 p.val.2 x y z) i : ℝ)

theorem artinCompactRotationCoefficients_norm_le (x y z : ℂ)
    (p : artinCompactRotationParameter) (i : Fin 6) :
    ‖artinCompactRotationCoefficients x y z p i‖ ≤ 2 * ‖x‖ + ‖y‖ + ‖z‖ := by
  simpa only [artinCompactRotationCoefficients, Complex.norm_real, Real.norm_eq_abs] using
    artinCompactRotation_real_coefficients_bound p.prop x y z i

def artinRotatedRealLinearProfile (L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] (ℝ → ℂ))
    (x y z : ℂ) (p : artinCompactRotationParameter) : ℝ → ℂ :=
  L (artinCompactRotation p.val.1 p.val.2 * artinTracelessMatrix x y z *
    (artinCompactRotation p.val.1 p.val.2)⁻¹)

theorem artinRotatedRealLinearProfile_eq_finite_sum
    (L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] (ℝ → ℂ)) (x y z : ℂ)
    (p : artinCompactRotationParameter) :
    artinRotatedRealLinearProfile L x y z p =
      artinFiniteProfileCombination Finset.univ (artinCompactRotationCoefficients x y z)
        (fun i => L (artinRealLieBasis i)) p := by
  unfold artinRotatedRealLinearProfile
  rw [artinCompactRotation_ad_real_expansion p.prop, map_sum]
  funext u
  simp [artinFiniteProfileCombination, artinCompactRotationCoefficients,
    Finset.sum_apply, map_smul, Complex.real_smul]

/-- A common all-order bound for the actual conjugated matrix under a fixed
real-linear profile map, assuming the six basis profiles' analytic bounds. -/
theorem artinRotatedRealLinearProfile_uniform_two_ended
    (L : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] (ℝ → ℂ)) (x y z : ℂ) {α A : ℝ}
    (hfα : ∀ i, ContDiff ℝ ∞
      (artinMellinLogPullback (L (artinRealLieBasis i)) ((-α : ℝ) : ℂ)))
    (hfA : ∀ i, ContDiff ℝ ∞
      (artinMellinLogPullback (L (artinRealLieBasis i)) (A : ℂ)))
    (hbα : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j
        (artinMellinLogPullback (L (artinRealLieBasis i)) ((-α : ℝ) : ℂ)) v‖ ≤ M)
    (hbA : ∀ i j, ∃ M, 0 < M ∧ ∀ v,
      ‖iteratedDeriv j
        (artinMellinLogPullback (L (artinRealLieBasis i)) (A : ℂ)) v‖ ≤ M) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet (artinRotatedRealLinearProfile L x y z p) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  have hC : 0 < max 1 (2 * ‖x‖ + ‖y‖ + ‖z‖) := lt_of_lt_of_le
    (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have ha : ∀ p i, i ∈ (Finset.univ : Finset (Fin 6)) →
      ‖artinCompactRotationCoefficients x y z p i‖ ≤
        max 1 (2 * ‖x‖ + ‖y‖ + ‖z‖) := fun p i _ =>
    (artinCompactRotationCoefficients_norm_le x y z p i).trans (le_max_right _ _)
  simpa only [artinRotatedRealLinearProfile_eq_finite_sum] using
    artinFiniteProfileCombination_uniform_two_ended Finset.univ
      (artinCompactRotationCoefficients x y z) hC ha hfα hfA hbα hbA j

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.ComplexJacquetGaussian
public import SimultaneousPrimitiveRoots.CompactRotationBasis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate
noncomputable section

def artinUpperRootMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, z; 0, 1]
def artinDiagonalMatrix (y : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![y, 0; 0, 1]
def artinWeylMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The ordinary spherical quotient on actual complex matrices. -/
def artinMatrixSphericalSection (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (‖g.det‖ / (‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2)) ^ (4 / 3 : ℝ)

def artinMatrixJacquetIntegrand (c : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℂ :=
  (artinMatrixSphericalSection (artinWeylMatrix * artinUpperRootMatrix x * g) : ℂ) *
    Complex.exp (-Complex.I * c * x.re)

def artinMatrixJacquet (c : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∫ x : ℂ, artinMatrixJacquetIntegrand c g x

theorem artinUpperRootMatrix_mul (x z : ℂ) :
    artinUpperRootMatrix x * artinUpperRootMatrix z = artinUpperRootMatrix (x + z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinUpperRootMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem artinDiagonalMatrix_upper (y z : ℂ) :
    artinDiagonalMatrix y * artinUpperRootMatrix z =
      artinUpperRootMatrix (y * z) * artinDiagonalMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinUpperRootMatrix, artinDiagonalMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem artinWeyl_upper_diagonal (x y : ℂ) :
    artinWeylMatrix * artinUpperRootMatrix x * artinDiagonalMatrix y =
      !![0, -1; y, x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinWeylMatrix, artinUpperRootMatrix, artinDiagonalMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem artinMatrixSphericalSection_jacquet {y : ℂ} (hy : y ≠ 0) (x : ℂ) :
    artinMatrixSphericalSection
      (artinWeylMatrix * artinUpperRootMatrix x * artinDiagonalMatrix y) =
      ‖y‖ ^ (4 / 3 : ℝ) * artinComplexJacquetSection ‖y‖ x := by
  rw [artinWeyl_upper_diagonal]
  simp only [artinMatrixSphericalSection, Matrix.det_fin_two_of, zero_mul,
    neg_one_mul, sub_neg_eq_add, zero_add, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, artinComplexJacquetSection]
  rw [Real.div_rpow (norm_nonneg _) (by positivity), Real.rpow_neg (by positivity)]
  rfl

theorem artinComplexRow_compact_norm (u v a b : ℂ) :
    ‖u * a - v * conj b‖ ^ 2 + ‖u * b + v * conj a‖ ^ 2 =
      (‖u‖ ^ 2 + ‖v‖ ^ 2) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem artinMatrixSphericalSection_compact (g : Matrix (Fin 2) (Fin 2) ℂ)
    {a b : ℂ} (hk : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    artinMatrixSphericalSection (g * artinCompactRotation a b) =
      artinMatrixSphericalSection g := by
  have hrow : ‖(g * artinCompactRotation a b) 1 0‖ ^ 2 +
      ‖(g * artinCompactRotation a b) 1 1‖ ^ 2 = ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, artinCompactRotation,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_neg, ← sub_eq_add_neg]
    rw [artinComplexRow_compact_norm, hk, mul_one]
  rw [artinMatrixSphericalSection, Matrix.det_mul, artinCompactRotation_det hk,
    mul_one, hrow]
  rfl

theorem artinMatrixJacquetIntegrand_diagonal {y : ℂ} (hy : y ≠ 0) (c : ℝ) (x : ℂ) :
    artinMatrixJacquetIntegrand c (artinDiagonalMatrix y) x =
      ((‖y‖ ^ (4 / 3 : ℝ) : ℝ) : ℂ) * artinComplexJacquetIntegrand ‖y‖ c x := by
  rw [artinMatrixJacquetIntegrand, artinMatrixSphericalSection_jacquet hy x,
    artinComplexJacquetIntegrand, Complex.ofReal_mul, mul_assoc]

theorem artinMatrixJacquet_diagonal {y : ℂ} (hy : y ≠ 0) (c : ℝ) :
    artinMatrixJacquet c (artinDiagonalMatrix y) = artinComplexJacquetIntegral ‖y‖ c := by
  unfold artinMatrixJacquet
  simp_rw [artinMatrixJacquetIntegrand_diagonal hy c]
  rw [integral_const_mul]
  rfl

theorem artinMatrixJacquetIntegrand_diagonal_integrable {y : ℂ} (hy : y ≠ 0) (c : ℝ) :
    Integrable (artinMatrixJacquetIntegrand c (artinDiagonalMatrix y)) := by
  have h := (artinComplexJacquetIntegrand_integrable (norm_pos_iff.mpr hy) c).const_mul
    (((‖y‖ ^ (4 / 3 : ℝ) : ℝ) : ℂ))
  apply h.congr
  exact Filter.Eventually.of_forall fun x =>
    (artinMatrixJacquetIntegrand_diagonal hy c x).symm

theorem artinMatrixSphericalSection_scalar (g : Matrix (Fin 2) (Fin 2) ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    artinMatrixSphericalSection (z • g) = artinMatrixSphericalSection g := by
  unfold artinMatrixSphericalSection
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.smul_apply, smul_eq_mul,
    norm_mul, norm_pow, mul_pow]
  rw [← mul_add]
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))]

theorem artinMatrixJacquetIntegrand_compact (c : ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ}
    (hk : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (x : ℂ) :
    artinMatrixJacquetIntegrand c (g * artinCompactRotation a b) x =
      artinMatrixJacquetIntegrand c g x := by
  unfold artinMatrixJacquetIntegrand
  rw [← Matrix.mul_assoc, artinMatrixSphericalSection_compact _ hk]

theorem artinMatrixJacquet_compact (c : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    {a b : ℂ} (hk : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    artinMatrixJacquet c (g * artinCompactRotation a b) = artinMatrixJacquet c g := by
  unfold artinMatrixJacquet
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => artinMatrixJacquetIntegrand_compact c g hk x

theorem artinMatrixJacquet_compact_curve_deriv (c : ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℝ → ℂ)
    (hk : ∀ t, ‖a t‖ ^ 2 + ‖b t‖ ^ 2 = 1) (t : ℝ) :
    deriv (fun s => artinMatrixJacquet c (g * artinCompactRotation (a s) (b s))) t = 0 := by
  have he : (fun s => artinMatrixJacquet c (g * artinCompactRotation (a s) (b s))) =
      fun _ : ℝ => artinMatrixJacquet c g := by
    funext s
    exact artinMatrixJacquet_compact c g (hk s)
  rw [he, deriv_const]

theorem artinMatrixJacquetIntegrand_upper (c : ℝ) (y z x : ℂ) :
    artinMatrixJacquetIntegrand c (artinDiagonalMatrix y * artinUpperRootMatrix z) x =
      Complex.exp (Complex.I * c * (y * z).re) *
        artinMatrixJacquetIntegrand c (artinDiagonalMatrix y) (x + y * z) := by
  have hm : artinWeylMatrix * artinUpperRootMatrix x *
      (artinDiagonalMatrix y * artinUpperRootMatrix z) =
      artinWeylMatrix * artinUpperRootMatrix (x + y * z) * artinDiagonalMatrix y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [artinWeylMatrix, artinUpperRootMatrix, artinDiagonalMatrix,
        Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  unfold artinMatrixJacquetIntegrand
  rw [hm]
  calc
    _ = (artinMatrixSphericalSection
        (artinWeylMatrix * artinUpperRootMatrix (x + y * z) * artinDiagonalMatrix y) : ℂ) *
        (Complex.exp (Complex.I * c * (y * z).re) *
          Complex.exp (-Complex.I * c * (x + y * z).re)) := by
      rw [← Complex.exp_add]
      congr 1
      congr 1
      simp only [Complex.add_re]
      push_cast
      ring
    _ = _ := by ring

theorem artinMatrixJacquet_upper (c : ℝ) (y z : ℂ) :
    artinMatrixJacquet c (artinDiagonalMatrix y * artinUpperRootMatrix z) =
      Complex.exp (Complex.I * c * (y * z).re) *
        artinMatrixJacquet c (artinDiagonalMatrix y) := by
  unfold artinMatrixJacquet
  simp_rw [artinMatrixJacquetIntegrand_upper]
  rw [integral_const_mul, integral_add_right_eq_self]

theorem artinMatrixJacquetIntegrand_upper_integrable {y : ℂ} (hy : y ≠ 0)
    (c : ℝ) (z : ℂ) :
    Integrable (artinMatrixJacquetIntegrand c
      (artinDiagonalMatrix y * artinUpperRootMatrix z)) := by
  have h := ((artinMatrixJacquetIntegrand_diagonal_integrable hy c).comp_add_right
    (y * z)).const_mul (Complex.exp (Complex.I * c * (y * z).re))
  apply h.congr
  exact Filter.Eventually.of_forall fun x =>
    (artinMatrixJacquetIntegrand_upper c y z x).symm

/-- Differentiate an actual right upper-root curve after computing its integral. -/
theorem artinMatrixJacquet_upper_hasDerivAt (c : ℝ) (y v : ℂ) :
    HasDerivAt (fun t : ℝ => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinUpperRootMatrix ((t : ℂ) * v)))
      (Complex.I * c * (y * v).re * artinMatrixJacquet c (artinDiagonalMatrix y)) 0 := by
  have he : (fun t : ℝ => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinUpperRootMatrix ((t : ℂ) * v))) =
      fun t : ℝ => Complex.exp ((Complex.I * c * (y * v).re) * (t : ℂ)) *
        artinMatrixJacquet c (artinDiagonalMatrix y) := by
    funext t
    rw [artinMatrixJacquet_upper]
    congr 1
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    push_cast
    ring
  rw [he]
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul
    (Complex.I * c * (y * v).re)).cexp).mul_const
      (artinMatrixJacquet c (artinDiagonalMatrix y))
  simpa using h

def artinMatrixUpperRootDerivative (c : ℝ) (y v : ℂ) : ℂ :=
  deriv (fun t : ℝ => artinMatrixJacquet c
    (artinDiagonalMatrix y * artinUpperRootMatrix ((t : ℂ) * v))) 0

theorem artinMatrixUpperRootDerivative_eq (c : ℝ) (y v : ℂ) :
    artinMatrixUpperRootDerivative c y v =
      Complex.I * c * (y * v).re * artinMatrixJacquet c (artinDiagonalMatrix y) :=
  (artinMatrixJacquet_upper_hasDerivAt c y v).deriv

theorem artinMatrixUpperRootDerivative_complex_plus (c : ℝ) (y : ℂ) :
    artinMatrixUpperRootDerivative c y 1 - Complex.I *
      artinMatrixUpperRootDerivative c y Complex.I =
      Complex.I * c * y * artinMatrixJacquet c (artinDiagonalMatrix y) := by
  simp only [artinMatrixUpperRootDerivative_eq, mul_one]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem artinMatrixUpperRootDerivative_complex_minus (c : ℝ) (y : ℂ) :
    artinMatrixUpperRootDerivative c y 1 + Complex.I *
      artinMatrixUpperRootDerivative c y Complex.I =
      Complex.I * c * conj y * artinMatrixJacquet c (artinDiagonalMatrix y) := by
  simp only [artinMatrixUpperRootDerivative_eq, mul_one]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

def artinMatrixRootWhittakerPlus (c : ℝ) (y : ℂ) : ℂ :=
  (Complex.I * c)⁻¹ * (artinMatrixUpperRootDerivative c y 1 -
    Complex.I * artinMatrixUpperRootDerivative c y Complex.I)

def artinMatrixRootWhittakerMinus (c : ℝ) (y : ℂ) : ℂ :=
  (Complex.I * c)⁻¹ * (artinMatrixUpperRootDerivative c y 1 +
    Complex.I * artinMatrixUpperRootDerivative c y Complex.I)

theorem artinMatrixRootWhittakerPlus_eq {c : ℝ} (hc : c ≠ 0) (y : ℂ) :
    artinMatrixRootWhittakerPlus c y = y * artinMatrixJacquet c (artinDiagonalMatrix y) := by
  rw [artinMatrixRootWhittakerPlus, artinMatrixUpperRootDerivative_complex_plus]
  have h : Complex.I * (c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr hc)
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem artinMatrixRootWhittakerMinus_eq {c : ℝ} (hc : c ≠ 0) (y : ℂ) :
    artinMatrixRootWhittakerMinus c y = conj y * artinMatrixJacquet c (artinDiagonalMatrix y) := by
  rw [artinMatrixRootWhittakerMinus, artinMatrixUpperRootDerivative_complex_minus]
  have h : Complex.I * (c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (Complex.ofReal_ne_zero.mpr hc)
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem artinMatrixJacquet_diagonal_bessel {c : ℝ} (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) :
    artinMatrixJacquet c (artinDiagonalMatrix y) =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        (‖y‖ : ℂ) * artinBesselKIntegral (1 / 3) (c * ‖y‖) := by
  rw [artinMatrixJacquet_diagonal hy,
    artinComplexJacquetIntegral_bessel (norm_pos_iff.mpr hy) hc]
  push_cast
  ring

theorem artinMatrixRootWhittakerPlus_bessel {c : ℝ} (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) :
    artinMatrixRootWhittakerPlus c y =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        ((‖y‖ ^ 2 : ℝ) : ℂ) * (y / (‖y‖ : ℂ)) *
          artinBesselKIntegral (1 / 3) (c * ‖y‖) := by
  rw [artinMatrixRootWhittakerPlus_eq (ne_of_gt hc), artinMatrixJacquet_diagonal_bessel hc hy]
  have hn : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  push_cast
  field_simp

theorem artinMatrixRootWhittakerMinus_bessel {c : ℝ} (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) :
    artinMatrixRootWhittakerMinus c y =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        ((‖y‖ ^ 2 : ℝ) : ℂ) * (conj y / (‖y‖ : ℂ)) *
          artinBesselKIntegral (1 / 3) (c * ‖y‖) := by
  rw [artinMatrixRootWhittakerMinus_eq (ne_of_gt hc), artinMatrixJacquet_diagonal_bessel hc hy]
  have hn : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  push_cast
  field_simp

def artinMatrixRootPhase (reverse : Bool) (phase : Circle) : ℂ :=
  if reverse then conj (phase : ℂ) else (phase : ℂ)

def artinMatrixRootRadialProfile (c : ℝ) (reverse : Bool) (phase : Circle) (u : ℝ) : ℂ :=
  if reverse then artinMatrixRootWhittakerMinus c ((Real.sqrt u : ℂ) * (phase : ℂ))
    else artinMatrixRootWhittakerPlus c ((Real.sqrt u : ℂ) * (phase : ℂ))

theorem artinMatrixRootPhase_norm (reverse : Bool) (phase : Circle) :
    ‖artinMatrixRootPhase reverse phase‖ = 1 := by
  cases reverse <;> simp [artinMatrixRootPhase]

theorem artinMatrixRootRadialProfile_eq_bessel {c u : ℝ} (hc : 0 < c)
    (hu : 0 < u) (reverse : Bool) (phase : Circle) :
    artinMatrixRootRadialProfile c reverse phase u =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        artinMatrixRootPhase reverse phase * artinBesselLocalProfile c u := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hy : (Real.sqrt u : ℂ) * (phase : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hs)) phase.coe_ne_zero
  have hn : ‖(Real.sqrt u : ℂ) * (phase : ℂ)‖ = Real.sqrt u := by
    rw [norm_mul, Circle.norm_coe, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_one]
  have hs0 : (Real.sqrt u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  cases reverse
  · change artinMatrixRootWhittakerPlus c ((Real.sqrt u : ℂ) * (phase : ℂ)) = _
    rw [artinMatrixRootWhittakerPlus_bessel hc hy, hn, Real.sq_sqrt hu.le]
    simp [artinMatrixRootPhase, artinBesselLocalProfile]
    field_simp [hs0]
  · change artinMatrixRootWhittakerMinus c ((Real.sqrt u : ℂ) * (phase : ℂ)) = _
    rw [artinMatrixRootWhittakerMinus_bessel hc hy, hn, Real.sq_sqrt hu.le]
    simp [artinMatrixRootPhase, artinBesselLocalProfile, map_mul, Complex.conj_ofReal]
    field_simp [hs0]

theorem artinMatrixRootRadialProfile_logJet {c : ℝ} (hc : 0 < c)
    (reverse : Bool) (phase : Circle) (j : ℕ) (u : ℝ) :
    artinLogProfileJet (artinMatrixRootRadialProfile c reverse phase) j u =
      (((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        artinMatrixRootPhase reverse phase) * artinLogProfileJet (artinBesselLocalProfile c) j u := by
  have he : (fun v : ℝ => artinMatrixRootRadialProfile c reverse phase (Real.exp (-v))) =
      fun v : ℝ => (((2 * Real.pi / Real.Gamma (4 / 3) *
        (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * artinMatrixRootPhase reverse phase) *
          artinBesselLocalProfile c (Real.exp (-v)) := by
    funext v
    exact artinMatrixRootRadialProfile_eq_bessel hc (Real.exp_pos _) reverse phase
  unfold artinLogProfileJet
  rw [he, iteratedDeriv_const_mul_field]

theorem artinBesselLocalProfile_logJet_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinBesselLocalProfile c) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinBesselLocalProfile_logJet_power_bound
    hc (σ := -α) (by linarith) j
  obtain ⟨N, hN, hbN⟩ := artinBesselLocalProfile_logJet_power_bound
    hc (σ := A) (by linarith) j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg (u ^ α) (u ^ (-A))
    (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hbM u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M N) (Real.rpow_nonneg hu.le _))
  · exact (hbN u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M N) (Real.rpow_nonneg hu.le _))

/-- The constant is chosen before the phase and before the two complex root combinations. -/
theorem artinMatrixRootRadialProfile_uniform_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ reverse phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixRootRadialProfile c reverse phase) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinBesselLocalProfile_logJet_two_ended hc hα hA j
  let C : ℝ := 2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ)
  have hC : 0 < C := artinComplexJacquet_prefactor_pos hc
  refine ⟨C * M, mul_pos hC hM, fun reverse phase u hu => ?_⟩
  rw [artinMatrixRootRadialProfile_logJet hc, norm_mul, norm_mul,
    artinMatrixRootPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hC.le]
  exact (mul_le_mul_of_nonneg_left (hb u hu) hC.le).trans_eq (mul_assoc _ _ _).symm

theorem artinMatrixRootRadialProfile_paper_bound {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ reverse phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixRootRadialProfile c reverse phase) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) :=
  artinMatrixRootRadialProfile_uniform_two_ended hc (by norm_num) hA j

theorem artinComplexJacquetRadialProfile_logJet {c : ℝ} (hc : 0 < c) (j : ℕ) (u : ℝ) :
    artinLogProfileJet (artinComplexJacquetRadialProfile c) j u =
      ((2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        artinLogProfileJet (artinSphericalBesselProfile c) j u := by
  have he : (fun v : ℝ => artinComplexJacquetRadialProfile c (Real.exp (-v))) =
      fun v : ℝ => ((2 * Real.pi / Real.Gamma (4 / 3) *
        (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * artinSphericalBesselProfile c (Real.exp (-v)) := by
    funext v
    exact artinComplexJacquetRadialProfile_eq_spherical hc (Real.exp_pos _)
  unfold artinLogProfileJet
  rw [he, iteratedDeriv_const_mul_field]

theorem artinComplexJacquetRadialProfile_logJet_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 1 / 3) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinComplexJacquetRadialProfile c) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinSphericalBesselProfile_logJet_two_ended hc hα hA j
  let C : ℝ := 2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ)
  have hC : 0 < C := artinComplexJacquet_prefactor_pos hc
  refine ⟨C * M, mul_pos hC hM, fun u hu => ?_⟩
  rw [artinComplexJacquetRadialProfile_logJet hc, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hC.le]
  exact (mul_le_mul_of_nonneg_left (hb u hu) hC.le).trans_eq (mul_assoc _ _ _).symm

end
end SimultaneousPrimitiveRoots

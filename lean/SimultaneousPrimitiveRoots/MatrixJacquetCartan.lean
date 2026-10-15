module

public import SimultaneousPrimitiveRoots.MatrixJacquetRoot
public import SimultaneousPrimitiveRoots.MultiplicativeMellinConvolution

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate
noncomputable section

/-- The actual real Cartan curve with tangent diag(1,-1). -/
def artinCartanMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp t : ℂ), 0; 0, (Real.exp (-t) : ℂ)]

theorem artinCartanMatrix_zero : artinCartanMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [artinCartanMatrix]

theorem artinCartanMatrix_det (t : ℝ) : (artinCartanMatrix t).det = 1 := by
  simp only [artinCartanMatrix, Matrix.det_fin_two_of, mul_zero, sub_zero]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

theorem artinCartanMatrix_tangent (i j : Fin 2) :
    HasDerivAt (fun t => artinCartanMatrix t i j) (!![1, 0; 0, -1] i j) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (Real.exp t : ℂ)) 1 0 := by
    simpa using (Real.hasDerivAt_exp (0 : ℝ)).ofReal_comp
  have hn : HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ)) (-1) 0 := by
    simpa using ((Real.hasDerivAt_exp (- (0 : ℝ))).comp 0
      (hasDerivAt_id (0 : ℝ)).neg).ofReal_comp
  fin_cases i <;> fin_cases j <;> change HasDerivAt _ _ _
  · exact hp
  · exact hasDerivAt_const 0 0
  · exact hasDerivAt_const 0 0
  · exact hn

theorem artinCartanMatrix_mul (s t : ℝ) :
    artinCartanMatrix s * artinCartanMatrix t = artinCartanMatrix (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinCartanMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Real.exp_add, Complex.ofReal_mul, mul_comm]

theorem artinMatrixJacquetIntegrand_scalar (c : ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) {z : ℂ} (hz : z ≠ 0) (x : ℂ) :
    artinMatrixJacquetIntegrand c (z • g) x = artinMatrixJacquetIntegrand c g x := by
  unfold artinMatrixJacquetIntegrand
  rw [Matrix.mul_smul, artinMatrixSphericalSection_scalar _ hz]

theorem artinMatrixJacquet_scalar (c : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    artinMatrixJacquet c (z • g) = artinMatrixJacquet c g := by
  unfold artinMatrixJacquet
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => artinMatrixJacquetIntegrand_scalar c g hz x

theorem artinDiagonalMatrix_cartan (y : ℂ) (t : ℝ) :
    artinDiagonalMatrix y * artinCartanMatrix t =
      (Real.exp (-t) : ℂ) • artinDiagonalMatrix (y * (Real.exp (2 * t) : ℂ)) := by
  have he : Real.exp (-t) * Real.exp (2 * t) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinDiagonalMatrix, artinCartanMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul]
  have he' : (Real.exp (-t) : ℂ) * (Real.exp (2 * t) : ℂ) =
      (Real.exp t : ℂ) := by exact_mod_cast he
  calc
    _ = y * ((Real.exp (-t) : ℂ) * (Real.exp (2 * t) : ℂ)) := by
      rw [he', Complex.ofReal_exp]
    _ = _ := by simp only [Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_ofNat]; ring

theorem artinMatrixJacquet_cartan (c : ℝ) (y : ℂ) (t : ℝ) :
    artinMatrixJacquet c (artinDiagonalMatrix y * artinCartanMatrix t) =
      artinMatrixJacquet c (artinDiagonalMatrix (y * (Real.exp (2 * t) : ℂ))) := by
  rw [artinDiagonalMatrix_cartan]
  exact artinMatrixJacquet_scalar c _
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

theorem artinMatrixJacquetIntegrand_cartan_integrable {y : ℂ} (hy : y ≠ 0)
    (c t : ℝ) :
    Integrable (artinMatrixJacquetIntegrand c
      (artinDiagonalMatrix y * artinCartanMatrix t)) := by
  rw [artinDiagonalMatrix_cartan]
  have h := artinMatrixJacquetIntegrand_diagonal_integrable
    (mul_ne_zero hy (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (2 * t)))) c
  apply h.congr
  exact Filter.Eventually.of_forall fun x =>
    (artinMatrixJacquetIntegrand_scalar c _
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) x).symm

theorem artinMatrixJacquet_diagonal_radial {y : ℂ} (hy : y ≠ 0) (c : ℝ) :
    artinMatrixJacquet c (artinDiagonalMatrix y) =
      artinComplexJacquetRadialProfile c (‖y‖ ^ 2) := by
  rw [artinMatrixJacquet_diagonal hy, artinComplexJacquetRadialProfile,
    Real.sqrt_sq (norm_nonneg _)]

theorem artinMatrixJacquet_cartan_radial {y : ℂ} (hy : y ≠ 0) (c t : ℝ) :
    artinMatrixJacquet c (artinDiagonalMatrix y * artinCartanMatrix t) =
      artinComplexJacquetRadialProfile c (‖y‖ ^ 2 * Real.exp (4 * t)) := by
  rw [artinMatrixJacquet_cartan, artinMatrixJacquet_diagonal_radial
    (mul_ne_zero hy (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)))]
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
    ← Real.exp_nat_mul]
  congr 2
  norm_num
  ring

theorem artinComplexJacquetRadialProfile_log_smooth {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞ (fun v => artinComplexJacquetRadialProfile c (Real.exp (-v))) := by
  have h := (artinSphericalBesselProfile_log_smooth_bounded hc
    (σ := 0) (by norm_num)).1
  have he0 : artinMellinLogPullback (artinSphericalBesselProfile c) (0 : ℂ) =
      fun v => artinSphericalBesselProfile c (Real.exp (-v)) := by
    funext v
    simp [artinMellinLogPullback]
  rw [Complex.ofReal_zero, he0] at h
  have he : (fun v => artinComplexJacquetRadialProfile c (Real.exp (-v))) =
      fun v => ((2 * Real.pi / Real.Gamma (4 / 3) *
        (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
          artinSphericalBesselProfile c (Real.exp (-v)) := by
    funext v
    exact artinComplexJacquetRadialProfile_eq_spherical hc (Real.exp_pos _)
  rw [he]
  exact contDiff_const.mul h

theorem artinMatrixJacquet_cartan_log_curve {y : ℂ} (hy : y ≠ 0) (c t : ℝ) :
    artinMatrixJacquet c (artinDiagonalMatrix y * artinCartanMatrix t) =
      artinComplexJacquetRadialProfile c
        (Real.exp (-(-Real.log (‖y‖ ^ 2) - 4 * t))) := by
  rw [artinMatrixJacquet_cartan_radial hy]
  congr 1
  rw [show -(-Real.log (‖y‖ ^ 2) - 4 * t) = Real.log (‖y‖ ^ 2) + 4 * t by ring,
    Real.exp_add, Real.exp_log (sq_pos_of_pos (norm_pos_iff.mpr hy))]

/-- All derivatives of a radial exponential curve, obtained by affine log coordinates. -/
theorem artinProfile_radial_exp_iteratedDeriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ (fun v => f (Real.exp (-v)))) {u : ℝ} (hu : 0 < u)
    (a : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s => f (u * Real.exp (a * s))) t =
      (-a) ^ j • artinLogProfileJet f j (u * Real.exp (a * t)) := by
  let F : ℝ → ℂ := fun v => f (Real.exp (-v))
  have he : (fun s => f (u * Real.exp (a * s))) =
      fun s => F ((-a) * s - Real.log u) := by
    funext s
    dsimp only [F]
    rw [show -((-a) * s - Real.log u) = Real.log u + a * s by ring,
      Real.exp_add, Real.exp_log hu]
  have hshift : ContDiff ℝ j (fun v => F (v - Real.log u)) :=
    (hf.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [he, iteratedDeriv_comp_const_smul hshift (-a),
    iteratedDeriv_comp_sub_const j F (Real.log u)]
  unfold artinLogProfileJet
  rw [Real.log_mul hu.ne' (Real.exp_ne_zero _), Real.log_exp]
  dsimp only [F]
  congr 2
  ring

theorem artinMatrixJacquet_cartan_contDiff {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) :
    ContDiff ℝ ∞ (fun t => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinCartanMatrix t)) := by
  have he : (fun t => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinCartanMatrix t)) =
      fun t => artinComplexJacquetRadialProfile c
        (Real.exp (-(-Real.log (‖y‖ ^ 2) - 4 * t))) := by
    funext t
    exact artinMatrixJacquet_cartan_log_curve hy c t
  rw [he]
  exact (artinComplexJacquetRadialProfile_log_smooth hc).comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem artinMatrixJacquet_cartan_iteratedDeriv {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinCartanMatrix s)) t =
      (-4 : ℝ) ^ j • artinLogProfileJet (artinComplexJacquetRadialProfile c) j
        (‖y‖ ^ 2 * Real.exp (4 * t)) := by
  have he : (fun s => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinCartanMatrix s)) =
      fun s => artinComplexJacquetRadialProfile c (‖y‖ ^ 2 * Real.exp (4 * s)) := by
    funext s
    exact artinMatrixJacquet_cartan_radial hy c s
  rw [he]
  exact artinProfile_radial_exp_iteratedDeriv
    (artinComplexJacquetRadialProfile_log_smooth hc)
    (sq_pos_of_pos (norm_pos_iff.mpr hy)) 4 j t

theorem artinMatrixJacquet_cartan_hasDerivAt {c : ℝ} (hc : 0 < c)
    {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun t => artinMatrixJacquet c
      (artinDiagonalMatrix y * artinCartanMatrix t))
      ((-4 : ℝ) • artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 (‖y‖ ^ 2))
      0 := by
  have h := (artinMatrixJacquet_cartan_contDiff hc hy).differentiable
    (by simp) |>.differentiableAt (x := (0 : ℝ)) |>.hasDerivAt
  have hd := artinMatrixJacquet_cartan_iteratedDeriv hc hy 1 0
  simp only [iteratedDeriv_one, pow_one, mul_zero, Real.exp_zero, mul_one] at hd
  rwa [hd] at h

def artinMatrixCartanDerivative (c : ℝ) (y : ℂ) : ℂ :=
  deriv (fun t => artinMatrixJacquet c (artinDiagonalMatrix y * artinCartanMatrix t)) 0

theorem artinMatrixCartanDerivative_eq {c : ℝ} (hc : 0 < c) {y : ℂ} (hy : y ≠ 0) :
    artinMatrixCartanDerivative c y =
      (-4 : ℂ) * artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 (‖y‖ ^ 2) := by
  simpa only [artinMatrixCartanDerivative, real_smul, Complex.ofReal_neg,
    Complex.ofReal_ofNat] using (artinMatrixJacquet_cartan_hasDerivAt hc hy).deriv

/-- The Cartan image is defined by differentiating the actual matrix integral. -/
def artinMatrixCartanRadialProfile (c : ℝ) (phase : Circle) (u : ℝ) : ℂ :=
  artinMatrixCartanDerivative c ((Real.sqrt u : ℂ) * (phase : ℂ))

theorem artinMatrixCartanRadialProfile_eq {c u : ℝ} (hc : 0 < c) (hu : 0 < u)
    (phase : Circle) :
    artinMatrixCartanRadialProfile c phase u =
      (-4 : ℂ) * artinLogProfileJet (artinComplexJacquetRadialProfile c) 1 u := by
  have hy : (Real.sqrt u : ℂ) * (phase : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne') phase.coe_ne_zero
  rw [artinMatrixCartanRadialProfile, artinMatrixCartanDerivative_eq hc hy,
    norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hu.le]

theorem artinMatrixCartanRadialProfile_phase_invariant {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (phase phase' : Circle) :
    artinMatrixCartanRadialProfile c phase u = artinMatrixCartanRadialProfile c phase' u := by
  rw [artinMatrixCartanRadialProfile_eq hc hu, artinMatrixCartanRadialProfile_eq hc hu]

theorem artinMatrixCartanRadialProfile_logJet {c : ℝ} (hc : 0 < c)
    (phase : Circle) (j : ℕ) (u : ℝ) :
    artinLogProfileJet (artinMatrixCartanRadialProfile c phase) j u =
      (-4 : ℂ) * artinLogProfileJet (artinComplexJacquetRadialProfile c) (j + 1) u := by
  let F : ℝ → ℂ := fun v => artinComplexJacquetRadialProfile c (Real.exp (-v))
  have he : (fun v => artinMatrixCartanRadialProfile c phase (Real.exp (-v))) =
      fun v => (-4 : ℂ) * deriv F v := by
    funext v
    rw [artinMatrixCartanRadialProfile_eq hc (Real.exp_pos _), artinLogProfileJet,
      Real.log_exp, neg_neg, iteratedDeriv_one]
  rw [artinLogProfileJet, he, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']
  rfl

theorem artinMatrixCartanRadialProfile_uniform_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 1 / 3) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixCartanRadialProfile c phase) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinComplexJacquetRadialProfile_logJet_two_ended hc hα hA (j + 1)
  refine ⟨4 * M, mul_pos (by norm_num) hM, fun phase u hu => ?_⟩
  rw [artinMatrixCartanRadialProfile_logJet hc, norm_mul]
  have hn : ‖(-4 : ℂ)‖ = 4 := by norm_num
  rw [hn]
  exact (mul_le_mul_of_nonneg_left (hb u hu) (by norm_num)).trans_eq
    (mul_assoc _ _ _).symm

theorem artinMatrixCartanRadialProfile_bessel_logJet {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (phase : Circle) :
    artinMatrixCartanRadialProfile c phase u =
      (-4 : ℂ) * ((2 * Real.pi / Real.Gamma (4 / 3) *
        (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
          artinLogProfileJet (artinSphericalBesselProfile c) 1 u := by
  rw [artinMatrixCartanRadialProfile_eq hc hu, artinComplexJacquetRadialProfile_logJet hc]
  ring

theorem artinMatrixCartanRadialProfile_contDiffOn {c : ℝ} (hc : 0 < c)
    (phase : Circle) :
    ContDiffOn ℝ ∞ (artinMatrixCartanRadialProfile c phase) (Ioi 0) := by
  have he : (fun v => artinMatrixCartanRadialProfile c phase (Real.exp (-v))) =
      fun v => (-4 : ℂ) * deriv
        (fun w => artinComplexJacquetRadialProfile c (Real.exp (-w))) v := by
    funext v
    rw [artinMatrixCartanRadialProfile_eq hc (Real.exp_pos _), artinLogProfileJet,
      Real.log_exp, neg_neg, iteratedDeriv_one]
  apply artinProfile_contDiffOn_of_log (σ := 0)
  have h : ContDiff ℝ ∞ (fun v => artinMatrixCartanRadialProfile c phase (Real.exp (-v))) := by
    rw [he]
    exact contDiff_const.mul
      (contDiff_infty_iff_deriv.mp (artinComplexJacquetRadialProfile_log_smooth hc)).2
  have he0 : artinMellinLogPullback (artinMatrixCartanRadialProfile c phase) (0 : ℂ) =
      fun v => artinMatrixCartanRadialProfile c phase (Real.exp (-v)) := by
    funext v
    simp [artinMellinLogPullback]
  simpa only [Complex.ofReal_zero, he0] using h

theorem artinMatrixJacquet_cartan_uniform_two_ended {c α A : ℝ}
    (hc : 0 < c) (hα : α < 1 / 3) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (y : ℂ) (t : ℝ), y ≠ 0 →
      ‖iteratedDeriv j (fun s => artinMatrixJacquet c
        (artinDiagonalMatrix y * artinCartanMatrix s)) t‖ ≤
        M * min ((‖y‖ ^ 2 * Real.exp (4 * t)) ^ α)
          ((‖y‖ ^ 2 * Real.exp (4 * t)) ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinComplexJacquetRadialProfile_logJet_two_ended hc hα hA j
  refine ⟨4 ^ j * M, mul_pos (pow_pos (by norm_num) j) hM, fun y t hy => ?_⟩
  rw [artinMatrixJacquet_cartan_iteratedDeriv hc hy, norm_smul, norm_pow]
  have hn : ‖(-4 : ℝ)‖ = 4 := by norm_num
  rw [hn]
  exact (mul_le_mul_of_nonneg_left
    (hb _ (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)) (Real.exp_pos _)))
    (by positivity)).trans_eq (mul_assoc _ _ _).symm

end
end SimultaneousPrimitiveRoots

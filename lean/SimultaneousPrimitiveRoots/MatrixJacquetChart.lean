module

public import SimultaneousPrimitiveRoots.EndpointJacquetBounds
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate Matrix.Norms.Elementwise
noncomputable section

def artinMatrixRowMass (g : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

def artinMatrixJacquetShift (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (g 0 0 * conj (g 1 0) + g 0 1 * conj (g 1 1)) / (artinMatrixRowMass g : ℂ)

def artinMatrixJacquetDiagonal (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  g.det / (artinMatrixRowMass g : ℂ)

def artinMatrixJacquetCompact (g : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  artinCompactRotation (g 1 1 / (Real.sqrt (artinMatrixRowMass g) : ℂ))
    (conj (g 1 0) / (Real.sqrt (artinMatrixRowMass g) : ℂ))

theorem artinMatrixRowMass_nonneg (g : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ artinMatrixRowMass g := by
  unfold artinMatrixRowMass
  positivity

theorem artinMatrixRowMass_pos {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    0 < artinMatrixRowMass g := by
  by_contra h
  have h0 : artinMatrixRowMass g = 0 := le_antisymm (le_of_not_gt h)
    (artinMatrixRowMass_nonneg g)
  have hc : g 1 0 = 0 := norm_eq_zero.mp (by
    unfold artinMatrixRowMass at h0
    nlinarith [sq_nonneg ‖g 1 1‖, norm_nonneg (g 1 0)])
  have hd : g 1 1 = 0 := norm_eq_zero.mp (by
    unfold artinMatrixRowMass at h0
    nlinarith [sq_nonneg ‖g 1 0‖, norm_nonneg (g 1 1)])
  exact hg (by simp [Matrix.det_fin_two, hc, hd])

theorem artinMatrixJacquetCompact_normalized {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : 0 < artinMatrixRowMass g) :
    ‖g 1 1 / (Real.sqrt (artinMatrixRowMass g) : ℂ)‖ ^ 2 +
      ‖conj (g 1 0) / (Real.sqrt (artinMatrixRowMass g) : ℂ)‖ ^ 2 = 1 := by
  rw [norm_div, norm_div, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow, div_pow,
    ← add_div, Real.sq_sqrt hg.le]
  simpa [artinMatrixRowMass, add_comm] using div_self hg.ne'

/-- A direct two-by-two decomposition; no abstract Iwasawa theory is assumed. -/
theorem artinMatrixJacquet_chart_matrix {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : 0 < artinMatrixRowMass g) :
    g * artinMatrixJacquetCompact g =
      ((artinMatrixRowMass g : ℂ) / (Real.sqrt (artinMatrixRowMass g) : ℂ)) •
        (artinUpperRootMatrix (artinMatrixJacquetShift g) *
          artinDiagonalMatrix (artinMatrixJacquetDiagonal g)) := by
  have hr : (artinMatrixRowMass g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hs : (Real.sqrt (artinMatrixRowMass g) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hg).ne'
  have hrow : g 1 0 * conj (g 1 0) + g 1 1 * conj (g 1 1) =
      (artinMatrixRowMass g : ℂ) := by
    rw [Complex.mul_conj', Complex.mul_conj']
    simp [artinMatrixRowMass]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinMatrixJacquetCompact, artinCompactRotation, artinMatrixJacquetShift,
      artinMatrixJacquetDiagonal, artinUpperRootMatrix, artinDiagonalMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Complex.conj_ofReal,
      Matrix.smul_apply, smul_eq_mul] <;> field_simp
  · ring
  · ring
  · exact hrow

theorem artinMatrixJacquetIntegrand_left_upper (c : ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (z x : ℂ) :
    artinMatrixJacquetIntegrand c (artinUpperRootMatrix z * g) x =
      Complex.exp (Complex.I * c * z.re) * artinMatrixJacquetIntegrand c g (x + z) := by
  have hm : artinWeylMatrix * artinUpperRootMatrix x * (artinUpperRootMatrix z * g) =
      artinWeylMatrix * artinUpperRootMatrix (x + z) * g := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc artinWeylMatrix,
      artinUpperRootMatrix_mul]
  unfold artinMatrixJacquetIntegrand
  rw [hm]
  have he : Complex.I * c * z.re + -Complex.I * c * (x + z).re =
      -Complex.I * c * x.re := by
    simp only [Complex.add_re]
    push_cast
    ring
  calc
    _ = (artinMatrixSphericalSection
        (artinWeylMatrix * artinUpperRootMatrix (x + z) * g) : ℂ) *
          (Complex.exp (Complex.I * c * z.re) *
            Complex.exp (-Complex.I * c * (x + z).re)) := by
      rw [← Complex.exp_add, he]
    _ = _ := by ring

theorem artinMatrixJacquet_left_upper (c : ℝ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    artinMatrixJacquet c (artinUpperRootMatrix z * g) =
      Complex.exp (Complex.I * c * z.re) * artinMatrixJacquet c g := by
  unfold artinMatrixJacquet
  simp_rw [artinMatrixJacquetIntegrand_left_upper]
  rw [integral_const_mul, integral_add_right_eq_self]

theorem artinMatrixJacquetDiagonal_ne_zero {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det ≠ 0) : artinMatrixJacquetDiagonal g ≠ 0 :=
  div_ne_zero hg (Complex.ofReal_ne_zero.mpr (artinMatrixRowMass_pos hg).ne')

/-- The actual integral at every invertible matrix, reduced to the already
computed spherical integral and an explicit additive phase. -/
theorem artinMatrixJacquet_chart {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det ≠ 0) (c : ℝ) :
    artinMatrixJacquet c g = Complex.exp (Complex.I * c * (artinMatrixJacquetShift g).re) *
      artinComplexJacquetRadialProfile c (‖artinMatrixJacquetDiagonal g‖ ^ 2) := by
  have hr := artinMatrixRowMass_pos hg
  have hs : ((artinMatrixRowMass g : ℂ) / (Real.sqrt (artinMatrixRowMass g) : ℂ)) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne')
  calc
    _ = artinMatrixJacquet c (g * artinMatrixJacquetCompact g) :=
      (artinMatrixJacquet_compact c g (artinMatrixJacquetCompact_normalized hr)).symm
    _ = artinMatrixJacquet c (artinUpperRootMatrix (artinMatrixJacquetShift g) *
        artinDiagonalMatrix (artinMatrixJacquetDiagonal g)) := by
      rw [artinMatrixJacquet_chart_matrix hr, artinMatrixJacquet_scalar c _ hs]
    _ = _ := by
      rw [artinMatrixJacquet_left_upper,
        artinMatrixJacquet_diagonal_radial (artinMatrixJacquetDiagonal_ne_zero hg)]

theorem artinMatrixJacquetIntegrand_left_upper_integrable (c : ℝ)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : Integrable (artinMatrixJacquetIntegrand c g))
    (z : ℂ) : Integrable (artinMatrixJacquetIntegrand c (artinUpperRootMatrix z * g)) := by
  apply ((hg.comp_add_right z).const_mul (Complex.exp (Complex.I * c * z.re))).congr
  exact Filter.Eventually.of_forall fun x =>
    (artinMatrixJacquetIntegrand_left_upper c g z x).symm

/-- Absolute convergence at every invertible matrix follows from the actual
diagonal integral and the same explicit chart. -/
theorem artinMatrixJacquetIntegrand_integrable {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det ≠ 0) (c : ℝ) : Integrable (artinMatrixJacquetIntegrand c g) := by
  have hr := artinMatrixRowMass_pos hg
  have hs : ((artinMatrixRowMass g : ℂ) / (Real.sqrt (artinMatrixRowMass g) : ℂ)) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne')
  have hb := artinMatrixJacquetIntegrand_left_upper_integrable c
    (artinMatrixJacquetIntegrand_diagonal_integrable (artinMatrixJacquetDiagonal_ne_zero hg) c)
    (artinMatrixJacquetShift g)
  apply hb.congr
  exact Filter.Eventually.of_forall fun x => by
    calc
      _ = artinMatrixJacquetIntegrand c (g * artinMatrixJacquetCompact g) x := by
        rw [artinMatrixJacquet_chart_matrix hr, artinMatrixJacquetIntegrand_scalar c _ hs]
      _ = _ := artinMatrixJacquetIntegrand_compact c g
        (artinMatrixJacquetCompact_normalized hr) x

theorem artinComplexJacquetRadialProfile_contDiffOn {c : ℝ} (hc : 0 < c) :
    ContDiffOn ℝ ∞ (artinComplexJacquetRadialProfile c) (Ioi 0) := by
  apply artinProfile_contDiffOn_of_log (σ := 0)
  have he : artinMellinLogPullback (artinComplexJacquetRadialProfile c) (0 : ℂ) =
      fun v => artinComplexJacquetRadialProfile c (Real.exp (-v)) := by
    funext v
    simp [artinMellinLogPullback]
  rw [Complex.ofReal_zero, he]
  exact artinComplexJacquetRadialProfile_log_smooth hc

theorem artinComplexNormSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

theorem artinMatrixRowMass_contDiff : ContDiff ℝ ∞ artinMatrixRowMass := by
  exact (artinComplexNormSq_contDiff.comp (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (0 : Fin 2))).add
    (artinComplexNormSq_contDiff.comp (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (1 : Fin 2)))

theorem artinMatrixDet_contDiff :
    ContDiff ℝ ∞ (fun g : Matrix (Fin 2) (Fin 2) ℂ => g.det) := by
  simp only [Matrix.det_fin_two]
  exact ((contDiff_apply_apply ℝ ℂ (0 : Fin 2) (0 : Fin 2)).mul (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (1 : Fin 2))).sub
    ((contDiff_apply_apply ℝ ℂ (0 : Fin 2) (1 : Fin 2)).mul (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (0 : Fin 2)))

theorem artinMatrixJacquetShift_contDiffAt {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det ≠ 0) : ContDiffAt ℝ ∞ artinMatrixJacquetShift g := by
  have hc : ContDiff ℝ ∞ (fun z : ℂ => conj z) := Complex.conjCLE.contDiff
  have hn := (((contDiff_apply_apply ℝ ℂ (0 : Fin 2) (0 : Fin 2)).mul
      (hc.comp (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (0 : Fin 2)))).add
    ((contDiff_apply_apply ℝ ℂ (0 : Fin 2) (1 : Fin 2)).mul
      (hc.comp (contDiff_apply_apply ℝ ℂ (1 : Fin 2) (1 : Fin 2)))))
  change ContDiffAt ℝ ∞ (fun G =>
    (G 0 0 * conj (G 1 0) + G 0 1 * conj (G 1 1)) / (artinMatrixRowMass G : ℂ)) g
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv]
  exact hn.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp g
    (artinMatrixRowMass_contDiff.contDiffAt.inv (artinMatrixRowMass_pos hg).ne'))

theorem artinMatrixJacquetDiagonal_contDiffAt {g : Matrix (Fin 2) (Fin 2) ℂ}
    (hg : g.det ≠ 0) : ContDiffAt ℝ ∞ artinMatrixJacquetDiagonal g := by
  change ContDiffAt ℝ ∞ (fun G => G.det / (artinMatrixRowMass G : ℂ)) g
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv]
  exact artinMatrixDet_contDiff.contDiffAt.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp g
      (artinMatrixRowMass_contDiff.contDiffAt.inv (artinMatrixRowMass_pos hg).ne'))

/-- Smoothness is proved for the actual matrix integral, by its explicit
coordinate formula, without interchanging differentiation and integration. -/
theorem artinMatrixJacquet_contDiffAt {c : ℝ} (hc : 0 < c)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) :
    ContDiffAt ℝ ∞ (artinMatrixJacquet c) g := by
  have hu : 0 < ‖artinMatrixJacquetDiagonal g‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (artinMatrixJacquetDiagonal_ne_zero hg))
  have hs := artinMatrixJacquetShift_contDiffAt hg
  have hd := artinMatrixJacquetDiagonal_contDiffAt hg
  have hp : ContDiffAt ℝ ∞ (artinComplexJacquetRadialProfile c)
      (‖artinMatrixJacquetDiagonal g‖ ^ 2) :=
    (artinComplexJacquetRadialProfile_contDiffOn hc).contDiffAt
    (isOpen_Ioi.mem_nhds hu)
  have hphase : ContDiffAt ℝ ∞ (fun G : Matrix (Fin 2) (Fin 2) ℂ =>
      Complex.exp (Complex.I * c * (artinMatrixJacquetShift G).re)) g :=
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp g
      (Complex.reCLM.contDiff.contDiffAt.comp g hs))).cexp
  have hradius : ContDiffAt ℝ ∞ (fun G : Matrix (Fin 2) (Fin 2) ℂ =>
      artinComplexJacquetRadialProfile c (‖artinMatrixJacquetDiagonal G‖ ^ 2)) g := by
    have hnorm : ContDiffAt ℝ ∞ (fun G : Matrix (Fin 2) (Fin 2) ℂ =>
        ‖artinMatrixJacquetDiagonal G‖ ^ 2) g :=
      ContDiffAt.fun_comp (f := artinMatrixJacquetDiagonal)
        (g := fun z : ℂ => ‖z‖ ^ 2) g artinComplexNormSq_contDiff.contDiffAt hd
    exact ContDiffAt.fun_comp (f := fun G : Matrix (Fin 2) (Fin 2) ℂ =>
      ‖artinMatrixJacquetDiagonal G‖ ^ 2) (g := artinComplexJacquetRadialProfile c) g hp hnorm
  have hformula : ContDiffAt ℝ ∞ (fun G : Matrix (Fin 2) (Fin 2) ℂ =>
      Complex.exp (Complex.I * c * (artinMatrixJacquetShift G).re) *
        artinComplexJacquetRadialProfile c (‖artinMatrixJacquetDiagonal G‖ ^ 2)) g :=
    hphase.mul hradius
  apply hformula.congr_of_eventuallyEq
  filter_upwards [artinMatrixDet_contDiff.continuous.continuousAt.eventually_ne hg] with G hG
  exact artinMatrixJacquet_chart hG c

end
end SimultaneousPrimitiveRoots

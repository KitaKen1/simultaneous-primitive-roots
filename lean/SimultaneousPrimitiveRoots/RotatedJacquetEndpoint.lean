module

public import SimultaneousPrimitiveRoots.MatrixJacquetCompactDifferential

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex Matrix
open scoped Topology ContDiff ComplexConjugate Matrix.Norms.Elementwise BigOperators
noncomputable section

/-- Direct transport of the actual unweighted log jets; no boundary Mellin
integrability is required. -/
theorem artinFiniteProfileCombination_logJet {I P : Type*} (s : Finset I)
    (a : P → I → ℂ) {f : I → ℝ → ℂ}
    (hf : ∀ i, ContDiff ℝ ∞ (fun v => f i (Real.exp (-v))))
    (p : P) (j : ℕ) (u : ℝ) :
    artinLogProfileJet (artinFiniteProfileCombination s a f p) j u =
      ∑ i ∈ s, a p i * artinLogProfileJet (f i) j u := by
  have hd : ∀ i ∈ s, ContDiffAt ℝ j
      (fun v => a p i * f i (Real.exp (-v))) (-Real.log u) :=
    fun i _ => ((contDiff_const.mul (hf i)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt
  unfold artinLogProfileJet
  change iteratedDeriv j (fun v => ∑ i ∈ s, a p i * f i (Real.exp (-v))) _ = _
  rw [iteratedDeriv_fun_sum hd]
  simp only [iteratedDeriv_const_mul_field]

theorem artinFiniteProfileCombination_uniform_jet_bound {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) {f : I → ℝ → ℂ} {C : ℝ}
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C)
    (hf : ∀ i, ContDiff ℝ ∞ (fun v => f i (Real.exp (-v))))
    (w : ℝ → ℝ) (hw : ∀ u, 0 < u → 0 ≤ w u) (j : ℕ)
    (hb : ∀ i, ∃ M, 0 < M ∧ ∀ u, 0 < u → ‖artinLogProfileJet (f i) j u‖ ≤ M * w u) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet (artinFiniteProfileCombination s a f p) j u‖ ≤ M * w u := by
  choose M _hM hbM using hb
  refine ⟨max 1 (C * ∑ i ∈ s, M i), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun p u hu => ?_⟩
  rw [artinFiniteProfileCombination_logJet s a hf]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ s, C * (M i * w u) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (ha p i hi) (hbM i u hu) (norm_nonneg _) hC.le
    _ = (C * ∑ i ∈ s, M i) * w u := by
      simp only [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (hw u hu)

/-- Two fixed actual images; all rotation and phase dependence is in their
coefficients, independent of the positive radial variable. -/
def artinMatrixJacquetReducedBasis (c : ℝ) (i : Fin 2) : ℝ → ℂ :=
  if i = 0 then artinMatrixCartanRadialProfile c 1
  else artinMatrixRootRadialProfile c false 1

theorem artinMatrixRootRadialProfile_real_axis {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    artinMatrixRootRadialProfile c false 1 u =
      (Real.sqrt u : ℂ) * artinComplexJacquetRadialProfile c u := by
  have hy : (Real.sqrt u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'
  have hn : ‖(Real.sqrt u : ℂ)‖ ^ 2 = u := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hu.le]
  simp only [artinMatrixRootRadialProfile, Bool.false_eq_true, ↓reduceIte,
    Circle.coe_one, mul_one]
  rw [artinMatrixRootWhittakerPlus_eq hc.ne', artinMatrixJacquet_diagonal_radial hy, hn]

theorem artinMatrixJacquetReducedBasis_log_smooth {c : ℝ} (hc : 0 < c) (i : Fin 2) :
    ContDiff ℝ ∞ (fun v => artinMatrixJacquetReducedBasis c i (Real.exp (-v))) := by
  fin_cases i
  · simp only [artinMatrixJacquetReducedBasis, ↓reduceIte]
    exact (artinMatrixCartanRadialProfile_contDiffOn hc 1).comp_contDiff
      (Real.contDiff_exp.comp contDiff_id.neg) (fun v => Real.exp_pos _)
  · simp only [artinMatrixJacquetReducedBasis, Fin.isValue, ↓reduceIte]
    have he : (fun v : ℝ => artinMatrixRootRadialProfile c false 1 (Real.exp (-v))) =
        fun v => (((2 * Real.pi / Real.Gamma (4 / 3) *
          (c / 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) * artinMatrixRootPhase false 1) *
          artinBesselLocalProfile c (Real.exp (-v)) := by
      funext v
      exact artinMatrixRootRadialProfile_eq_bessel hc (Real.exp_pos _) false 1
    rw [he]
    have hf := (artinBesselLocalProfile_log_smooth_bounded hc (σ := 0) (by norm_num)).1
    have he0 : artinMellinLogPullback (artinBesselLocalProfile c) (0 : ℂ) =
        fun v => artinBesselLocalProfile c (Real.exp (-v)) := by
      funext v
      simp [artinMellinLogPullback]
    rw [Complex.ofReal_zero, he0] at hf
    exact contDiff_const.mul hf

theorem artinMatrixJacquetReducedBasis_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i u, 0 < u →
      ‖artinLogProfileJet (artinMatrixJacquetReducedBasis c i) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinMatrixJacquetLocalImageProfile_endpoint_two_ended hc hA j
  refine ⟨M, hM, fun i u hu => ?_⟩
  fin_cases i
  · simpa only [artinMatrixJacquetReducedBasis, artinMatrixJacquetLocalImageProfile,
      Fin.isValue, ↓reduceIte] using hb 1 1 u hu
  · simpa only [artinMatrixJacquetReducedBasis, artinMatrixJacquetLocalImageProfile,
      Fin.isValue, ↓reduceIte] using hb 2 1 u hu

def artinRotatedJacquetRootCoefficient (c : ℝ) (x v z : ℂ)
    (p : artinCompactRotationParameter) (phase : Circle) : ℂ :=
  Complex.I * (c : ℂ) *
    ((((artinRotatedUpper p.val.1 p.val.2 x v z).re +
       (artinRotatedLower p.val.1 p.val.2 x v z).re) * (phase : ℂ).re +
      ((artinRotatedUpper p.val.1 p.val.2 x v z).im -
       (artinRotatedLower p.val.1 p.val.2 x v z).im) * ((phase : ℂ) * Complex.I).re : ℝ) : ℂ)

theorem artinRotatedJacquetRootCoefficient_norm_le {c : ℝ} (hc : 0 < c)
    (x v z : ℂ) (p : artinCompactRotationParameter) (phase : Circle) :
    ‖artinRotatedJacquetRootCoefficient c x v z p phase‖ ≤
      4 * c * (2 * ‖x‖ + ‖v‖ + ‖z‖) := by
  let D := 2 * ‖x‖ + ‖v‖ + ‖z‖
  let e := artinRotatedUpper p.val.1 p.val.2 x v z
  let f := artinRotatedLower p.val.1 p.val.2 x v z
  obtain ⟨ha, hb⟩ := artinCompactRotation_norm_entries p.prop
  have he : ‖e‖ ≤ D := artinRotatedUpper_norm_le ha hb x v z
  have hf : ‖f‖ ≤ D := artinRotatedLower_norm_le ha hb x v z
  have hB : |e.re + f.re| ≤ 2 * D := by
    have h := abs_add_le e.re f.re
    have he' := (Complex.abs_re_le_norm e).trans he
    have hf' := (Complex.abs_re_le_norm f).trans hf
    linarith
  have hF : |e.im - f.im| ≤ 2 * D := by
    have h := abs_sub e.im f.im
    have he' := (Complex.abs_im_le_norm e).trans he
    have hf' := (Complex.abs_im_le_norm f).trans hf
    linarith
  have hp : |(phase : ℂ).re| ≤ 1 := by simpa using Complex.abs_re_le_norm (phase : ℂ)
  have hpi : |((phase : ℂ) * Complex.I).re| ≤ 1 := by
    simpa [norm_mul] using Complex.abs_re_le_norm ((phase : ℂ) * Complex.I)
  have h1 := mul_le_mul_of_nonneg_left hp (abs_nonneg (e.re + f.re))
  have h2 := mul_le_mul_of_nonneg_left hpi (abs_nonneg (e.im - f.im))
  have hs : |(e.re + f.re) * (phase : ℂ).re +
      (e.im - f.im) * ((phase : ℂ) * Complex.I).re| ≤ 4 * D := by
    have h := abs_add_le ((e.re + f.re) * (phase : ℂ).re)
      ((e.im - f.im) * ((phase : ℂ) * Complex.I).re)
    simp only [abs_mul, mul_one] at h h1 h2
    linarith
  unfold artinRotatedJacquetRootCoefficient
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left hs hc.le).trans_eq (by dsimp [D]; ring)

def artinRotatedJacquetCoefficients (c : ℝ) (x v z : ℂ)
    (q : artinCompactRotationParameter × Circle) (i : Fin 2) : ℂ :=
  if i = 0 then ((artinRotatedDiagonal q.1.val.1 q.1.val.2 x v z).re : ℂ)
  else artinRotatedJacquetRootCoefficient c x v z q.1 q.2

theorem artinRotatedJacquetCoefficients_norm_le {c : ℝ} (hc : 0 < c)
    (x v z : ℂ) (q : artinCompactRotationParameter × Circle) (i : Fin 2) :
    ‖artinRotatedJacquetCoefficients c x v z q i‖ ≤
      max 1 (max (2 * ‖x‖ + ‖v‖ + ‖z‖) (4 * c * (2 * ‖x‖ + ‖v‖ + ‖z‖))) := by
  fin_cases i
  · simp only [artinRotatedJacquetCoefficients, ↓reduceIte, Complex.norm_real,
      Real.norm_eq_abs]
    obtain ⟨ha, hb⟩ := artinCompactRotation_norm_entries q.1.prop
    exact ((Complex.abs_re_le_norm _).trans
      (artinRotatedDiagonal_norm_le ha hb x v z)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · simp only [artinRotatedJacquetCoefficients, Fin.isValue, ↓reduceIte]
    exact (artinRotatedJacquetRootCoefficient_norm_le hc x v z q.1 q.2).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-- The profile is defined from the actual Frechet differential of the integral. -/
def artinMatrixRotatedJacquetProfile (c : ℝ) (x v z : ℂ)
    (p : artinCompactRotationParameter) (phase : Circle) (u : ℝ) : ℂ :=
  artinMatrixJacquetDifferential c
    (artinDiagonalMatrix ((Real.sqrt u : ℂ) * (phase : ℂ)) *
      artinCompactRotation p.val.1 p.val.2) (artinTracelessMatrix x v z)

theorem artinMatrixRotatedJacquetProfile_eq_combination {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (x v z : ℂ)
    (p : artinCompactRotationParameter) (phase : Circle) :
    artinMatrixRotatedJacquetProfile c x v z p phase u =
      artinFiniteProfileCombination Finset.univ (artinRotatedJacquetCoefficients c x v z)
        (artinMatrixJacquetReducedBasis c) (p, phase) u := by
  have hy : (Real.sqrt u : ℂ) * (phase : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne') phase.coe_ne_zero
  have hn : ‖(Real.sqrt u : ℂ) * (phase : ℂ)‖ ^ 2 = u := by
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hu.le]
  rw [artinMatrixRotatedJacquetProfile, artinMatrixJacquetDifferential_rotated_formula hc hy p.prop,
    artinMatrixJacquet_diagonal_radial hy, hn]
  simp only [artinFiniteProfileCombination, Fin.sum_univ_two,
    artinRotatedJacquetCoefficients, artinMatrixJacquetReducedBasis, Fin.isValue, ↓reduceIte]
  rw [artinMatrixCartanRadialProfile_eq hc hu,
    artinMatrixRootRadialProfile_real_axis hc hu]
  simp only [artinRotatedJacquetRootCoefficient, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub]
  ring

theorem artinMatrixRotatedJacquetProfile_logJet {c : ℝ} (hc : 0 < c)
    (x v z : ℂ) (p : artinCompactRotationParameter) (phase : Circle) (j : ℕ) (u : ℝ) :
    artinLogProfileJet (artinMatrixRotatedJacquetProfile c x v z p phase) j u =
      ∑ i : Fin 2, artinRotatedJacquetCoefficients c x v z (p, phase) i *
        artinLogProfileJet (artinMatrixJacquetReducedBasis c i) j u := by
  have he : (fun w : ℝ => artinMatrixRotatedJacquetProfile c x v z p phase (Real.exp (-w))) =
      fun w => artinFiniteProfileCombination Finset.univ (artinRotatedJacquetCoefficients c x v z)
        (artinMatrixJacquetReducedBasis c) (p, phase) (Real.exp (-w)) := by
    funext w
    exact artinMatrixRotatedJacquetProfile_eq_combination hc (Real.exp_pos _) x v z p phase
  change iteratedDeriv j _ (-Real.log u) = _
  rw [he]
  exact artinFiniteProfileCombination_logJet Finset.univ _
    (artinMatrixJacquetReducedBasis_log_smooth hc) (p, phase) j u

theorem artinMatrixRotatedJacquetProfile_log_smooth {c : ℝ} (hc : 0 < c)
    (x v z : ℂ) (p : artinCompactRotationParameter) (phase : Circle) :
    ContDiff ℝ ∞ (fun w => artinMatrixRotatedJacquetProfile c x v z p phase (Real.exp (-w))) := by
  have he : (fun w : ℝ => artinMatrixRotatedJacquetProfile c x v z p phase (Real.exp (-w))) =
      fun w => ∑ i : Fin 2, artinRotatedJacquetCoefficients c x v z (p, phase) i *
        artinMatrixJacquetReducedBasis c i (Real.exp (-w)) := by
    funext w
    exact artinMatrixRotatedJacquetProfile_eq_combination hc (Real.exp_pos _) x v z p phase
  rw [he]
  exact ContDiff.sum (fun i _ => contDiff_const.mul (artinMatrixJacquetReducedBasis_log_smooth hc i))

theorem artinMatrixRotatedJacquetProfile_contDiffOn {c : ℝ} (hc : 0 < c)
    (x v z : ℂ) (p : artinCompactRotationParameter) (phase : Circle) :
    ContDiffOn ℝ ∞ (artinMatrixRotatedJacquetProfile c x v z p phase) (Ioi 0) := by
  apply artinProfile_contDiffOn_of_log (σ := 0)
  have he : artinMellinLogPullback (artinMatrixRotatedJacquetProfile c x v z p phase) (0 : ℂ) =
      fun w => artinMatrixRotatedJacquetProfile c x v z p phase (Real.exp (-w)) := by
    funext w
    simp [artinMellinLogPullback]
  rw [Complex.ofReal_zero, he]
  exact artinMatrixRotatedJacquetProfile_log_smooth hc x v z p phase

/-- One constant is selected before every normalized compact rotation and Circle
phase. The Lie vector and derivative order are fixed; no growing-field uniformity
or original representation identification is asserted. -/
theorem artinMatrixRotatedJacquetProfile_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (x v z : ℂ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixRotatedJacquetProfile c x v z p phase) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  let C := max 1 (max (2 * ‖x‖ + ‖v‖ + ‖z‖) (4 * c * (2 * ‖x‖ + ‖v‖ + ‖z‖)))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨N, hN, hbN⟩ := artinMatrixJacquetReducedBasis_endpoint_two_ended hc hA j
  obtain ⟨M, hM, hbM⟩ := artinFiniteProfileCombination_uniform_jet_bound Finset.univ
    (artinRotatedJacquetCoefficients c x v z) hC
    (fun q i _ => artinRotatedJacquetCoefficients_norm_le hc x v z q i)
    (artinMatrixJacquetReducedBasis_log_smooth hc)
    (fun u => min (u ^ (1 / 3 : ℝ)) (u ^ (-A)))
    (fun u hu => le_min (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hu.le _)) j
    (fun i => ⟨N, hN, hbN i⟩)
  refine ⟨M, hM, fun p phase u hu => ?_⟩
  have he : artinLogProfileJet (artinMatrixRotatedJacquetProfile c x v z p phase) j u =
      artinLogProfileJet (artinFiniteProfileCombination Finset.univ
        (artinRotatedJacquetCoefficients c x v z) (artinMatrixJacquetReducedBasis c)
        (p, phase)) j u := by
    rw [artinMatrixRotatedJacquetProfile_logJet hc,
      artinFiniteProfileCombination_logJet Finset.univ _ (artinMatrixJacquetReducedBasis_log_smooth hc)]
  rw [he]
  exact hbM (p, phase) u hu

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.MatrixJacquetCartan

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution ContDiff
noncomputable section

/-- The zero-exponent Gamma kernel is bounded even though it is not L1. -/
theorem artinGammaLogJet_zero_exponent_bound (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinGammaLogJet 0 j v‖ ≤ M := by
  cases j with
  | zero =>
    refine ⟨1, zero_lt_one, fun v => ?_⟩
    rw [artinGammaLogJet, artinGammaDensity_log_exp]
    simp only [Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos (-v)])
  | succ j =>
    simpa only [artinGammaLogJet, Complex.ofReal_zero, neg_zero,
      zero_mul, zero_add] using artinGammaLogJet_bound (a := 1) (by norm_num) j

theorem artinGammaLogJet_bound_nonneg {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinGammaLogJet a j v‖ ≤ M := by
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h]
    exact artinGammaLogJet_zero_exponent_bound j
  · exact artinGammaLogJet_bound h j

/-- Swap the actual convolution factors in log coordinates, including at a boundary weight. -/
theorem artinGammaPairProfile_log_swap (a b : ℝ) (s : ℂ) :
    artinMellinLogPullback (artinGammaPairProfile a b) s =
      artinMellinLogPullback (artinGammaPairProfile b a) s := by
  funext v
  rw [artinGammaPairProfile, artinGammaPairProfile,
    artinMellinLogPullback_convolution, artinMellinLogPullback_convolution]
  have hmul : (ContinuousLinearMap.mul ℂ ℂ).flip = ContinuousLinearMap.mul ℂ ℂ := by
    ext
    simp
  rw [← convolution_flip, hmul]

theorem artinGammaPairLogJet_hasDerivAt_nonneg (a b σ : ℝ)
    (ha : 0 ≤ a + σ) (hb : 0 < b + σ) (j : ℕ) (v : ℝ) :
    HasDerivAt (artinGammaPairLogJet a b σ j)
      (artinGammaPairLogJet a b σ (j + 1) v) v := by
  exact artinConvolutionJet_hasDerivAt (artinGammaLogJet_hasDerivAt · _ ·)
    (artinGammaLogJet_bound_nonneg ha)
    ((artinMellin_convergent_iff_logPullback _ _).mp
      (artinGammaDensity_mellin_convergent b (by simpa using
        (show -b < σ by linarith)))) j v

theorem artinGammaPairLogJet_bound_nonneg (a b σ : ℝ)
    (ha : 0 ≤ a + σ) (hb : 0 < b + σ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinGammaPairLogJet a b σ j v‖ ≤ M := by
  exact artinConvolutionJet_bound (artinGammaLogJet_bound_nonneg ha)
    ((artinMellin_convergent_iff_logPullback _ _).mp
      (artinGammaDensity_mellin_convergent b (by simpa using
        (show -b < σ by linarith)))) j

theorem artinGammaPairProfile_log_smooth_bounded_nonneg (a b σ : ℝ)
    (ha : 0 ≤ a + σ) (hb : 0 < b + σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) v‖ ≤ M := by
  rw [← artinGammaPairLogJet_zero]
  have hd := artinGammaPairLogJet_hasDerivAt_nonneg a b σ ha hb
  refine ⟨artinJetChain_contDiff hd, fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv hd]
  exact artinGammaPairLogJet_bound_nonneg a b σ ha hb j

theorem artinGammaPairProfile_log_smooth_bounded_right_nonneg (a b σ : ℝ)
    (ha : 0 < a + σ) (hb : 0 ≤ b + σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinGammaPairProfile a b) (σ : ℂ)) v‖ ≤ M := by
  rw [artinGammaPairProfile_log_swap a b]
  exact artinGammaPairProfile_log_smooth_bounded_nonneg b a σ hb ha

theorem artinBesselLocalProfile_weighted_log_scale {c : ℝ} (hc : 0 < c) (σ v : ℝ) :
    artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ) v =
      (((2 / c ^ 2 : ℝ) : ℂ) * Complex.exp (-(σ : ℂ) * Real.log (c ^ 2 / 4))) *
        artinMellinLogPullback (artinGammaPairProfile (7 / 6) (5 / 6)) (σ : ℂ)
          (v - Real.log (c ^ 2 / 4)) := by
  rw [← artinBesselLogJet_zero hc σ, artinBesselLogJet, artinGammaPairLogJet_zero]

/-- The boundary sigma=-5/6 is allowed for bounded derivatives, not for the Mellin integral. -/
theorem artinBesselLocalProfile_log_smooth_bounded_closed {c σ : ℝ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) ≤ σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinBesselLocalProfile c) (σ : ℂ)) v‖ ≤ M := by
  have hp := artinGammaPairProfile_log_smooth_bounded_right_nonneg
    (7 / 6) (5 / 6) σ (by linarith) (by linarith)
  let D : ℂ := ((2 / c ^ 2 : ℝ) : ℂ) *
    Complex.exp (-(σ : ℂ) * Real.log (c ^ 2 / 4))
  have he := funext (artinBesselLocalProfile_weighted_log_scale hc σ)
  rw [he]
  refine ⟨contDiff_const.mul (hp.1.comp (contDiff_id.sub contDiff_const)), fun j => ?_⟩
  obtain ⟨M, _, hb⟩ := hp.2 j
  refine ⟨max 1 (‖D‖ * M), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun v => ?_⟩
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const]
  calc
    _ ≤ ‖D‖ * M := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg D)
    _ ≤ _ := le_max_right _ _

theorem artinBesselLocalProfile_logJet_endpoint_bound {c : ℝ}
    (hc : 0 < c) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinBesselLocalProfile c) j u‖ ≤ M * u ^ (5 / 6 : ℝ) := by
  have h := artinBesselLocalProfile_log_smooth_bounded_closed hc
    (σ := -(5 / 6)) le_rfl
  simpa only [neg_neg] using artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinSphericalBesselProfile_log_smooth_bounded_closed {c σ : ℝ}
    (hc : 0 < c) (hσ : -(1 / 3 : ℝ) ≤ σ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinSphericalBesselProfile c) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinMellinLogPullback (artinSphericalBesselProfile c) (σ : ℂ)) v‖ ≤ M := by
  rw [artinSphericalBesselProfile_log]
  have h := artinBesselLocalProfile_log_smooth_bounded_closed hc
    (σ := σ - 1 / 2) (by linarith)
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using h

theorem artinSphericalBesselProfile_logJet_endpoint_bound {c : ℝ}
    (hc : 0 < c) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinSphericalBesselProfile c) j u‖ ≤ M * u ^ (1 / 3 : ℝ) := by
  have h := artinSphericalBesselProfile_log_smooth_bounded_closed hc
    (σ := -(1 / 3)) le_rfl
  simpa only [neg_neg] using artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinSphericalBesselProfile_logJet_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinSphericalBesselProfile c) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinSphericalBesselProfile_logJet_endpoint_bound hc j
  obtain ⟨N, _, hbN⟩ := artinSphericalBesselProfile_logJet_power_bound
    hc (σ := A) (by linarith) j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  exact le_min
    ((hbM u hu).trans (mul_le_mul_of_nonneg_right (le_max_left M N)
      (Real.rpow_nonneg hu.le _)))
    ((hbN u hu).trans (mul_le_mul_of_nonneg_right (le_max_right M N)
      (Real.rpow_nonneg hu.le _)))

theorem artinComplexJacquetRadialProfile_logJet_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinComplexJacquetRadialProfile c) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinSphericalBesselProfile_logJet_endpoint_two_ended hc hA j
  let C : ℝ := 2 * Real.pi / Real.Gamma (4 / 3) * (c / 2) ^ (1 / 3 : ℝ)
  have hC : 0 < C := artinComplexJacquet_prefactor_pos hc
  refine ⟨C * M, mul_pos hC hM, fun u hu => ?_⟩
  rw [artinComplexJacquetRadialProfile_logJet hc, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hC.le]
  exact (mul_le_mul_of_nonneg_left (hb u hu) hC.le).trans_eq (mul_assoc _ _ _).symm

/-- The common endpoint constant is chosen before the phase of the actual Cartan image. -/
theorem artinMatrixCartanRadialProfile_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixCartanRadialProfile c phase) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinComplexJacquetRadialProfile_logJet_endpoint_two_ended hc hA (j + 1)
  refine ⟨4 * M, mul_pos (by norm_num) hM, fun phase u hu => ?_⟩
  rw [artinMatrixCartanRadialProfile_logJet hc, norm_mul]
  have hn : ‖(-4 : ℂ)‖ = 4 := by norm_num
  rw [hn]
  exact (mul_le_mul_of_nonneg_left (hb u hu) (by norm_num)).trans_eq
    (mul_assoc _ _ _).symm

theorem artinMatrixJacquet_cartan_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (y : ℂ) (t : ℝ), y ≠ 0 →
      ‖iteratedDeriv j (fun s => artinMatrixJacquet c
        (artinDiagonalMatrix y * artinCartanMatrix s)) t‖ ≤
        M * min ((‖y‖ ^ 2 * Real.exp (4 * t)) ^ (1 / 3 : ℝ))
          ((‖y‖ ^ 2 * Real.exp (4 * t)) ^ (-A)) := by
  obtain ⟨M, hM, hb⟩ := artinComplexJacquetRadialProfile_logJet_endpoint_two_ended hc hA j
  refine ⟨4 ^ j * M, mul_pos (pow_pos (by norm_num) j) hM, fun y t hy => ?_⟩
  rw [artinMatrixJacquet_cartan_iteratedDeriv hc hy, norm_smul, norm_pow]
  have hn : ‖(-4 : ℝ)‖ = 4 := by norm_num
  rw [hn]
  exact (mul_le_mul_of_nonneg_left
    (hb _ (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)) (Real.exp_pos _)))
    (by positivity)).trans_eq (mul_assoc _ _ _).symm

/-- The finite spherical-profile combination now includes the small-side endpoint. -/
theorem artinSphericalBesselBasis_endpoint_two_ended {I P : Type*}
    (s : Finset I) (a : P → I → ℂ) (c : I → ℝ) {A C : ℝ}
    (hc : ∀ i, 0 < c i) (hA : 0 < A)
    (hC : 0 < C) (ha : ∀ p i, i ∈ s → ‖a p i‖ ≤ C) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ p u, 0 < u →
      ‖artinLogProfileJet
        (artinFiniteProfileCombination s a (fun i => artinSphericalBesselProfile (c i)) p) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  exact artinFiniteProfileCombination_uniform_two_ended s a hC ha
    (fun i => (artinSphericalBesselProfile_log_smooth_bounded_closed (hc i)
      (σ := -(1 / 3)) le_rfl).1)
    (fun i => (artinSphericalBesselProfile_log_smooth_bounded_closed (hc i)
      (σ := A) (by linarith)).1)
    (fun i => (artinSphericalBesselProfile_log_smooth_bounded_closed (hc i)
      (σ := -(1 / 3)) le_rfl).2)
    (fun i => (artinSphericalBesselProfile_log_smooth_bounded_closed (hc i)
      (σ := A) (by linarith)).2) j

/-- The actual spherical integral, Cartan image and two normalized root images.
This definition does not identify the original representation's differential. -/
def artinMatrixJacquetLocalImageProfile (c : ℝ) (i : Fin 4) (phase : Circle) : ℝ → ℂ :=
  if i = 0 then artinComplexJacquetRadialProfile c
  else if i = 1 then artinMatrixCartanRadialProfile c phase
  else artinMatrixRootRadialProfile c (i = 3) phase

theorem artinMatrixJacquetLocalImageProfile_endpoint_two_ended {c A : ℝ}
    (hc : 0 < c) (hA : 0 < A) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ i phase u, 0 < u →
      ‖artinLogProfileJet (artinMatrixJacquetLocalImageProfile c i phase) j u‖ ≤
        M * min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) := by
  obtain ⟨S, hS, hbS⟩ := artinComplexJacquetRadialProfile_logJet_endpoint_two_ended hc hA j
  obtain ⟨H, _, hbH⟩ := artinMatrixCartanRadialProfile_endpoint_two_ended hc hA j
  obtain ⟨R, _, hbR⟩ := artinMatrixRootRadialProfile_paper_bound hc hA j
  let M := max S (max H R)
  have hSM : S ≤ M := le_max_left _ _
  have hHM : H ≤ M := (le_max_left H R).trans (le_max_right _ _)
  have hRM : R ≤ M := (le_max_right H R).trans (le_max_right _ _)
  refine ⟨M, lt_of_lt_of_le hS hSM, fun i phase u hu => ?_⟩
  have hmin : 0 ≤ min (u ^ (1 / 3 : ℝ)) (u ^ (-A)) :=
    le_min (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hu.le _)
  fin_cases i <;> simp only [artinMatrixJacquetLocalImageProfile, Fin.isValue]
  · exact (hbS u hu).trans (mul_le_mul_of_nonneg_right hSM hmin)
  · exact (hbH phase u hu).trans (mul_le_mul_of_nonneg_right hHM hmin)
  · exact (hbR false phase u hu).trans (mul_le_mul_of_nonneg_right hRM hmin)
  · exact (hbR true phase u hu).trans (mul_le_mul_of_nonneg_right hRM hmin)

end
end SimultaneousPrimitiveRoots

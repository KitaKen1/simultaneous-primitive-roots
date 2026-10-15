module

public import SimultaneousPrimitiveRoots.Hecke.AveragedTheta

/-!
# The Mellin transform of an averaged theta function

For a `ThetaFamily` over a finite measure space `(P, μ)`, the meromorphic function `Λ` of the
weak FE-pair `ThetaFamily.fePair` is, for `re s > d/2`, the averaged completed Epstein zeta function

`Λ(s) = ∫_P π^{-s} Γ(s) ∑_{m ≠ 0} |A_p m|^{-2s} dμ(p)`.

The interchange of the `t`-integral and the `p`-integral is justified by comparing every lattice of
the family with one scalar lattice `c ℤ^d`, whose Mellin integral converges by the one-lattice
result `thetaFEPair` (E1).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Asymptotics
open scoped Real Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem one_le_latticeTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {t : ℝ} (ht : 0 < t) :
    1 ≤ latticeTheta A t := by
  have h := (summable_theta A ht).le_tsum (0 : d → ℤ) (fun j _ => (Real.exp_pos _).le)
  have h0 : Real.exp (-(π * t) * sqNorm (A (intVec (0 : d → ℤ)))) = 1 := by
    simp [sqNorm_intVec_zero]
  rw [h0] at h
  exact h

theorem latticeTheta_mono {A B : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)}
    (hAB : ∀ m : d → ℤ, sqNorm (B (intVec m)) ≤ sqNorm (A (intVec m))) {t : ℝ} (ht : 0 < t) :
    latticeTheta A t ≤ latticeTheta B t := by
  have hp : 0 < π * t := by positivity
  refine Summable.tsum_le_tsum (fun m => Real.exp_le_exp.mpr ?_) (summable_theta A ht)
    (summable_theta B ht)
  have := mul_le_mul_of_nonneg_left (hAB m) hp.le
  linarith

omit [DecidableEq d] in
theorem sqNorm_smul (c : ℝ) (x : d → ℝ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq d] in
theorem sqNorm_le_card_mul_norm_sq (x : d → ℝ) : sqNorm x ≤ Fintype.card d * ‖x‖ ^ 2 := by
  unfold sqNorm
  calc ∑ i, x i ^ 2 ≤ ∑ _i : d, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        have h := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at h
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = Fintype.card d * ‖x‖ ^ 2 := by simp

/-- A scalar lattice below every lattice with ellipticity constant `κ`. -/
theorem exists_scalar_below [Nonempty d] {κ : ℝ} (hκ : 0 < κ) :
    ∃ B : (d → ℝ) ≃ₗ[ℝ] (d → ℝ), ∀ A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ),
      (∀ v : d → ℝ, κ * ‖v‖ ^ 2 ≤ sqNorm (A v)) →
        ∀ m : d → ℤ, sqNorm (B (intVec m)) ≤ sqNorm (A (intVec m)) := by
  have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  set c : ℝ := Real.sqrt (κ / Fintype.card d) with hc
  have hc0 : c ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ⟨LinearEquiv.smulOfNeZero ℝ (d → ℝ) c hc0, fun A hA m => ?_⟩
  rw [LinearEquiv.smulOfNeZero_apply, sqNorm_smul, hc, Real.sq_sqrt (by positivity)]
  have h1 := sqNorm_le_card_mul_norm_sq (intVec m)
  have h2 := hA (intVec m)
  have h3 : κ / Fintype.card d * sqNorm (intVec m) ≤
      κ / Fintype.card d * (Fintype.card d * ‖intVec m‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : κ / Fintype.card d * (Fintype.card d * ‖intVec m‖ ^ 2) = κ * ‖intVec m‖ ^ 2 := by
    field_simp
  linarith

namespace ThetaFamily

variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
variable (F : ThetaFamily d P) (μ : Measure P)

omit [OpensMeasurableSpace P] in
/-- Joint continuity of `(t, p) ↦ θ_{A_p}(t)` on `t > 0`. -/
theorem continuousOn_theta_uncurry :
    ContinuousOn (fun z : ℝ × P => latticeTheta (F.A z.2) z.1) (Ioi 0 ×ˢ univ) := by
  intro z hz
  have hz0 : 0 < z.1 := hz.1
  have hz' : (0 : ℝ) < z.1 / 2 := by positivity
  have hκ := F.κ_pos
  have hcont : ContinuousOn (fun z : ℝ × P => latticeTheta (F.A z.2) z.1)
      (Ioi (z.1 / 2) ×ˢ univ) := by
    unfold latticeTheta
    refine continuousOn_tsum
      (u := fun m : d → ℤ => Real.exp (-(π * (z.1 / 2) * F.κ) * ‖intVec m‖ ^ 2))
      (fun m => ?_) (summable_exp_neg_norm_sq (by positivity)) (fun m w hw => ?_)
    · have hs : Continuous (sqNorm (d := d)) := by
        unfold sqNorm
        fun_prop
      have h1 : Continuous fun w : ℝ × P => sqNorm (F.A w.2 (intVec m)) :=
        hs.comp ((F.continuous_A (intVec m)).comp continuous_snd)
      exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_fst).neg.mul h1)).continuousOn
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact exp_theta_term_le (F.A w.2) (F.lower w.2) hz'.le (le_of_lt hw.1) m
  have hmem : Ioi (z.1 / 2) ×ˢ (univ : Set P) ∈ 𝓝 z :=
    prod_mem_nhds (Ioi_mem_nhds (by linarith)) univ_mem
  exact (hcont.continuousAt hmem).continuousWithinAt

variable [IsFiniteMeasure μ]

/-- **The averaged `Λ` is the averaged completed Epstein series** for `re s > d/2`. -/
theorem Λ_eq_integral [Nonempty d] {s : ℂ} (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    (F.fePair μ).Λ s = ∫ p, ∑' m : d → ℤ,
      π ^ (-s) * Gamma s * 1 / ((sqNorm (F.A p (intVec m)) : ℝ) : ℂ) ^ s ∂μ := by
  have hM := (F.fePair μ).hasMellin hs
  rw [← hM.2]
  set H : ℝ → P → ℂ := fun t p =>
    (t : ℂ) ^ (s - 1) * (((latticeTheta (F.A p) t : ℝ) : ℂ) - 1) with hH
  -- the Mellin integral as an iterated integral
  have hstep : mellin (fun t => (F.fePair μ).f t - (F.fePair μ).f₀) s =
      ∫ t in Ioi 0, ∫ p, H t p ∂μ := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hft : (F.fePair μ).f t - (F.fePair μ).f₀ =
        ∫ p, (((latticeTheta (F.A p) t : ℝ) : ℂ) - 1) ∂μ := by
      rw [integral_sub ((F.integrable_theta μ ht0).ofReal) (integrable_const _),
        integral_complex_ofReal, integral_const, Complex.real_smul, mul_one]
      rfl
    simp only [hH, smul_eq_mul]
    rw [hft, integral_const_mul]
  -- domination by one scalar lattice
  obtain ⟨B, hB⟩ := exists_scalar_below (d := d) F.κ_pos
  have hBp : ∀ p m, sqNorm (B (intVec m)) ≤ sqNorm (F.A p (intVec m)) :=
    fun p => hB (F.A p) (F.lower p)
  have hconv := ((thetaFEPair B).hasMellin hs).1
  have hG : Integrable (fun t : ℝ =>
      ‖(t : ℂ) ^ (s - 1) • (((latticeTheta B t : ℝ) : ℂ) - 1)‖) (volume.restrict (Ioi 0)) :=
    hconv.norm
  have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod μ =
      (volume.prod μ).restrict (Ioi 0 ×ˢ (univ : Set P)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hG2 : Integrable (fun z : ℝ × P =>
      ‖(z.1 : ℂ) ^ (s - 1) • (((latticeTheta B z.1 : ℝ) : ℂ) - 1)‖ * (1 : ℝ))
      ((volume.restrict (Ioi 0)).prod μ) := hG.mul_prod (integrable_const 1)
  have hcontH : ContinuousOn (uncurry H) (Ioi 0 ×ˢ (univ : Set P)) := by
    intro z hz
    have hz0 : 0 < z.1 := hz.1
    have h1 : ContinuousWithinAt (fun z : ℝ × P => (z.1 : ℂ) ^ (s - 1))
        (Ioi 0 ×ˢ (univ : Set P)) z :=
      ((continuousAt_ofReal_cpow_const z.1 (s - 1) (Or.inr hz0.ne')).comp
        continuous_fst.continuousAt).continuousWithinAt
    have h2 : ContinuousWithinAt (fun z : ℝ × P => ((latticeTheta (F.A z.2) z.1 : ℝ) : ℂ) - 1)
        (Ioi 0 ×ˢ (univ : Set P)) z :=
      ((continuous_ofReal.continuousAt.comp_continuousWithinAt
        (F.continuousOn_theta_uncurry z hz))).sub continuousWithinAt_const
    exact h1.mul h2
  have hint : Integrable (uncurry H) ((volume.restrict (Ioi 0)).prod μ) := by
    rw [hmeas_eq] at hG2 ⊢
    refine hG2.mono' (hcontH.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ))
      (ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun z hz => ?_)
    have ht : 0 < z.1 := hz.1
    simp only [uncurry, hH, norm_mul, norm_smul, mul_one]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have e1 : ((latticeTheta (F.A z.2) z.1 : ℝ) : ℂ) - 1 =
        ((latticeTheta (F.A z.2) z.1 - 1 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((latticeTheta B z.1 : ℝ) : ℂ) - 1 = ((latticeTheta B z.1 - 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (one_le_latticeTheta _ ht)),
      abs_of_nonneg (sub_nonneg.mpr (one_le_latticeTheta _ ht))]
    linarith [latticeTheta_mono (hBp z.2) ht]
  rw [hstep, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp only
  rw [(hasSum_mellin_latticeTheta (F.A p) hs).tsum_eq]
  unfold mellin
  simp only [hH, smul_eq_mul]

end ThetaFamily

end SimultaneousPrimitiveRoots.Hecke

end

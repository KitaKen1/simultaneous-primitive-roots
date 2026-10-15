module

public import SimultaneousPrimitiveRoots.Hecke.ShiftedFamily
public import SimultaneousPrimitiveRoots.Hecke.AveragedMellin

/-!
# The Mellin transform of an averaged shifted theta function

For a `ThetaFamily` over a finite measure space `(P, μ)` and a shift `v` with `0 ∉ ℤ^d + v`, the
`Λ` of `ThetaFamily.shiftedFEPair` is, for `re s > d/2`, the averaged completed Epstein series of
the coset

`Λ(s) = ∫_P π^{-s} Γ(s) ∑_m |A_p(m + v)|^{-2s} dμ(p)`   (`ThetaFamily.shiftedΛ_eq_integral`).

As `f₀ = 0` nothing is subtracted and every term is positive. So Fubini applies with the
integrability of the iterated integral supplied by the Mellin convergence of the averaged function
itself (`WeakFEPair.hasMellin`); no comparison lattice is needed.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Function Filter Complex Asymptotics
open scoped Real Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
theorem sqNorm_shift_pos (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {v : d → ℝ}
    (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) (m : d → ℤ) : 0 < sqNorm (A (intVec m + v)) := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  have h1 : 0 < ‖intVec m + v‖ := norm_pos_iff.mpr (hv m)
  have h2 := hκA (intVec m + v)
  have h3 : 0 < κ * ‖intVec m + v‖ ^ 2 := by positivity
  linarith

omit [DecidableEq d] in
/-- `‖m + v‖ ≥ c ‖m‖` for a coset avoiding `0`. -/
theorem exists_norm_shift_ge (v : d → ℝ) (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : d → ℤ, c * ‖intVec m‖ ≤ ‖intVec m + v‖ := by
  obtain ⟨δ, hδ, hvδ⟩ := exists_dist_shifted_pos v hv
  have hv0 := norm_nonneg v
  refine ⟨min (1 / 2) (δ / (2 * ‖v‖ + 1)), lt_min (by norm_num) (by positivity), fun m => ?_⟩
  have hn := norm_nonneg (intVec m)
  have htri : ‖intVec m‖ ≤ ‖intVec m + v‖ + ‖v‖ := by
    have := norm_sub_le (intVec m + v) v
    rwa [add_sub_cancel_right] at this
  by_cases h : 2 * ‖v‖ ≤ ‖intVec m‖
  · calc min (1 / 2) (δ / (2 * ‖v‖ + 1)) * ‖intVec m‖ ≤ 1 / 2 * ‖intVec m‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hn
      _ ≤ ‖intVec m + v‖ := by linarith
  · push Not at h
    have h1 : min (1 / 2) (δ / (2 * ‖v‖ + 1)) * ‖intVec m‖ ≤ δ / (2 * ‖v‖ + 1) * ‖intVec m‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hn
    have h2 : δ / (2 * ‖v‖ + 1) * ‖intVec m‖ ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith [hvδ m]

omit [DecidableEq d] in
/-- **The Epstein series of a coset avoiding `0` converges** for `σ > d/2`. -/
theorem summable_shifted_epstein (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {v : d → ℝ}
    (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {σ : ℝ} (hσ : (Fintype.card d : ℝ) / 2 < σ) :
    Summable fun m : d → ℤ => ‖(1 : ℂ)‖ / sqNorm (A (intVec m + v)) ^ σ := by
  obtain ⟨κ, hκ, hκA⟩ := exists_sqNorm_lower A
  obtain ⟨c, hc, hcm⟩ := exists_norm_shift_ge v hv
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  set C : ℝ := κ * c ^ 2 with hC
  have hC0 : 0 < C := by positivity
  have hr : -(2 * σ) < -(Module.finrank ℤ (intSpan d) : ℝ) := by
    rw [finrank_intSpan]
    linarith
  have hL := ZLattice.summable_norm_rpow (intSpan d) (-(2 * σ)) hr
  have hL' : Summable fun m : d → ℤ => C ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)) :=
    ((intSpanEquiv (d := d)).summable_iff.mpr hL).mul_left _
  refine Summable.of_norm_bounded_eventually hL' ?_
  filter_upwards [(Set.finite_singleton (0 : d → ℤ)).compl_mem_cofinite] with m hm
  have hm0 : m ≠ 0 := hm
  have h1 := one_le_norm_intVec hm0
  have hn0 : 0 < ‖intVec m‖ := by linarith
  have hQ := hκA (intVec m + v)
  have hcm' : (c * ‖intVec m‖) ^ 2 ≤ ‖intVec m + v‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) (hcm m) 2
  have hlow : C * ‖intVec m‖ ^ 2 ≤ sqNorm (A (intVec m + v)) := by
    rw [hC]
    nlinarith
  have hpos : 0 < C * ‖intVec m‖ ^ 2 := by positivity
  rw [norm_one, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (Real.rpow_nonneg (sqNorm_nonneg _) _))]
  calc 1 / sqNorm (A (intVec m + v)) ^ σ ≤ 1 / (C * ‖intVec m‖ ^ 2) ^ σ := by
        apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos _)
        exact Real.rpow_le_rpow hpos.le hlow hσ0.le
    _ = C ^ (-σ) * ‖intVec m‖ ^ (-(2 * σ)) := by
        rw [one_div, ← Real.rpow_neg hpos.le, Real.mul_rpow hC0.le (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 2
        push_cast
        ring

omit [DecidableEq d] in
/-- The Mellin transform of one shifted theta function is its completed Epstein series. -/
theorem hasSum_mellin_shiftedTheta (A : (d → ℝ) ≃ₗ[ℝ] (d → ℝ)) {v : d → ℝ}
    (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {s : ℂ} (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    HasSum (fun m : d → ℤ =>
        π ^ (-s) * Gamma s * 1 / ((sqNorm (A (intVec m + v)) : ℝ) : ℂ) ^ s)
      (mellin (fun t => ((shiftedTheta A v t : ℝ) : ℂ)) s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  refine hasSum_mellin_pi_mul₀ (a := fun _ => (1 : ℂ)) (p := fun m => sqNorm (A (intVec m + v)))
    (fun m => sqNorm_nonneg _) hs0 (fun t ht => ?_) (summable_shifted_epstein A hv hs)
  have ht0 : (0 : ℝ) < t := ht
  have h := Complex.hasSum_ofReal.mpr (summable_shiftedTheta A ht0 v).hasSum
  convert h using 1
  · funext m
    have hp := (sqNorm_shift_pos A hv m).ne'
    simp only [hp, ↓reduceIte, one_mul]
    congr 2
    ring
  · rfl

namespace ThetaFamily

variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
variable (F : ThetaFamily d P) (μ : Measure P) (v : d → ℝ)

omit [MeasurableSpace P] [OpensMeasurableSpace P] in
/-- Joint continuity of `(t, p) ↦ θ_{A_p,v}(t)` on `t > 0`. -/
theorem continuousOn_shiftedTheta_uncurry :
    ContinuousOn (fun z : ℝ × P => shiftedTheta (F.A z.2) v z.1) (Ioi 0 ×ˢ univ) := by
  intro z hz
  have hz0 : 0 < z.1 := hz.1
  have hz' : (0 : ℝ) < z.1 / 2 := by positivity
  have hκ := F.κ_pos
  have hcont : ContinuousOn (fun z : ℝ × P => shiftedTheta (F.A z.2) v z.1)
      (Ioi (z.1 / 2) ×ˢ univ) := by
    unfold shiftedTheta
    refine continuousOn_tsum
      (u := fun m : d → ℤ => Real.exp (-(π * (z.1 / 2) * F.κ) * ‖intVec m + v‖ ^ 2))
      (fun m => ?_) (summable_exp_neg_norm_sq_shift (by positivity) v) (fun m w hw => ?_)
    · have hs : Continuous (sqNorm (d := d)) := by
        unfold sqNorm
        fun_prop
      have h1 : Continuous fun w : ℝ × P => sqNorm (F.A w.2 (intVec m + v)) :=
        hs.comp ((F.continuous_A (intVec m + v)).comp continuous_snd)
      exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_fst).neg.mul h1)).continuousOn
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact exp_shifted_term_le (F.A w.2) (F.lower w.2) hz'.le (le_of_lt hw.1) v m
  have hmem : Ioi (z.1 / 2) ×ˢ (univ : Set P) ∈ 𝓝 z :=
    prod_mem_nhds (Ioi_mem_nhds (by linarith)) univ_mem
  exact (hcont.continuousAt hmem).continuousWithinAt

variable [IsFiniteMeasure μ]

/-- **The averaged shifted `Λ` is the averaged completed Epstein series of the coset**, for
`re s > d/2`. -/
theorem shiftedΛ_eq_integral [Nonempty d] (hv : ∀ m : d → ℤ, intVec m + v ≠ 0) {s : ℂ}
    (hs : (Fintype.card d : ℝ) / 2 < s.re) :
    (F.shiftedFEPair μ v hv).Λ s = ∫ p, ∑' m : d → ℤ,
      π ^ (-s) * Gamma s * 1 / ((sqNorm (F.A p (intVec m + v)) : ℝ) : ℂ) ^ s ∂μ := by
  have hM := (F.shiftedFEPair μ v hv).hasMellin hs
  rw [← hM.2]
  set H : ℝ → P → ℂ := fun t p => (t : ℂ) ^ (s - 1) * ((shiftedTheta (F.A p) v t : ℝ) : ℂ)
    with hH
  -- the averaged function at a point `t > 0`
  have hft : ∀ t, (F.shiftedFEPair μ v hv).f t - (F.shiftedFEPair μ v hv).f₀ =
      ∫ p, ((shiftedTheta (F.A p) v t : ℝ) : ℂ) ∂μ := by
    intro t
    rw [shiftedFEPair_f₀, sub_zero, integral_complex_ofReal]
    rfl
  -- the Mellin integral as an iterated integral
  have hstep : mellin (fun t => (F.shiftedFEPair μ v hv).f t - (F.shiftedFEPair μ v hv).f₀) s =
      ∫ t in Ioi 0, ∫ p, H t p ∂μ := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hH, smul_eq_mul]
    rw [hft, integral_const_mul]
  have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod μ =
      (volume.prod μ).restrict (Ioi 0 ×ˢ (univ : Set P)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hcontH : ContinuousOn (uncurry H) (Ioi 0 ×ˢ (univ : Set P)) := by
    intro z hz
    have hz0 : 0 < z.1 := hz.1
    have h1 : ContinuousWithinAt (fun z : ℝ × P => (z.1 : ℂ) ^ (s - 1))
        (Ioi 0 ×ˢ (univ : Set P)) z :=
      ((continuousAt_ofReal_cpow_const z.1 (s - 1) (Or.inr hz0.ne')).comp
        continuous_fst.continuousAt).continuousWithinAt
    have h2 : ContinuousWithinAt (fun z : ℝ × P => ((shiftedTheta (F.A z.2) v z.1 : ℝ) : ℂ))
        (Ioi 0 ×ˢ (univ : Set P)) z :=
      continuous_ofReal.continuousAt.comp_continuousWithinAt
        (F.continuousOn_shiftedTheta_uncurry v z hz)
    exact h1.mul h2
  have hmeasH : AEStronglyMeasurable (uncurry H) ((volume.restrict (Ioi 0)).prod μ) := by
    rw [hmeas_eq]
    exact hcontH.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  -- integrability on the product: the `p`-integral of the norm is the Mellin integrand
  have hint : Integrable (uncurry H) ((volume.restrict (Ioi 0)).prod μ) := by
    rw [integrable_prod_iff hmeasH]
    refine ⟨ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_, ?_⟩
    · show Integrable (fun p => (t : ℂ) ^ (s - 1) * ((shiftedTheta (F.A p) v t : ℝ) : ℂ)) μ
      exact ((F.integrable_shiftedTheta μ v ht).ofReal (𝕜 := ℂ)).const_mul _
    · refine hM.1.norm.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_)
      have hnn : ∀ p, ‖H t p‖ = ‖(t : ℂ) ^ (s - 1)‖ * shiftedTheta (F.A p) v t := fun p => by
        rw [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (shiftedTheta_nonneg _ _ _)]
      simp only [uncurry_apply_pair, hnn]
      rw [integral_const_mul, hft, smul_eq_mul, norm_mul, integral_complex_ofReal,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun p => shiftedTheta_nonneg _ _ _)]
  rw [hstep, integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp only
  rw [(hasSum_mellin_shiftedTheta (F.A p) hv hs).tsum_eq]
  unfold mellin
  simp only [hH, smul_eq_mul]

end ThetaFamily

end SimultaneousPrimitiveRoots.Hecke

end

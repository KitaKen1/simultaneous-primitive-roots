module

public import SimultaneousPrimitiveRoots.WeightedLogDerivativeBounds

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Integrate one smooth log coordinate against an arbitrary measurable L1
tail. The tail can include finite-place, angular and class factors. -/
def artinShiftedIntegralJet (μ : Measure X) (τ : X → ℝ) (J : ℕ → ℝ → ℂ)
    (g : X → ℂ) (j : ℕ) (v : ℝ) : ℂ := ∫ x, J j (v + τ x) * g x ∂μ

theorem artinShiftedIntegralJet_integrable {τ : X → ℝ} {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hτ : Measurable τ) (hc : ∀ j, Continuous (J j))
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g μ)
    (j : ℕ) (v : ℝ) : Integrable (fun x => J j (v + τ x) * g x) μ := by
  obtain ⟨M, _, hM⟩ := hb j
  apply (hg.norm.const_mul M).mono'
    (((hc j).measurable.comp (measurable_const.add hτ)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    change ‖J j (v + τ x) * g x‖ ≤ M * ‖g x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))

theorem artinShiftedIntegralJet_hasDerivAt {τ : X → ℝ} {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hτ : Measurable τ)
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g μ)
    (j : ℕ) (v : ℝ) :
    HasDerivAt (artinShiftedIntegralJet μ τ J g j)
      (artinShiftedIntegralJet μ τ J g (j + 1) v) v := by
  have hc (j : ℕ) : Continuous (J j) :=
    (show Differentiable ℝ (J j) from fun v => (hJ j v).differentiableAt).continuous
  unfold artinShiftedIntegralJet
  apply artinIntegralJet_hasDerivAt (F := fun j v x => J j (v + τ x) * g x)
  · intro j v
    exact ((hc j).measurable.comp (measurable_const.add hτ)).aestronglyMeasurable.mul
      hg.aestronglyMeasurable
  · intro j
    obtain ⟨M, _, hM⟩ := hb j
    refine ⟨fun x => M * ‖g x‖, hg.norm.const_mul M, ae_of_all _ (fun x v => ?_)⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · intro j
    exact ae_of_all _ (fun x v => by
      simpa only [one_smul, Function.comp_apply, id_eq] using!
        ((hJ j (v + τ x)).scomp v ((hasDerivAt_id v).add_const (τ x))).mul_const (g x))

theorem artinShiftedIntegralJet_bound {τ : X → ℝ} {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M)
    (hg : Integrable g μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ v, ‖artinShiftedIntegralJet μ τ J g j v‖ ≤ M := by
  obtain ⟨M, _, hM⟩ := hb j
  refine ⟨max 1 (∫ x, M * ‖g x‖ ∂μ), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun v => ?_⟩
  apply le_trans _ (le_max_right _ _)
  exact norm_integral_le_of_norm_le (hg.norm.const_mul M) (ae_of_all _ (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)))

theorem artinShiftedIntegralJet_smooth_bounded {τ : X → ℝ} {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hτ : Measurable τ)
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g μ) :
    ContDiff ℝ ∞ (artinShiftedIntegralJet μ τ J g 0) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j (artinShiftedIntegralJet μ τ J g 0) v‖ ≤ M := by
  have hd := artinShiftedIntegralJet_hasDerivAt hτ hJ hb hg
  refine ⟨artinJetChain_contDiff hd, fun j => ?_⟩
  rw [artinJetChain_iteratedDeriv hd]
  exact artinShiftedIntegralJet_bound hb hg j

/-- A bounded measurable class/angular factor is absorbed into the L1 tail.
It need not be differentiable as a function on X. -/
theorem artinIntegrable_bounded_multiplier {g a : X → ℂ} (hg : Integrable g μ)
    (ha : AEStronglyMeasurable a μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    Integrable (fun x => a x * g x) μ := by
  apply (hg.norm.const_mul M).mono' (ha.mul hg.aestronglyMeasurable)
  exact hb.mono (fun x hx => by
    change ‖a x * g x‖ ≤ M * ‖g x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def artinShiftedBesselProfile (μ : Measure X) (c : ℝ) (τ : X → ℝ)
    (g : X → ℂ) (u : ℝ) : ℂ :=
  ∫ x, artinBesselLocalProfile c (u * Real.exp (-τ x)) * g x ∂μ

def artinShiftedBesselTail (σ : ℝ) (τ : X → ℝ) (g : X → ℂ) (x : X) : ℂ :=
  Complex.exp ((σ : ℂ) * τ x) * g x

def artinShiftedBesselLogJet (μ : Measure X) (c σ : ℝ) (τ : X → ℝ)
    (g : X → ℂ) : ℕ → ℝ → ℂ :=
  artinShiftedIntegralJet μ τ (artinBesselLogJet c σ) (artinShiftedBesselTail σ τ g)

theorem artinShiftedBesselTail_bounded_multiplier_integrable {σ : ℝ} {τ : X → ℝ}
    {g a : X → ℂ} (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (ha : AEStronglyMeasurable a μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    Integrable (artinShiftedBesselTail σ τ (fun x => a x * g x)) μ := by
  apply (artinIntegrable_bounded_multiplier hg ha hb).congr
  exact ae_of_all _ (fun x => by dsimp only [artinShiftedBesselTail]; ring)

theorem artinShiftedBesselLogJet_zero {c : ℝ} (hc : 0 < c) (σ : ℝ)
    (τ : X → ℝ) (g : X → ℂ) :
    artinShiftedBesselLogJet μ c σ τ g 0 =
      artinMellinLogPullback (artinShiftedBesselProfile μ c τ g) (σ : ℂ) := by
  funext v
  simp only [artinShiftedBesselLogJet, artinShiftedIntegralJet,
    artinBesselLogJet_zero hc σ, artinShiftedBesselTail, artinMellinLogPullback,
    artinShiftedBesselProfile]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [show -(v + τ x) = -v + -τ x by ring, Real.exp_add]
    have he : Complex.exp (-(σ : ℂ) * (v + τ x : ℝ)) *
        Complex.exp ((σ : ℂ) * τ x) = Complex.exp (-(σ : ℂ) * v) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (Complex.exp (-(σ : ℂ) * (v + τ x : ℝ)) * Complex.exp ((σ : ℂ) * τ x)) *
        (artinBesselLocalProfile c (Real.exp (-v) * Real.exp (-τ x)) * g x) := by ring
      _ = _ := by rw [he])

theorem artinShiftedBesselProfile_log_smooth_bounded {c σ : ℝ} {τ : X → ℝ}
    {g : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hτ : Measurable τ) (hg : Integrable (artinShiftedBesselTail σ τ g) μ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinShiftedBesselProfile μ c τ g) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j
          (artinMellinLogPullback (artinShiftedBesselProfile μ c τ g) (σ : ℂ)) v‖ ≤ M := by
  rw [← artinShiftedBesselLogJet_zero hc σ τ g]
  exact artinShiftedIntegralJet_smooth_bounded hτ (artinBesselLogJet_hasDerivAt hc hσ)
    (artinBesselLogJet_bound hc hσ) hg

theorem artinShiftedBesselProfile_contDiffOn {c σ : ℝ} {τ : X → ℝ} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) :
    ContDiffOn ℝ ∞ (artinShiftedBesselProfile μ c τ g) (Ioi 0) :=
  artinProfile_contDiffOn_of_log (artinShiftedBesselProfile_log_smooth_bounded hc hσ hτ hg).1

theorem artinShiftedBesselProfile_bounded_multiplier_log_smooth {c σ : ℝ}
    {τ : X → ℝ} {g a : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hτ : Measurable τ) (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (ha : AEStronglyMeasurable a μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    ContDiff ℝ ∞ (artinMellinLogPullback
      (artinShiftedBesselProfile μ c τ (fun x => a x * g x)) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ B, 0 < B ∧ ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinShiftedBesselProfile μ c τ (fun x => a x * g x)) (σ : ℂ)) v‖ ≤ B :=
  artinShiftedBesselProfile_log_smooth_bounded hc hσ hτ
    (artinShiftedBesselTail_bounded_multiplier_integrable hg ha hb)

theorem artinShiftedBesselProfile_logJet_power_bound {c σ : ℝ} {τ : X → ℝ}
    {g : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinShiftedBesselProfile μ c τ g) j u‖ ≤ M * u ^ (-σ) := by
  have h := artinShiftedBesselProfile_log_smooth_bounded hc hσ hτ hg
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinShiftedBesselProfile_logJet_two_ended {c α A : ℝ} {τ : X → ℝ}
    {g : X → ℂ} (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A)
    (hτ : Measurable τ)
    (hgα : Integrable (artinShiftedBesselTail (-α) τ g) μ)
    (hgA : Integrable (artinShiftedBesselTail A τ g) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinShiftedBesselProfile μ c τ g) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M, hM, hbM⟩ := artinShiftedBesselProfile_logJet_power_bound hc
    (σ := -α) (by linarith) hτ hgα j
  obtain ⟨N, hN, hbN⟩ := artinShiftedBesselProfile_logJet_power_bound hc
    (σ := A) (by linarith) hτ hgA j
  refine ⟨max M N, lt_of_lt_of_le hM (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg (u ^ α) (u ^ (-A))
    (le_of_lt (lt_of_lt_of_le hM (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hbM u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M N) (Real.rpow_nonneg hu.le _))
  · exact (hbN u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M N) (Real.rpow_nonneg hu.le _))

end
end SimultaneousPrimitiveRoots

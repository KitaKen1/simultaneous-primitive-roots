module

public import SimultaneousPrimitiveRoots.ShiftedBesselProfiles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The same constant works for every unit-bounded mask and every shift.
No finiteness of the mask parameter set is needed. -/
theorem artinShiftedIntegralJet_unit_mask_uniform_bound {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M)
    (hg : Integrable g μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (τ : X → ℝ) (a : X → ℂ), (∀ x, ‖a x‖ ≤ 1) →
      ∀ v, ‖artinShiftedIntegralJet μ τ J (fun x => a x * g x) j v‖ ≤ M := by
  obtain ⟨M, hM, hbM⟩ := hb j
  refine ⟨max 1 (∫ x, M * ‖g x‖ ∂μ), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun τ a ha v => ?_⟩
  apply le_trans _ (le_max_right _ _)
  apply norm_integral_le_of_norm_le (hg.norm.const_mul M)
  exact ae_of_all _ (fun x => by
    calc
      ‖J j (v + τ x) * (a x * g x)‖ = ‖J j (v + τ x)‖ * (‖a x‖ * ‖g x‖) := by
        simp only [norm_mul]
      _ ≤ M * (1 * ‖g x‖) := mul_le_mul (hbM _) (mul_le_mul_of_nonneg_right (ha x)
        (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM.le
      _ = _ := by ring)

theorem artinShiftedIntegralJet_iteratedDeriv {τ : X → ℝ} {J : ℕ → ℝ → ℂ}
    {g : X → ℂ} (hτ : Measurable τ)
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g μ) (j : ℕ) :
    iteratedDeriv j (artinShiftedIntegralJet μ τ J g 0) =
      artinShiftedIntegralJet μ τ J g j :=
  artinJetChain_iteratedDeriv (artinShiftedIntegralJet_hasDerivAt hτ hJ hb hg) j

theorem artinShiftedIntegralJet_unit_mask_uniform_iteratedDeriv {τ : X → ℝ}
    {J : ℕ → ℝ → ℂ} {g : X → ℂ} (hτ : Measurable τ)
    (hJ : ∀ j v, HasDerivAt (J j) (J (j + 1) v) v)
    (hb : ∀ j, ∃ M, 0 < M ∧ ∀ v, ‖J j v‖ ≤ M) (hg : Integrable g μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (a : X → ℂ), AEStronglyMeasurable a μ → (∀ x, ‖a x‖ ≤ 1) →
      ∀ v, ‖iteratedDeriv j (artinShiftedIntegralJet μ τ J (fun x => a x * g x) 0) v‖ ≤ M := by
  obtain ⟨M, hM, hbM⟩ := artinShiftedIntegralJet_unit_mask_uniform_bound hb hg j
  refine ⟨M, hM, fun a ha hba v => ?_⟩
  rw [artinShiftedIntegralJet_iteratedDeriv hτ hJ hb
    (artinIntegrable_bounded_multiplier hg ha (ae_of_all _ hba))]
  exact hbM τ a hba v

/-- For fixed c, sigma, measure, shift and unmasked tail, one constant per
order controls every measurable mask of norm at most one. This is not a
uniform estimate for a family of varying number fields. -/
theorem artinShiftedBesselProfile_unit_mask_uniform_log_jets {c σ : ℝ}
    {τ : X → ℝ} {g : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hτ : Measurable τ) (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (a : X → ℂ), AEStronglyMeasurable a μ → (∀ x, ‖a x‖ ≤ 1) →
      ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinShiftedBesselProfile μ c τ (fun x => a x * g x)) (σ : ℂ)) v‖ ≤ M := by
  obtain ⟨M, hM, hbM⟩ := artinShiftedIntegralJet_unit_mask_uniform_bound
    (artinBesselLogJet_bound hc hσ) hg j
  refine ⟨M, hM, fun a ha hba v => ?_⟩
  rw [← artinShiftedBesselLogJet_zero hc σ τ (fun x => a x * g x)]
  unfold artinShiftedBesselLogJet
  rw [artinShiftedIntegralJet_iteratedDeriv hτ (artinBesselLogJet_hasDerivAt hc hσ)
    (artinBesselLogJet_bound hc hσ)
    (artinShiftedBesselTail_bounded_multiplier_integrable hg ha (ae_of_all _ hba))]
  have heq : artinShiftedBesselTail σ τ (fun x => a x * g x) =
      fun x => a x * artinShiftedBesselTail σ τ g x := by
    funext x
    dsimp only [artinShiftedBesselTail]
    ring
  rw [heq]
  exact hbM τ a hba v

end
end SimultaneousPrimitiveRoots

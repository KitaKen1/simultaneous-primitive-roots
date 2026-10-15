module

public import SimultaneousPrimitiveRoots.ReflectedClassBesselProfiles
public import SimultaneousPrimitiveRoots.UnitMaskUniformLogJets

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section
variable {G H : Type*} [Monoid G] [Monoid H]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Constants may be chosen before the class and angular masks. -/
theorem artinRadialClassBesselProfile_unit_masks_uniform_log_jets (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle),
      (∀ h, ‖b h‖ ≤ 1) → AEStronglyMeasurable (fun x => b (χ (z x))) μ →
      AEStronglyMeasurable
        (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ →
      ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinRadialClassBesselProfile μ n c χ b η τ z g) (σ : ℂ)) v‖ ≤ M := by
  obtain ⟨M, hM, hbM⟩ := artinShiftedBesselProfile_unit_mask_uniform_log_jets hc hσ hτ hg j
  refine ⟨M, hM, fun b η hba hb hη v => ?_⟩
  rw [artinRadialClassBesselProfile_eq_shifted n hk c χ he]
  exact hbM _ (artinRadialClassMultiplier_aestronglyMeasurable n hk χ he b η z hb hη 1)
    (fun x => artinRadialClassMultiplier_bounded n hk χ he b η hba (z x) 1) v

end

section
variable {G H X : Type*} [Monoid G] [Group H] [MeasurableSpace X] {μ : Measure X}

/-- One constant per order is uniform in the reflected row class kappa, even
for an infinite class group of exponent k. The underlying K profile, measure,
shift and unmasked L1 tail stay fixed. -/
theorem artinReflectedClassBesselProfile_uniform_in_kappa (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hB : ∀ κ, MeasurableSet {x | κ * (χ (z x))⁻¹ ∈ B})
    (hphase : ∀ κ, AEStronglyMeasurable (fun x => (phase κ (χ (z x)) : ℂ)) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ κ v, ‖iteratedDeriv j (artinMellinLogPullback
      (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) (σ : ℂ)) v‖ ≤ M := by
  obtain ⟨M, hM, hbM⟩ := artinRadialClassBesselProfile_unit_masks_uniform_log_jets
    n hk χ he hc hσ hτ hg j
  refine ⟨M, hM, fun κ v => ?_⟩
  exact hbM (artinReflectedClassMask B phase κ) η
    (artinReflectedClassMask_norm_le_one B phase κ)
    (artinReflectedClassMask_aestronglyMeasurable B phase κ (fun x => χ (z x)) (hB κ) (hphase κ))
    hη v

end
end SimultaneousPrimitiveRoots

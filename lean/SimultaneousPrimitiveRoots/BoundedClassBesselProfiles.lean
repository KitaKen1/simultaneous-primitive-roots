module

public import SimultaneousPrimitiveRoots.RadialClassBesselProfiles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section
variable {G H : Type*} [Monoid G] [Monoid H]

/-- Direct class bounds do not require a finite class quotient. -/
theorem artinRadialClassMultiplier_bounded (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {M : ℝ} (hb : ∀ h, ‖b h‖ ≤ M)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) :
    ‖artinRadialClassMultiplier n χ b η z u‖ ≤ M := by
  rw [artinRadialClassMultiplier_norm n hk χ he]
  exact hb _

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem artinRadialClassBesselProfile_bounded_tail_integrable (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {σ M : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hM : ∀ h, ‖b h‖ ≤ M)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    Integrable (artinShiftedBesselTail σ τ
      (fun x => artinRadialClassMultiplier n χ b η (z x) 1 * g x)) μ :=
  artinShiftedBesselTail_bounded_multiplier_integrable hg
    (artinRadialClassMultiplier_aestronglyMeasurable n hk χ he b η z hb hη 1)
    (ae_of_all _ (fun x => artinRadialClassMultiplier_bounded n hk χ he b η hM (z x) 1))

theorem artinRadialClassBesselProfile_bounded_log_smooth (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ M : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (hM : ∀ h, ‖b h‖ ≤ M)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    ContDiff ℝ ∞ (artinMellinLogPullback
      (artinRadialClassBesselProfile μ n c χ b η τ z g) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ B, 0 < B ∧ ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinRadialClassBesselProfile μ n c χ b η τ z g) (σ : ℂ)) v‖ ≤ B := by
  rw [artinRadialClassBesselProfile_eq_shifted n hk c χ he]
  exact artinShiftedBesselProfile_log_smooth_bounded hc hσ hτ
    (artinRadialClassBesselProfile_bounded_tail_integrable n hk χ he b η hg hM hb hη)

theorem artinRadialClassBesselProfile_bounded_contDiffOn (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ M : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (hM : ∀ h, ‖b h‖ ≤ M)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    ContDiffOn ℝ ∞ (artinRadialClassBesselProfile μ n c χ b η τ z g) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinRadialClassBesselProfile_bounded_log_smooth n hk χ he b η hc hσ hτ hg hM hb hη).1

theorem artinRadialClassBesselProfile_bounded_logJet_power_bound (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ M : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ) (hM : ∀ h, ‖b h‖ ≤ M)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ B, 0 < B ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinRadialClassBesselProfile μ n c χ b η τ z g) j u‖ ≤
        B * u ^ (-σ) := by
  have h := artinRadialClassBesselProfile_bounded_log_smooth n hk χ he b η hc hσ hτ hg hM hb hη
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinRadialClassBesselProfile_bounded_logJet_two_ended (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c α A M : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A) (hτ : Measurable τ)
    (hgα : Integrable (artinShiftedBesselTail (-α) τ g) μ)
    (hgA : Integrable (artinShiftedBesselTail A τ g) μ) (hM : ∀ h, ‖b h‖ ≤ M)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ B, 0 < B ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinRadialClassBesselProfile μ n c χ b η τ z g) j u‖ ≤
        B * min (u ^ α) (u ^ (-A)) := by
  rw [artinRadialClassBesselProfile_eq_shifted n hk c χ he]
  exact artinShiftedBesselProfile_logJet_two_ended hc hα hA hτ
    (artinRadialClassBesselProfile_bounded_tail_integrable n hk χ he b η hgα hM hb hη)
    (artinRadialClassBesselProfile_bounded_tail_integrable n hk χ he b η hgA hM hb hη) j

end
end SimultaneousPrimitiveRoots

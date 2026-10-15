module

public import SimultaneousPrimitiveRoots.BoundedClassBesselProfiles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots
open Classical MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section
variable {H : Type*} [Group H]

/-- The reflected class multiplier, with an actual indicator and squared phase.
Its identification with the manuscript Hilbert pairing is a separate task. -/
def artinReflectedClassMask (B : Set H) (phase : H → H → Circle) (κ h : H) : ℂ :=
  if κ * h⁻¹ ∈ B then (phase κ h : ℂ) ^ 2 else 0

theorem artinReflectedClassMask_of_mem (B : Set H) (phase : H → H → Circle)
    (κ h : H) (hh : κ * h⁻¹ ∈ B) :
    artinReflectedClassMask B phase κ h = (phase κ h : ℂ) ^ 2 := by
  simp [artinReflectedClassMask, hh]

theorem artinReflectedClassMask_of_not_mem (B : Set H) (phase : H → H → Circle)
    (κ h : H) (hh : κ * h⁻¹ ∉ B) : artinReflectedClassMask B phase κ h = 0 := by
  simp [artinReflectedClassMask, hh]

theorem artinReflectedClassMask_norm (B : Set H) (phase : H → H → Circle)
    (κ h : H) : ‖artinReflectedClassMask B phase κ h‖ = if κ * h⁻¹ ∈ B then 1 else 0 := by
  by_cases hh : κ * h⁻¹ ∈ B <;> simp [artinReflectedClassMask, hh, norm_pow]

theorem artinReflectedClassMask_norm_le_one (B : Set H) (phase : H → H → Circle)
    (κ h : H) : ‖artinReflectedClassMask B phase κ h‖ ≤ 1 := by
  rw [artinReflectedClassMask_norm]
  split <;> norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem artinReflectedClassMask_aestronglyMeasurable (B : Set H)
    (phase : H → H → Circle) (κ : H) (f : X → H)
    (hB : MeasurableSet {x | κ * (f x)⁻¹ ∈ B})
    (hphase : AEStronglyMeasurable (fun x => (phase κ (f x) : ℂ)) μ) :
    AEStronglyMeasurable (fun x => artinReflectedClassMask B phase κ (f x)) μ := by
  have h := (hphase.fun_mul hphase).indicator hB
  apply h.congr
  exact ae_of_all _ (fun x => by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, artinReflectedClassMask, pow_two])

variable {G : Type*} [Monoid G]

def artinReflectedClassBesselProfile (μ : Measure X) (n : ℕ) (c : ℝ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (B : Set H)
    (phase : H → H → Circle) (κ : H) (η : (Fin (n + 1) → Circle) → Circle)
    (τ : X → ℝ) (z : X → G × (Fin (n + 1) → ℂˣ)) (g : X → ℂ) (u : ℝ) : ℂ :=
  artinRadialClassBesselProfile μ n c χ (artinReflectedClassMask B phase κ) η τ z g u

theorem artinReflectedClassBesselProfile_eq_integral (n : ℕ) (c : ℝ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (B : Set H)
    (phase : H → H → Circle) (κ : H) (η : (Fin (n + 1) → Circle) → Circle)
    (τ : X → ℝ) (z : X → G × (Fin (n + 1) → ℂˣ)) (g : X → ℂ) (u : ℝ) :
    artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g u =
      ∫ x, artinBesselLocalProfile c (u * Real.exp (-τ x)) *
        ((if κ * (χ (artinFiniteComplexNormSection n u * z x))⁻¹ ∈ B
          then (phase κ (χ (artinFiniteComplexNormSection n u * z x)) : ℂ) ^ 2 else 0) *
          (η (fun i => artinComplexUnitAngle ((artinComplexNormSection n u * (z x).2) i)) : ℂ) *
          g x) ∂μ := rfl

theorem artinReflectedClassMultiplier_norm_le_one (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (κ : H)
    (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) :
    ‖artinRadialClassMultiplier n χ (artinReflectedClassMask B phase κ) η z u‖ ≤ 1 :=
  artinRadialClassMultiplier_bounded n hk χ he _ η
    (artinReflectedClassMask_norm_le_one B phase κ) z u

theorem artinReflectedClassBesselProfile_log_smooth (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (κ : H)
    (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hB : MeasurableSet {x | κ * (χ (z x))⁻¹ ∈ B})
    (hphase : AEStronglyMeasurable (fun x => (phase κ (χ (z x)) : ℂ)) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    ContDiff ℝ ∞ (artinMellinLogPullback
      (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) (σ : ℂ)) v‖ ≤ M :=
  artinRadialClassBesselProfile_bounded_log_smooth n hk χ he _ η hc hσ hτ hg
    (artinReflectedClassMask_norm_le_one B phase κ)
    (artinReflectedClassMask_aestronglyMeasurable B phase κ (fun x => χ (z x)) hB hphase) hη

theorem artinReflectedClassBesselProfile_logJet_two_ended (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (B : Set H) (phase : H → H → Circle) (κ : H)
    (η : (Fin (n + 1) → Circle) → Circle)
    {c α A : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hα : α < 5 / 6) (hA : 0 < A) (hτ : Measurable τ)
    (hgα : Integrable (artinShiftedBesselTail (-α) τ g) μ)
    (hgA : Integrable (artinShiftedBesselTail A τ g) μ)
    (hB : MeasurableSet {x | κ * (χ (z x))⁻¹ ∈ B})
    (hphase : AEStronglyMeasurable (fun x => (phase κ (χ (z x)) : ℂ)) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinReflectedClassBesselProfile μ n c χ B phase κ η τ z g) j u‖ ≤
        M * min (u ^ α) (u ^ (-A)) :=
  artinRadialClassBesselProfile_bounded_logJet_two_ended n hk χ he _ η hc hα hA hτ hgα hgA
    (artinReflectedClassMask_norm_le_one B phase κ)
    (artinReflectedClassMask_aestronglyMeasurable B phase κ (fun x => χ (z x)) hB hphase) hη j

end
end SimultaneousPrimitiveRoots

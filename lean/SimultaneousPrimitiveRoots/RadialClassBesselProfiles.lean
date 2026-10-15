module

public import SimultaneousPrimitiveRoots.NormSectionPowers
public import SimultaneousPrimitiveRoots.ShiftedBesselProfiles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff
noncomputable section

variable {G H : Type*} [Monoid G] [Monoid H]

/-- Actual class and angular factors are evaluated after radial transport.
The bounded class function remains inside the integral. -/
def artinRadialClassMultiplier (n : ℕ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (b : H → ℂ)
    (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) : ℂ :=
  b (χ (artinFiniteComplexNormSection n u * z)) *
    (η (fun i => artinComplexUnitAngle ((artinComplexNormSection n u * z.2) i)) : ℂ)

theorem artinRadialClassMultiplier_eq (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) :
    artinRadialClassMultiplier n χ b η z u =
      b (χ z) * (η (fun i => artinComplexUnitAngle (z.2 i)) : ℂ) := by
  unfold artinRadialClassMultiplier
  rw [artinFiniteComplexNormSection_class_mul n hk χ he u z,
    artinComplexNormSection_angle_mul]

theorem artinRadialClassMultiplier_radial_invariant (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u v : ℝ) :
    artinRadialClassMultiplier n χ b η z u = artinRadialClassMultiplier n χ b η z v := by
  rw [artinRadialClassMultiplier_eq n hk χ he, artinRadialClassMultiplier_eq n hk χ he]

theorem artinRadialClassMultiplier_norm (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) :
    ‖artinRadialClassMultiplier n χ b η z u‖ = ‖b (χ z)‖ := by
  rw [artinRadialClassMultiplier_eq n hk χ he, norm_mul, Circle.norm_coe, mul_one]

theorem artinRadialClassMultiplier_finite_bound [Fintype H] (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    (z : G × (Fin (n + 1) → ℂˣ)) (u : ℝ) :
    ‖artinRadialClassMultiplier n χ b η z u‖ ≤ ∑ h : H, ‖b h‖ := by
  rw [artinRadialClassMultiplier_norm n hk χ he]
  exact Finset.single_le_sum (fun h _ => norm_nonneg (b h)) (Finset.mem_univ (χ z))

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem artinRadialClassMultiplier_aestronglyMeasurable (n : ℕ) {k : ℕ} (hk : 0 < k)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    (z : X → G × (Fin (n + 1) → ℂˣ))
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (u : ℝ) :
    AEStronglyMeasurable (fun x => artinRadialClassMultiplier n χ b η (z x) u) μ := by
  simpa only [artinRadialClassMultiplier_eq n hk χ he] using hb.fun_mul hη

def artinRadialClassBesselProfile (μ : Measure X) (n : ℕ) (c : ℝ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (b : H → ℂ)
    (η : (Fin (n + 1) → Circle) → Circle) (τ : X → ℝ)
    (z : X → G × (Fin (n + 1) → ℂˣ)) (g : X → ℂ) (u : ℝ) : ℂ :=
  ∫ x, artinBesselLocalProfile c (u * Real.exp (-τ x)) *
    (artinRadialClassMultiplier n χ b η (z x) u * g x) ∂μ

/-- Pointwise integral identity; this profile is not defined by a Mellin answer. -/
theorem artinRadialClassBesselProfile_eq_shifted (n : ℕ) {k : ℕ} (hk : 0 < k) (c : ℝ)
    (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle) (τ : X → ℝ)
    (z : X → G × (Fin (n + 1) → ℂˣ)) (g : X → ℂ) :
    artinRadialClassBesselProfile μ n c χ b η τ z g =
      artinShiftedBesselProfile μ c τ
        (fun x => artinRadialClassMultiplier n χ b η (z x) 1 * g x) := by
  funext u
  unfold artinRadialClassBesselProfile artinShiftedBesselProfile
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [artinRadialClassMultiplier_radial_invariant n hk χ he b η (z x) u 1])

/-- Finiteness supplies the uniform-in-class bound. Measurability and the
actual unmasked weighted L1 tail remain explicit application hypotheses. -/
theorem artinRadialClassBesselProfile_log_smooth_bounded [Fintype H] (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    ContDiff ℝ ∞ (artinMellinLogPullback
      (artinRadialClassBesselProfile μ n c χ b η τ z g) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ B, 0 < B ∧ ∀ v, ‖iteratedDeriv j (artinMellinLogPullback
        (artinRadialClassBesselProfile μ n c χ b η τ z g) (σ : ℂ)) v‖ ≤ B := by
  rw [artinRadialClassBesselProfile_eq_shifted n hk c χ he]
  exact artinShiftedBesselProfile_bounded_multiplier_log_smooth hc hσ hτ hg
    (artinRadialClassMultiplier_aestronglyMeasurable n hk χ he b η z hb hη 1)
    (ae_of_all _ (fun x => artinRadialClassMultiplier_finite_bound n hk χ he b η (z x) 1))

theorem artinRadialClassBesselProfile_contDiffOn [Fintype H] (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) :
    ContDiffOn ℝ ∞ (artinRadialClassBesselProfile μ n c χ b η τ z g) (Ioi 0) :=
  artinProfile_contDiffOn_of_log
    (artinRadialClassBesselProfile_log_smooth_bounded n hk χ he b η hc hσ hτ hg hb hη).1

theorem artinRadialClassBesselProfile_logJet_power_bound [Fintype H] (n : ℕ) {k : ℕ}
    (hk : 0 < k) (χ : (G × (Fin (n + 1) → ℂˣ)) →* H) (he : ∀ h : H, h ^ k = 1)
    (b : H → ℂ) (η : (Fin (n + 1) → Circle) → Circle)
    {c σ : ℝ} {τ : X → ℝ} {z : X → G × (Fin (n + 1) → ℂˣ)} {g : X → ℂ}
    (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ) (hτ : Measurable τ)
    (hg : Integrable (artinShiftedBesselTail σ τ g) μ)
    (hb : AEStronglyMeasurable (fun x => b (χ (z x))) μ)
    (hη : AEStronglyMeasurable
      (fun x => (η (fun i => artinComplexUnitAngle ((z x).2 i)) : ℂ)) μ) (j : ℕ) :
    ∃ B, 0 < B ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinRadialClassBesselProfile μ n c χ b η τ z g) j u‖ ≤
        B * u ^ (-σ) := by
  have h := artinRadialClassBesselProfile_log_smooth_bounded n hk χ he b η hc hσ hτ hg hb hη
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

end
end SimultaneousPrimitiveRoots

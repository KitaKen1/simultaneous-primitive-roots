module

public import SimultaneousPrimitiveRoots.ValuationShellIntegrability
public import SimultaneousPrimitiveRoots.ShiftedBesselProfiles

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology ContDiff Pointwise
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The dependent complex norm is u/rho(x). The other factor is integrated
against the actual given measure, rather than replaced by a constant mass. -/
def artinFinitePlaceBesselProfile (μ : Measure X) (c : ℝ) (ρ : X → ℝ)
    (f : X → ℂ) (u : ℝ) : ℂ :=
  ∫ x, artinBesselLocalProfile c (u / ρ x) * f x ∂μ

theorem artinFinitePlaceBesselProfile_eq_shifted (c : ℝ) {ρ : X → ℝ}
    (hρ : ∀ x, 0 < ρ x) (f : X → ℂ) :
    artinFinitePlaceBesselProfile μ c ρ f =
      artinShiftedBesselProfile μ c (fun x => Real.log (ρ x)) f := by
  funext u
  unfold artinFinitePlaceBesselProfile artinShiftedBesselProfile
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [Real.exp_neg, Real.exp_log (hρ x), div_eq_mul_inv])

omit [MeasurableSpace X] in
theorem artinShiftedBesselTail_log_radius (σ : ℝ) {ρ : X → ℝ}
    (hρ : ∀ x, 0 < ρ x) (f : X → ℂ) :
    artinShiftedBesselTail σ (fun x => Real.log (ρ x)) f =
      fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x := by
  funext x
  unfold artinShiftedBesselTail
  rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Real.rpow_def_of_pos (hρ x), mul_comm σ]

theorem artinFinitePlaceBesselProfile_log_smooth_bounded {c σ : ℝ}
    {ρ : X → ℝ} {f : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (hf : Integrable (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) μ) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinFinitePlaceBesselProfile μ c ρ f) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j
          (artinMellinLogPullback (artinFinitePlaceBesselProfile μ c ρ f) (σ : ℂ)) v‖ ≤ M := by
  rw [artinFinitePlaceBesselProfile_eq_shifted c hρ f]
  apply artinShiftedBesselProfile_log_smooth_bounded hc hσ (Real.measurable_log.comp hρm)
  change Integrable (artinShiftedBesselTail σ (fun x => Real.log (ρ x)) f) μ
  rwa [artinShiftedBesselTail_log_radius σ hρ f]

theorem artinFinitePlaceBesselProfile_logJet_power_bound {c σ : ℝ}
    {ρ : X → ℝ} {f : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (hf : Integrable (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) μ) (j : ℕ) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinLogProfileJet (artinFinitePlaceBesselProfile μ c ρ f) j u‖ ≤ M * u ^ (-σ) := by
  have h := artinFinitePlaceBesselProfile_log_smooth_bounded hc hσ hρm hρ hf
  exact artinLogProfileJet_bound_of_weighted h.1 h.2 j

theorem artinFinitePlaceBesselProfile_contDiffOn {c σ : ℝ}
    {ρ : X → ℝ} {f : X → ℂ} (hc : 0 < c) (hσ : -(5 / 6 : ℝ) < σ)
    (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (hf : Integrable (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) μ) :
    ContDiffOn ℝ ∞ (artinFinitePlaceBesselProfile μ c ρ f) (Ioi 0) :=
  artinProfile_contDiffOn_of_log (artinFinitePlaceBesselProfile_log_smooth_bounded hc hσ hρm hρ hf).1

section HaarShells

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    {ν : Measure G} [ν.IsMulLeftInvariant]

/-- A direct shell-to-profile bridge. Weighted tail integrability is derived
from the geometric shell estimate and actual Haar invariance. Identification
with the paper's local Whittaker factor, and its norm section, is separate. -/
theorem artinHaarValuationBesselProfile_log_smooth_bounded {f : G → ℂ}
    (ρ : G →* ℝ) (hρm : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (hf : AEStronglyMeasurable f ν) {π : G} {U T : Set G}
    (hUm : MeasurableSet U) (hUfin : ν U < ⊤)
    {Q δ σ C c : ℝ} (hQ : 1 < Q) (hσ : 0 < δ + σ)
    (hB : -(5 / 6 : ℝ) < σ) (hC : 0 ≤ C) (hc : 0 < c)
    (hπ : ρ π = Q ^ (-1 : ℝ)) (hU : ∀ u ∈ U, ρ u = 1)
    (hb : ∀ k x, x ∈ π ^ k • U → ‖f x‖ ≤ C * (ρ x) ^ δ)
    (hT : IntegrableOn (fun x => ((ρ x ^ σ : ℝ) : ℂ) * f x) T ν)
    (hs : Function.support f ⊆ T ∪ ⋃ k : ℕ, π ^ k • U) :
    ContDiff ℝ ∞ (artinMellinLogPullback (artinFinitePlaceBesselProfile ν c ρ f) (σ : ℂ)) ∧
      ∀ j : ℕ, ∃ M, 0 < M ∧ ∀ v,
        ‖iteratedDeriv j
          (artinMellinLogPullback (artinFinitePlaceBesselProfile ν c ρ f) (σ : ℂ)) v‖ ≤ M :=
  artinFinitePlaceBesselProfile_log_smooth_bounded hc hB hρm hρ
    (artinHaarValuationFactor_integrable ρ hρm hf hUm hUfin hQ hσ hC hπ hU hb hT hs)

end HaarShells
end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.GaussianLeftSpatialIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set
noncomputable section
open Classical

theorem negativeClosedStrip_realProd_preimage :
    Complex.measurableEquivRealProd.symm ⁻¹' negativeClosedStrip =
      Icc (-1 : ℝ) 0 ×ˢ (univ : Set ℝ) := by
  ext p
  simp [negativeClosedStrip, Complex.measurableEquivRealProd_symm_apply]

theorem integrable_negativeClosedStrip_realProd {f : ℂ → ℂ}
    (hf : IntegrableOn f negativeClosedStrip) :
    Integrable (fun p : ℝ × ℝ => f ((p.1 : ℂ) + p.2 * Complex.I))
      ((volume.restrict (Icc (-1 : ℝ) 0)).prod volume) := by
  have hh := (Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  rw [negativeClosedStrip_realProd_preimage] at hh
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ] at hh
  simpa only [Function.comp_def,
    Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I] using hh

theorem negativeClosedStrip_integral_norm_eq_iterated {f : ℂ → ℂ}
    (hf : IntegrableOn f negativeClosedStrip) :
    (∫ z : ℂ in negativeClosedStrip, ‖f z‖) =
      ∫ σ : ℝ in Icc (-1 : ℝ) 0, ∫ y : ℝ, ‖f ((σ : ℂ) + y * Complex.I)‖ := by
  have hh := Complex.volume_preserving_equiv_real_prod.symm.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding (fun z => ‖f z‖) negativeClosedStrip
  rw [negativeClosedStrip_realProd_preimage] at hh
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hh
  have hh' : (∫ p : ℝ × ℝ,
      ‖f ((p.1 : ℂ) + p.2 * Complex.I)‖
        ∂(volume.restrict (Icc (-1 : ℝ) 0)).prod volume) =
      ∫ z : ℂ in negativeClosedStrip, ‖f z‖ := by
    simpa only [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I] using hh
  rw [← hh', integral_prod _ (integrable_negativeClosedStrip_realProd hf).norm]

/-- Fubini and the first moment method choose one actual integrable vertical
line with norm integral at most the strip's spatial integral, avoiding any
countable set of forbidden real parts. -/
theorem exists_negative_line_integrable_norm_le {f : ℂ → ℂ}
    (hf : IntegrableOn f negativeClosedStrip) {Z : Set ℝ} (hZ : Z.Countable) :
    ∃ σ : ℝ, -1 ≤ σ ∧ σ ≤ 0 ∧ σ ∉ Z ∧
      Integrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I)) ∧
      (∫ y : ℝ, ‖f ((σ : ℂ) + y * Complex.I)‖) ≤
        ∫ z : ℂ in negativeClosedStrip, ‖f z‖ := by
  let μ : Measure ℝ := volume.restrict (Icc (-1 : ℝ) 0)
  have hμ : μ univ = 1 := by simp [μ, Real.volume_Icc]
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_iff.mpr hμ
  let g : ℝ → ℝ := fun σ => ∫ y : ℝ, ‖f ((σ : ℂ) + y * Complex.I)‖
  have hp := integrable_negativeClosedStrip_realProd hf
  have hg : Integrable g μ := hp.integral_norm_prod_left
  have hgood : ∀ᵐ σ ∂μ, σ ∈ Icc (-1 : ℝ) 0 ∧ σ ∉ Z ∧
      Integrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I)) := by
    have hz : ∀ᵐ σ ∂volume, σ ∉ Z := measure_eq_zero_iff_ae_notMem.mp (hZ.measure_zero volume)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc, hp.prod_right_ae,
      ae_mono Measure.restrict_le_self hz] with σ hs hi hz'
    exact ⟨hs, hz', hi⟩
  let N : Set ℝ := {σ | ¬ (σ ∈ Icc (-1 : ℝ) 0 ∧ σ ∉ Z ∧
    Integrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I)))}
  have hN : μ N = 0 := measure_eq_zero_iff_ae_notMem.mpr (by
    filter_upwards [hgood] with σ hs
    exact not_not.mpr hs)
  obtain ⟨σ, hσ, hh⟩ := exists_notMem_null_le_integral hg hN
  have hs : σ ∈ Icc (-1 : ℝ) 0 ∧ σ ∉ Z ∧
      Integrable (fun y : ℝ => f ((σ : ℂ) + y * Complex.I)) := not_not.mp hσ
  refine ⟨σ, hs.1.1, hs.1.2, hs.2.1, hs.2.2, ?_⟩
  rw [negativeClosedStrip_integral_norm_eq_iterated hf]
  exact hh

end
end SimultaneousPrimitiveRoots

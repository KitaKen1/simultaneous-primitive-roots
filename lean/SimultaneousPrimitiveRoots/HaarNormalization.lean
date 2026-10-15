module

public import SimultaneousPrimitiveRoots.HaarCutoffMass
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

theorem artinHaarNormalization_pos {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure] :
    0 < (Measure.haarScalarFactor ν μ : ℝ) :=
  NNReal.coe_pos.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure ν μ)

/-- The normalizing scalar is determined by the two actual Haar measures. -/
theorem artinHaarNormalization_measure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure] :
    ν = Measure.haarScalarFactor ν μ • μ :=
  Measure.isMulLeftInvariant_eq_smul ν μ

theorem artinFiniteSheetMass_smul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Set Ω) (a : NNReal) :
    artinFiniteSheetMass (a • μ) U = (a : ℝ) * artinFiniteSheetMass μ U := by
  change ((a : ENNReal) * μ U).toReal = (a : ℝ) * (μ U).toReal
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]

theorem artinFiniteHaarBesselSheetProfile_smul {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) (U : Set Ω) (c : Fin (n + 1) → ℝ)
    (a : NNReal) (u : ℝ) :
    artinFiniteHaarBesselSheetProfile (a • μ) U c u =
      (a : ℂ) * artinFiniteHaarBesselSheetProfile μ U c u := by
  rw [artinFiniteHaarBesselSheetProfile_factor, artinFiniteHaarBesselSheetProfile_factor,
    artinFiniteSheetMass_smul, Complex.ofReal_mul, mul_assoc]

theorem reflectionGammaQuotient_scale_C (a C A : ℝ) (r : ℕ) (z : ℂ) :
    reflectionGammaQuotient (a * C) A r z =
      (a : ℂ)⁻¹ * reflectionGammaQuotient C A r z := by
  simp only [reflectionGammaQuotient, Complex.ofReal_mul, mul_inv_rev]
  ring

theorem reflectionInverseMellinLine_scale_C (a C A : ℝ) (r : ℕ) (σ T : ℝ) :
    reflectionInverseMellinLine (a * C) A r σ T =
      (a : ℂ)⁻¹ * reflectionInverseMellinLine C A r σ T := by
  simp only [reflectionInverseMellinLine, reflectionInverseMellinIntegrand,
    reflectionGammaQuotient_scale_C]
  simp_rw [show ∀ z : ℂ, (T : ℂ) ^ z * ((a : ℂ)⁻¹ * reflectionGammaQuotient C A r z) =
    (a : ℂ)⁻¹ * ((T : ℂ) ^ z * reflectionGammaQuotient C A r z) by intro z; ring]
  rw [integral_const_mul]
  ring

theorem reflectionKernel_scale_C (a C A : ℝ) (r : ℕ) (T : ℝ) :
    reflectionKernel (a * C) A r T = (a : ℂ)⁻¹ * reflectionKernel C A r T :=
  reflectionInverseMellinLine_scale_C a C A r 0 T

/-- Scaling actual Haar mass scales V and C equally and leaves κV unchanged. -/
theorem reflectionKernel_profile_scale_cancel {a : ℝ} (ha : a ≠ 0)
    (C A : ℝ) (r : ℕ) (V : ℝ → ℂ) (u T : ℝ) :
    reflectionKernel (a * C) A r T * ((a : ℂ) * V (u * T)) =
      reflectionKernel C A r T * V (u * T) := by
  rw [reflectionKernel_scale_C]
  have h : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  field_simp

theorem reflectionKernel_profile_scale_integral {a : ℝ} (ha : a ≠ 0)
    (C A : ℝ) (r : ℕ) (V : ℝ → ℂ) (u : ℝ) :
    (∫ T, reflectionKernel (a * C) A r T * ((a : ℂ) * V (u * T))
      ∂artinPositiveMultiplicativeMeasure) =
    ∫ T, reflectionKernel C A r T * V (u * T) ∂artinPositiveMultiplicativeMeasure := by
  apply integral_congr_ae
  exact ae_of_all _ (reflectionKernel_profile_scale_cancel ha C A r V u)

theorem artinHaarNormalization_sheetMass {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure] (U : Set G) :
    artinFiniteSheetMass ν U =
      (Measure.haarScalarFactor ν μ : ℝ) * artinFiniteSheetMass μ U := by
  conv_lhs => rw [artinHaarNormalization_measure ν μ]
  exact artinFiniteSheetMass_smul μ U _

theorem artinHaarNormalization_profile {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure]
    {n : ℕ} (U : Set G) (c : Fin (n + 1) → ℝ) (u : ℝ) :
    artinFiniteHaarBesselSheetProfile ν U c u =
      (Measure.haarScalarFactor ν μ : ℂ) * artinFiniteHaarBesselSheetProfile μ U c u := by
  conv_lhs => rw [artinHaarNormalization_measure ν μ]
  exact artinFiniteHaarBesselSheetProfile_smul μ U c _ u

/-- Actual Haar normalization cancels pointwise, hence in the Gaussian integral. -/
theorem artinHaarNormalization_kernel_profile {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (ν μ : Measure G) [ν.IsHaarMeasure] [μ.IsHaarMeasure]
    {n : ℕ} (U : Set G) (c : Fin (n + 1) → ℝ) (A u T : ℝ) :
    reflectionKernel (artinFiniteSheetMass ν U * artinFiniteBesselSheetC c) A (n + 1) T *
      artinFiniteHaarBesselSheetProfile ν U c (u * T) =
    reflectionKernel (artinFiniteSheetMass μ U * artinFiniteBesselSheetC c) A (n + 1) T *
      artinFiniteHaarBesselSheetProfile μ U c (u * T) := by
  rw [artinHaarNormalization_sheetMass ν μ U, artinHaarNormalization_profile ν μ U c,
    mul_assoc]
  exact reflectionKernel_profile_scale_cancel (artinHaarNormalization_pos ν μ).ne'
    _ _ _ _ _ _

end
end SimultaneousPrimitiveRoots

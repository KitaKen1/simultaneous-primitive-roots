module

public import SimultaneousPrimitiveRoots.ComplexPlaceHaar
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.Topology.Algebra.Group.Units

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex NumberField NumberField.InfinitePlace
noncomputable section

variable {K : Type*} [Field K] {v : InfinitePlace K} (hv : v.IsComplex)

/-- The actual infinite-place completion, with its field multiplication and topology. -/
def artinComplexCompletionFieldEquiv : v.Completion ≃ₜ* ℂ where
  __ := (Completion.ringEquivComplexOfIsComplex hv).toMulEquiv
  continuous_toFun := (Completion.isometryEquivComplexOfIsComplex hv).continuous
  continuous_invFun := (Completion.isometryEquivComplexOfIsComplex hv).symm.continuous

/-- Lift the actual field isomorphism to the multiplicative local group. -/
def artinComplexCompletionUnitsEquiv : v.Completionˣ ≃ₜ* ℂˣ :=
  Units.mapContinuousMulEquiv (artinComplexCompletionFieldEquiv hv)

theorem artinComplexCompletionUnitsEquiv_val (z : v.Completionˣ) :
    (artinComplexCompletionUnitsEquiv hv z : ℂ) = Completion.extensionEmbedding v (z : v.Completion) :=
  rfl

theorem artinComplexCompletionUnitsEquiv_norm (z : v.Completionˣ) :
    ‖(artinComplexCompletionUnitsEquiv hv z : ℂ)‖ = ‖(z : v.Completion)‖ := by
  rw [artinComplexCompletionUnitsEquiv_val]
  have h := (Completion.isometry_extensionEmbedding v).dist_eq (z : v.Completion) 0
  simpa only [map_zero, dist_zero_right] using h

theorem artinComplexCompletionUnitsEquiv_norm_sq (z : v.Completionˣ) :
    ‖(artinComplexCompletionUnitsEquiv hv z : ℂ)‖ ^ 2 = ‖(z : v.Completion)‖ ^ 2 := by
  rw [artinComplexCompletionUnitsEquiv_norm]

instance artinInfiniteCompletionMeasurable : MeasurableSpace v.Completion := borel _

instance artinInfiniteCompletionBorel : BorelSpace v.Completion := ⟨rfl⟩

instance artinInfiniteCompletionUnitsBorel : BorelSpace v.Completionˣ where
  measurable_eq := by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace v.Completion) =
      borel v.Completionˣ
    rw [Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap,
      (BorelSpace.measurable_eq (α := v.Completion))]

include hv in
theorem artinComplexCompletionUnits_secondCountable : SecondCountableTopology v.Completionˣ :=
  (artinComplexCompletionUnitsEquiv hv).toHomeomorph.isEmbedding.secondCountableTopology

/-- Pull back the constructed complex Haar through the actual local-field isomorphism. -/
def artinComplexCompletionHaar : Measure v.Completionˣ :=
  Measure.map (artinComplexCompletionUnitsEquiv hv).symm artinComplexPlaceHaar

instance artinComplexCompletionHaar_isHaar : (artinComplexCompletionHaar hv).IsHaarMeasure := by
  unfold artinComplexCompletionHaar
  exact (artinComplexCompletionUnitsEquiv hv).symm.isHaarMeasure_map _

theorem artinComplexCompletionHaar_integral (f : v.Completionˣ → ℂ) :
    (∫ z, f z ∂artinComplexCompletionHaar hv) =
      ∫ z, f ((artinComplexCompletionUnitsEquiv hv).symm z) ∂artinComplexPlaceHaar :=
  integral_map_equiv (artinComplexCompletionUnitsEquiv hv).symm.toHomeomorph.toMeasurableEquiv f

theorem artinComplexCompletionHaar_map :
    Measure.map (artinComplexCompletionUnitsEquiv hv) (artinComplexCompletionHaar hv) =
      artinComplexPlaceHaar := by
  unfold artinComplexCompletionHaar
  rw [Measure.map_map (g := artinComplexCompletionUnitsEquiv hv)
    (f := (artinComplexCompletionUnitsEquiv hv).symm)
    (artinComplexCompletionUnitsEquiv hv).continuous.measurable
    (artinComplexCompletionUnitsEquiv hv).symm.continuous.measurable]
  simp only [Function.comp_def, ContinuousMulEquiv.apply_symm_apply]
  exact Measure.map_id

theorem artinComplexCompletionHaar_normalization (μ : Measure v.Completionˣ) [μ.IsHaarMeasure] :
    μ = Measure.haarScalarFactor μ (artinComplexCompletionHaar hv) •
      artinComplexCompletionHaar hv := by
  letI := artinComplexCompletionUnits_secondCountable hv
  exact artinHaarNormalization_measure μ (artinComplexCompletionHaar hv)

theorem artinComplexCompletionHaar_normalization_pos (μ : Measure v.Completionˣ)
    [μ.IsHaarMeasure] :
    0 < (Measure.haarScalarFactor μ (artinComplexCompletionHaar hv) : ℝ) :=
  artinHaarNormalization_pos μ (artinComplexCompletionHaar hv)

theorem artinComplexCompletionHaar_radial_integral (f : ℝ → ℂ) :
    (∫ z : v.Completionˣ, f (‖(z : v.Completion)‖ ^ 2) ∂artinComplexCompletionHaar hv) =
      ∫ t, f t ∂artinPositiveMultiplicativeMeasure := by
  rw [artinComplexCompletionHaar_integral]
  have hn : ∀ z : ℂˣ, ‖((artinComplexCompletionUnitsEquiv hv).symm z : v.Completion)‖ =
      ‖(z : ℂ)‖ := by
    intro z
    simpa using (artinComplexCompletionUnitsEquiv_norm hv
      ((artinComplexCompletionUnitsEquiv hv).symm z)).symm
  simp_rw [hn]
  rw [artinComplexPlaceHaar_radial_integral, ← artinPositiveMultiplicative_integral_exp]

theorem artinComplexCompletionHaar_radial_integrable {f : ℝ → ℂ}
    (hf : Integrable (fun x : ℝ => f (Real.exp x))) :
    Integrable (fun z : v.Completionˣ => f (‖(z : v.Completion)‖ ^ 2))
      (artinComplexCompletionHaar hv) := by
  unfold artinComplexCompletionHaar
  apply (artinComplexCompletionUnitsEquiv hv).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun z : ℂˣ => f
    (‖((artinComplexCompletionUnitsEquiv hv).symm z : v.Completion)‖ ^ 2)) artinComplexPlaceHaar
  have hn : ∀ z : ℂˣ, ‖((artinComplexCompletionUnitsEquiv hv).symm z : v.Completion)‖ =
      ‖(z : ℂ)‖ := by
    intro z
    simpa using (artinComplexCompletionUnitsEquiv_norm hv
      ((artinComplexCompletionUnitsEquiv hv).symm z)).symm
  simpa only [Function.comp_def, hn] using artinComplexPlaceHaar_radial_integrable hf

theorem artinComplexCompletionHaar_mellin (μ : Measure v.Completionˣ) [μ.IsHaarMeasure]
    (f : ℝ → ℂ) (s : ℂ) :
    (∫ z : v.Completionˣ, ((‖(z : v.Completion)‖ ^ 2 : ℝ) : ℂ) ^ s *
      f (‖(z : v.Completion)‖ ^ 2) ∂μ) =
      (Measure.haarScalarFactor μ (artinComplexCompletionHaar hv) : ℂ) * mellin f s := by
  conv_lhs => rw [artinComplexCompletionHaar_normalization hv μ]
  rw [integral_smul_nnreal_measure, artinComplexCompletionHaar_radial_integral hv
    (fun t : ℝ => (t : ℂ) ^ s * f t),
    ← artinMellin_eq_multiplicative]
  simp [NNReal.smul_def, Complex.real_smul]

include hv in
theorem artinComplexCompletionHaar_bessel_integrable (μ : Measure v.Completionˣ)
    [μ.IsHaarMeasure] {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun z : v.Completionˣ => ((‖(z : v.Completion)‖ ^ 2 : ℝ) : ℂ) ^ s *
      artinBesselLocalProfile c (‖(z : v.Completion)‖ ^ 2)) μ := by
  rw [artinComplexCompletionHaar_normalization hv μ]
  apply Integrable.smul_measure_nnreal
  apply artinComplexCompletionHaar_radial_integrable hv
    (f := fun t : ℝ => (t : ℂ) ^ s * artinBesselLocalProfile c t)
  exact (artinPositiveMultiplicative_integrable_exp_iff _).mp
    ((artinMellin_convergent_iff_multiplicative _ _).mp
      (artinBesselLocalProfile_mellin_convergent hc hs))

/-- The K integral and Gamma formula now live on the actual complex-place completion. -/
theorem artinComplexCompletionHaar_bessel_mellin (μ : Measure v.Completionˣ)
    [μ.IsHaarMeasure] {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    (∫ z : v.Completionˣ, ((‖(z : v.Completion)‖ ^ 2 : ℝ) : ℂ) ^ s *
      artinBesselLocalProfile c (‖(z : v.Completion)‖ ^ 2) ∂μ) =
      (Measure.haarScalarFactor μ (artinComplexCompletionHaar hv) : ℂ) *
        (((2 / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ s *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) := by
  rw [artinComplexCompletionHaar_mellin, artinBesselLocalProfile_mellin_gammaForm hc hs]

end
end SimultaneousPrimitiveRoots

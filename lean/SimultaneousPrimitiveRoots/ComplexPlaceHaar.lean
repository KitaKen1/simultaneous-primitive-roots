module

public import SimultaneousPrimitiveRoots.ComplexPlaceCoordinates
public import SimultaneousPrimitiveRoots.HaarNormalization
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex TopologicalSpace
noncomputable section

instance artinComplexUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

instance artinComplexUnitsBorel : BorelSpace ℂˣ where
  measurable_eq := by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace ℂ) = borel ℂˣ
    rw [Units.isEmbedding_val₀.isInducing.eq_induced, borel_comap,
      (BorelSpace.measurable_eq (α := ℂ))]

/-- The inherited Lebesgue measure on the logarithmic radial group. -/
instance artinLogRadialMeasureSpace : MeasureSpace (Multiplicative ℝ) :=
  inferInstanceAs (MeasureSpace ℝ)

instance artinLogRadialBorel : BorelSpace (Multiplicative ℝ) :=
  inferInstanceAs (BorelSpace ℝ)

instance artinLogRadialHaar : (volume : Measure (Multiplicative ℝ)).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  toIsOpenPosMeasure := inferInstanceAs ((volume : Measure ℝ).IsOpenPosMeasure)
  map_mul_left_eq_self g := by
    change Measure.map (fun x : ℝ => Multiplicative.toAdd g + x) volume = volume
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := (volume : Measure ℝ)) _

/-- An actual Haar measure on Circle with total angular mass one. -/
def artinCircleHaar : Measure Circle := Measure.haarMeasure (⊤ : PositiveCompacts Circle)

instance artinCircleHaar_isHaar : artinCircleHaar.IsHaarMeasure := by
  unfold artinCircleHaar
  infer_instance

theorem artinCircleHaar_univ : artinCircleHaar univ = 1 := by
  change Measure.haarMeasure (⊤ : PositiveCompacts Circle) _ = 1
  simpa only [PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts Circle)))

instance artinCircleHaar_probability : IsProbabilityMeasure artinCircleHaar :=
  ⟨artinCircleHaar_univ⟩

theorem artinCircleHaar_unique (η : Measure Circle) [η.IsHaarMeasure]
    [IsProbabilityMeasure η] : η = artinCircleHaar :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure η artinCircleHaar

/-- Multiplicative Haar on actual complex units, constructed from log(|z|²) and angle. -/
def artinComplexPlaceHaar : Measure ℂˣ :=
  Measure.map artinComplexPlaceCoordinates
    ((volume : Measure (Multiplicative ℝ)).prod artinCircleHaar)

instance artinComplexPlaceHaar_isHaar : artinComplexPlaceHaar.IsHaarMeasure := by
  unfold artinComplexPlaceHaar
  infer_instance

theorem artinComplexPlaceHaar_normalization (μ : Measure ℂˣ) [μ.IsHaarMeasure] :
    μ = Measure.haarScalarFactor μ artinComplexPlaceHaar • artinComplexPlaceHaar :=
  artinHaarNormalization_measure μ artinComplexPlaceHaar

theorem artinComplexPlaceHaar_normalization_pos (μ : Measure ℂˣ) [μ.IsHaarMeasure] :
    0 < (Measure.haarScalarFactor μ artinComplexPlaceHaar : ℝ) :=
  artinHaarNormalization_pos μ artinComplexPlaceHaar

/-- Change of variables for the actual complex group and its constructed Haar measure. -/
theorem artinComplexPlaceHaar_integral (f : ℂˣ → ℂ) :
    (∫ z, f z ∂artinComplexPlaceHaar) =
    ∫ p, f (artinComplexPolarUnit p)
      ∂((volume : Measure (Multiplicative ℝ)).prod artinCircleHaar) := by
  exact integral_map_equiv artinComplexPlaceCoordinates.toHomeomorph.toMeasurableEquiv f

/-- Any actual complex Haar differs by one positive scalar, not a polar Jacobian computation. -/
theorem artinComplexPlaceHaar_integral_normalized (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    (f : ℂˣ → ℂ) :
    (∫ z, f z ∂μ) = (Measure.haarScalarFactor μ artinComplexPlaceHaar : ℂ) *
      ∫ p, f (artinComplexPolarUnit p)
        ∂((volume : Measure (Multiplicative ℝ)).prod artinCircleHaar) := by
  conv_lhs => rw [artinComplexPlaceHaar_normalization μ]
  rw [integral_smul_nnreal_measure, artinComplexPlaceHaar_integral f]
  simp [NNReal.smul_def, Complex.real_smul]

theorem artinComplexPlaceHaar_radial_integral (f : ℝ → ℂ) :
    (∫ z : ℂˣ, f (‖(z : ℂ)‖ ^ 2) ∂artinComplexPlaceHaar) =
      ∫ x : ℝ, f (Real.exp x) := by
  rw [artinComplexPlaceHaar_integral]
  simp_rw [artinComplexPolarUnit_norm_sq]
  rw [integral_fun_fst (μ := (volume : Measure (Multiplicative ℝ)))
    (ν := artinCircleHaar) (fun x : Multiplicative ℝ => f (Real.exp (Multiplicative.toAdd x)))]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rfl

theorem artinComplexPlaceHaar_radial_integrable {f : ℝ → ℂ}
    (hf : Integrable (fun x : ℝ => f (Real.exp x))) :
    Integrable (fun z : ℂˣ => f (‖(z : ℂ)‖ ^ 2)) artinComplexPlaceHaar := by
  unfold artinComplexPlaceHaar
  apply artinComplexPlaceCoordinates.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun p => f (‖(artinComplexPolarUnit p : ℂ)‖ ^ 2)) _
  simp_rw [artinComplexPolarUnit_norm_sq]
  exact (show Integrable (fun x : Multiplicative ℝ => f (Real.exp (Multiplicative.toAdd x)))
    volume from hf).comp_fst artinCircleHaar

theorem artinComplexPlaceHaar_radial_integrable_normalized (μ : Measure ℂˣ)
    [μ.IsHaarMeasure] {f : ℝ → ℂ} (hf : Integrable (fun x : ℝ => f (Real.exp x))) :
    Integrable (fun z : ℂˣ => f (‖(z : ℂ)‖ ^ 2)) μ := by
  rw [artinComplexPlaceHaar_normalization μ]
  exact (artinComplexPlaceHaar_radial_integrable hf).smul_measure_nnreal

/-- Exact dt/t formula for any actual complex multiplicative Haar, up to its positive scalar. -/
theorem artinComplexPlaceHaar_radial_multiplicative (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    (f : ℝ → ℂ) :
    (∫ z : ℂˣ, f (‖(z : ℂ)‖ ^ 2) ∂μ) =
      (Measure.haarScalarFactor μ artinComplexPlaceHaar : ℂ) *
        ∫ t, f t ∂artinPositiveMultiplicativeMeasure := by
  conv_lhs => rw [artinComplexPlaceHaar_normalization μ]
  rw [integral_smul_nnreal_measure, artinComplexPlaceHaar_radial_integral,
    ← artinPositiveMultiplicative_integral_exp]
  simp [NNReal.smul_def, Complex.real_smul]

theorem artinComplexPlaceHaar_mellin_integrable (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    Integrable (fun z : ℂˣ => ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * f (‖(z : ℂ)‖ ^ 2)) μ := by
  apply artinComplexPlaceHaar_radial_integrable_normalized μ
    (f := fun t : ℝ => (t : ℂ) ^ s * f t)
  exact (artinPositiveMultiplicative_integrable_exp_iff _).mp
    ((artinMellin_convergent_iff_multiplicative f s).mp hf)

theorem artinComplexPlaceHaar_mellin (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    (f : ℝ → ℂ) (s : ℂ) :
    (∫ z : ℂˣ, ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * f (‖(z : ℂ)‖ ^ 2) ∂μ) =
      (Measure.haarScalarFactor μ artinComplexPlaceHaar : ℂ) * mellin f s := by
  rw [artinComplexPlaceHaar_radial_multiplicative μ (fun t : ℝ => (t : ℂ) ^ s * f t),
    ← artinMellin_eq_multiplicative]

theorem artinComplexPlaceHaar_bessel_integrable (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun z : ℂˣ => ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s *
      artinBesselLocalProfile c (‖(z : ℂ)‖ ^ 2)) μ :=
  artinComplexPlaceHaar_mellin_integrable μ (artinBesselLocalProfile_mellin_convergent hc hs)

/-- The actual local K integral on complex units has the required Gamma normalization. -/
theorem artinComplexPlaceHaar_bessel_mellin (μ : Measure ℂˣ) [μ.IsHaarMeasure]
    {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    (∫ z : ℂˣ, ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s *
      artinBesselLocalProfile c (‖(z : ℂ)‖ ^ 2) ∂μ) =
      (Measure.haarScalarFactor μ artinComplexPlaceHaar : ℂ) *
        (((2 / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ s *
          (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6))) := by
  rw [artinComplexPlaceHaar_mellin, artinBesselLocalProfile_mellin_gammaForm hc hs]

end
end SimultaneousPrimitiveRoots

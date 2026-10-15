module

public import SimultaneousPrimitiveRoots.ComplexNormKernelCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

instance artinFreeLogMeasureSpace (n : ℕ) : MeasureSpace (Multiplicative (Fin n → ℝ)) :=
  inferInstanceAs (MeasureSpace (Fin n → ℝ))

instance artinFreeLogBorel (n : ℕ) : BorelSpace (Multiplicative (Fin n → ℝ)) :=
  inferInstanceAs (BorelSpace (Fin n → ℝ))

instance artinFreeLogHaar (n : ℕ) :
    (volume : Measure (Multiplicative (Fin n → ℝ))).IsHaarMeasure where
  toIsFiniteMeasureOnCompacts :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure (Fin n → ℝ)))
  toIsOpenPosMeasure := inferInstanceAs ((volume : Measure (Fin n → ℝ)).IsOpenPosMeasure)
  map_mul_left_eq_self g := by
    change Measure.map (fun x : Fin n → ℝ => Multiplicative.toAdd g + x) volume = volume
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self
      (μ := (volume : Measure (Fin n → ℝ))) _

instance artinComplexNormKernelLocallyCompact (n : ℕ) :
    LocallyCompactSpace (artinComplexNormKernel n) :=
  (artinComplexNormKernel_isClosed n).locallyCompactSpace

instance artinComplexNormKernelSecondCountable (n : ℕ) :
    SecondCountableTopology (artinComplexNormKernel n) :=
  (artinComplexNormKernel_isClosed n).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

/-- Product angular Haar, with actual total mass one. -/
def artinComplexAnglesHaar (n : ℕ) : Measure (Fin (n + 1) → Circle) :=
  Measure.pi (fun _ => artinCircleHaar)

instance artinComplexAnglesHaar_isHaar (n : ℕ) :
    (artinComplexAnglesHaar n).IsHaarMeasure := by
  unfold artinComplexAnglesHaar
  infer_instance

instance artinComplexAnglesHaar_probability (n : ℕ) :
    IsProbabilityMeasure (artinComplexAnglesHaar n) := by
  unfold artinComplexAnglesHaar
  infer_instance

/-- Actual Haar on the product-norm-one subgroup, from r-1 log radii and r angles. -/
def artinComplexNormKernelHaar (n : ℕ) : Measure (artinComplexNormKernel n) :=
  Measure.map (artinComplexNormKernelCoordinates n)
    ((volume : Measure (Multiplicative (Fin n → ℝ))).prod (artinComplexAnglesHaar n))

instance artinComplexNormKernelHaar_isHaar (n : ℕ) :
    (artinComplexNormKernelHaar n).IsHaarMeasure := by
  unfold artinComplexNormKernelHaar
  exact (artinComplexNormKernelCoordinates n).isHaarMeasure_map
    ((volume : Measure (Multiplicative (Fin n → ℝ))).prod (artinComplexAnglesHaar n))

theorem artinComplexNormKernelHaar_normalization {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure] :
    μ = Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) •
      artinComplexNormKernelHaar n :=
  artinHaarNormalization_measure μ (artinComplexNormKernelHaar n)

theorem artinComplexNormKernelHaar_normalization_pos {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure] :
    0 < (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℝ) :=
  artinHaarNormalization_pos μ (artinComplexNormKernelHaar n)

theorem artinComplexNormKernelHaar_integral (n : ℕ) (f : artinComplexNormKernel n → ℂ) :
    (∫ z, f z ∂artinComplexNormKernelHaar n) =
      ∫ p, f (artinComplexNormKernelCoordinates n p)
        ∂((volume : Measure (Multiplicative (Fin n → ℝ))).prod (artinComplexAnglesHaar n)) :=
  integral_map_equiv (artinComplexNormKernelCoordinates n).toHomeomorph.toMeasurableEquiv f

/-- Transport Haar on X_1 by the actual multiplicative section; never restrict ambient Haar. -/
def artinComplexNormSheetTransport (n : ℕ) (u : ℝ) (z : artinComplexNormKernel n) :
    Fin (n + 1) → ℂˣ := artinComplexNormSection n u * z.1

theorem artinComplexNormSheetTransport_isClosedEmbedding (n : ℕ) (u : ℝ) :
    Topology.IsClosedEmbedding (artinComplexNormSheetTransport n u) :=
  (Homeomorph.mulLeft (artinComplexNormSection n u)).isClosedEmbedding.comp
    (artinComplexNormKernel_isClosed n).isClosedEmbedding_subtypeVal

theorem artinComplexNormSheetTransport_product (n : ℕ) {u : ℝ} (hu : 0 < u)
    (z : artinComplexNormKernel n) :
    (∏ i, ‖(artinComplexNormSheetTransport n u z i : ℂ)‖ ^ 2) = u := by
  simp only [artinComplexNormSheetTransport, Pi.mul_apply, Units.val_mul,
    norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [artinComplexNormSection_product n hu, z.2, mul_one]

/-- A genuine transported norm-sheet measure, supported on product norm u when u>0. -/
def artinComplexNormSheetMeasure {n : ℕ} (μ : Measure (artinComplexNormKernel n))
    (u : ℝ) : Measure (Fin (n + 1) → ℂˣ) :=
  Measure.map (artinComplexNormSheetTransport n u) μ

theorem artinComplexNormSheetMeasure_supported {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) {u : ℝ} (hu : 0 < u) :
    ∀ᵐ z ∂artinComplexNormSheetMeasure μ u, (∏ i, ‖(z i : ℂ)‖ ^ 2) = u := by
  have hp : Continuous (fun z : Fin (n + 1) → ℂˣ => ∏ i, ‖(z i : ℂ)‖ ^ 2) :=
    continuous_finsetProd _ (fun i _ =>
      ((Units.continuous_val.comp (continuous_apply i)).norm.pow 2))
  apply (ae_map_iff
    (artinComplexNormSheetTransport_isClosedEmbedding n u).continuous.measurable.aemeasurable
    ((isClosed_eq hp continuous_const).measurableSet)).mpr
  exact Filter.Eventually.of_forall (artinComplexNormSheetTransport_product n hu)

theorem artinComplexNormSheetMeasure_transport_mul {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    artinComplexNormSheetMeasure μ (v * u) =
      Measure.map (fun z => artinComplexNormSection n v * z)
        (artinComplexNormSheetMeasure μ u) := by
  have hm : Measurable (fun z : Fin (n + 1) → ℂˣ => artinComplexNormSection n v * z) :=
    (continuous_const.mul continuous_id).measurable
  rw [artinComplexNormSheetMeasure, artinComplexNormSheetMeasure,
    Measure.map_map hm
      (artinComplexNormSheetTransport_isClosedEmbedding n u).continuous.measurable]
  congr 1
  funext z
  simp only [Function.comp_apply, artinComplexNormSheetTransport,
    artinComplexNormSection_mul n hv hu, mul_assoc]

theorem artinComplexNormSheetMeasure_integral {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) (u : ℝ) (f : (Fin (n + 1) → ℂˣ) → ℂ) :
    (∫ z, f z ∂artinComplexNormSheetMeasure μ u) =
      ∫ z, f (artinComplexNormSheetTransport n u z) ∂μ :=
  (artinComplexNormSheetTransport_isClosedEmbedding n u).integral_map f

/-- Normalization is one positive scalar for every transported fiber, independent of u. -/
theorem artinComplexNormSheetMeasure_integral_normalized {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure] (u : ℝ)
    (f : (Fin (n + 1) → ℂˣ) → ℂ) :
    (∫ z, f z ∂artinComplexNormSheetMeasure μ u) =
      (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℂ) *
        ∫ p, f (artinComplexNormPoint n (Real.log u) p)
          ∂((volume : Measure (Multiplicative (Fin n → ℝ))).prod (artinComplexAnglesHaar n)) := by
  rw [artinComplexNormSheetMeasure_integral]
  conv_lhs => rw [artinComplexNormKernelHaar_normalization μ]
  rw [integral_smul_nnreal_measure, artinComplexNormKernelHaar_integral]
  simp_rw [artinComplexNormSheetTransport, ← artinComplexNormPoint_transport]
  simp only [NNReal.smul_def, Complex.real_smul]

end
end SimultaneousPrimitiveRoots

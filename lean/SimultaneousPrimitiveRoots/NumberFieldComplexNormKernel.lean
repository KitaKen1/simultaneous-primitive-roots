module

public import SimultaneousPrimitiveRoots.NumberFieldComplexProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField NumberField.InfinitePlace MeasureTheory Set Topology
open scoped Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev ArtinNumberFieldFiniteComplexGroup :=
  ArtinNumberFieldFiniteUnits K × ArtinNumberFieldComplexUnits K

def artinNumberFieldFiniteComplexNorm :
    ArtinNumberFieldFiniteComplexGroup K →* Multiplicative ℝ :=
  (artinNumberFieldFiniteLogNorm K).comp (MonoidHom.fst _ _) *
    (artinNumberFieldComplexLogNorm K).comp (MonoidHom.snd _ _)

def artinNumberFieldFiniteComplexNormKernel : Subgroup (ArtinNumberFieldFiniteComplexGroup K) :=
  (artinNumberFieldFiniteComplexNorm K).ker

theorem artinNumberFieldFiniteComplexNorm_continuous :
    Continuous (artinNumberFieldFiniteComplexNorm K) :=
  ((artinNumberFieldFiniteLogNorm_continuous K).comp continuous_fst).mul
    ((artinNumberFieldComplexLogNorm_continuous K).comp continuous_snd)

theorem artinNumberFieldFiniteComplexNorm_exp (p : ArtinNumberFieldFiniteComplexGroup K) :
    Real.exp (Multiplicative.toAdd (artinNumberFieldFiniteComplexNorm K p)) =
      Real.exp (Multiplicative.toAdd (artinNumberFieldFiniteLogNorm K p.1)) *
        ∏ v : ArtinNumberFieldComplexPlaces K, ‖(p.2 v : v.1.Completion)‖ ^ 2 := by
  change Real.exp (Multiplicative.toAdd (artinNumberFieldFiniteLogNorm K p.1) +
    Multiplicative.toAdd (artinNumberFieldComplexLogNorm K p.2)) = _
  rw [Real.exp_add, artinNumberFieldComplexLogNorm_exp]

theorem artinNumberFieldFiniteComplexNormKernel_isClosed :
    IsClosed (artinNumberFieldFiniteComplexNormKernel K : Set (ArtinNumberFieldFiniteComplexGroup K)) :=
  isClosed_eq (artinNumberFieldFiniteComplexNorm_continuous K) continuous_const

instance artinNumberFieldFiniteComplexNormKernel_locallyCompact :
    LocallyCompactSpace (artinNumberFieldFiniteComplexNormKernel K) :=
  (artinNumberFieldFiniteComplexNormKernel_isClosed K).locallyCompactSpace

theorem artinNumberFieldFiniteComplexNormKernel_secondCountable :
    SecondCountableTopology (artinNumberFieldFiniteComplexNormKernel K) := inferInstance

theorem artinNumberFieldFiniteComplexNormKernelHaar_exists :
    ∃ μ : Measure (artinNumberFieldFiniteComplexNormKernel K), μ.IsHaarMeasure :=
  ⟨Measure.haar, inferInstance⟩

def artinNumberFieldFiniteComplexUnitsEquiv (hr : 0 < nrComplexPlaces K) :
    ArtinNumberFieldFiniteComplexGroup K ≃ₜ*
      (ArtinNumberFieldFiniteUnits K × (Fin (nrComplexPlaces K - 1 + 1) → ℂˣ)) where
  __ := (MulEquiv.refl (ArtinNumberFieldFiniteUnits K)).prodCongr
    (artinNumberFieldComplexUnitsEquiv K hr).toMulEquiv
  continuous_toFun := continuous_fst.prodMk
    ((artinNumberFieldComplexUnitsEquiv K hr).continuous.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    ((artinNumberFieldComplexUnitsEquiv K hr).symm.continuous.comp continuous_snd)

theorem artinNumberFieldFiniteComplexUnitsEquiv_norm (hr : 0 < nrComplexPlaces K)
    (p : ArtinNumberFieldFiniteComplexGroup K) :
    artinFiniteComplexNorm (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1)
      (artinNumberFieldFiniteComplexUnitsEquiv K hr p) = artinNumberFieldFiniteComplexNorm K p := by
  change artinNumberFieldFiniteLogNorm K p.1 *
    artinComplexTotalLogNorm (nrComplexPlaces K - 1) (artinNumberFieldComplexUnitsEquiv K hr p.2) =
    artinNumberFieldFiniteLogNorm K p.1 * artinNumberFieldComplexLogNorm K p.2
  rw [artinNumberFieldComplexUnitsEquiv_logNorm]

/-- The actual norm-one group, retaining all completions, is isomorphic to the checked model. -/
def artinNumberFieldFiniteComplexNormKernelEquiv (hr : 0 < nrComplexPlaces K) :
    artinNumberFieldFiniteComplexNormKernel K ≃ₜ*
      artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1) := by
  let e := artinNumberFieldFiniteComplexUnitsEquiv K hr
  have hf (z : artinNumberFieldFiniteComplexNormKernel K) :
      e z.1 ∈ artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1) := by
    change artinFiniteComplexNorm _ _ (e z.1) = 1
    rw [artinNumberFieldFiniteComplexUnitsEquiv_norm]
    exact z.2
  have hi (z : artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1)) :
      e.symm z.1 ∈ artinNumberFieldFiniteComplexNormKernel K := by
    change artinNumberFieldFiniteComplexNorm K (e.symm z.1) = 1
    rw [← artinNumberFieldFiniteComplexUnitsEquiv_norm K hr]
    change artinFiniteComplexNorm _ _ (e (e.symm z.1)) = 1
    rw [e.apply_symm_apply]
    exact z.2
  refine { toFun := fun z => ⟨e z.1, hf z⟩
           invFun := fun z => ⟨e.symm z.1, hi z⟩
           left_inv := ?_, right_inv := ?_, map_mul' := ?_
           continuous_toFun := ?_, continuous_invFun := ?_ }
  · intro z; apply Subtype.ext; exact e.symm_apply_apply z.1
  · intro z; apply Subtype.ext; exact e.apply_symm_apply z.1
  · intro z w; apply Subtype.ext; exact e.map_mul z.1 w.1
  · exact (e.continuous.comp continuous_subtype_val).subtype_mk _
  · exact (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem artinNumberFieldFiniteComplexNormKernelEquiv_finite (hr : 0 < nrComplexPlaces K)
    (z : artinNumberFieldFiniteComplexNormKernel K) :
    (artinNumberFieldFiniteComplexNormKernelEquiv K hr z).1.1 = z.1.1 := rfl

def artinNumberFieldComplexKernelModelHaar (hr : 0 < nrComplexPlaces K)
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) :
    Measure (artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1)) :=
  Measure.map (artinNumberFieldFiniteComplexNormKernelEquiv K hr) μ

instance artinNumberFieldComplexKernelModelHaar_isHaar (hr : 0 < nrComplexPlaces K)
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) [μ.IsHaarMeasure] :
    (artinNumberFieldComplexKernelModelHaar K hr μ).IsHaarMeasure :=
  (artinNumberFieldFiniteComplexNormKernelEquiv K hr).isHaarMeasure_map μ

theorem artinNumberFieldComplexKernelModelHaar_integral (hr : 0 < nrComplexPlaces K)
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K))
    (f : artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K)
      (nrComplexPlaces K - 1) → ℂ) :
    (∫ z, f z ∂artinNumberFieldComplexKernelModelHaar K hr μ) =
      ∫ z, f (artinNumberFieldFiniteComplexNormKernelEquiv K hr z) ∂μ :=
  integral_map_equiv (artinNumberFieldFiniteComplexNormKernelEquiv K hr).toHomeomorph.toMeasurableEquiv f

end
end SimultaneousPrimitiveRoots

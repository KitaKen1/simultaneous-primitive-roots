module

public import SimultaneousPrimitiveRoots.FiniteNormCutoffEmbedding
public import SimultaneousPrimitiveRoots.HaarNormalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- Actual finite-cutoff Haar, obtained from the finite ambient Haar by open inclusion. -/
def artinFiniteUnitCutoffHaar (ν : Measure G) (U : Subgroup G) : Measure U :=
  ν.comap (Subtype.val : U → G)

theorem artinFiniteUnitCutoffHaar_isHaar (ν : Measure G) [ν.IsHaarMeasure]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) :
    (artinFiniteUnitCutoffHaar ν U).IsHaarMeasure := by
  have hf : Topology.IsOpenEmbedding (U.subtype : U → G) := hUo.isOpenEmbedding_subtypeVal
  exact Measure.IsHaarMeasure.comap (f := U.subtype) (mH := inferInstance) ν hf

theorem artinFiniteUnitCutoffHaar_mass (ν : Measure G) (U : Subgroup G)
    (hUo : IsOpen (U : Set G)) : artinFiniteUnitCutoffHaar ν U Set.univ = ν U := by
  have hf : Topology.IsOpenEmbedding (Subtype.val : U → G) := hUo.isOpenEmbedding_subtypeVal
  simpa [artinFiniteUnitCutoffHaar] using hf.measurableEmbedding.comap_apply ν Set.univ

theorem artinFiniteUnitCutoffHaar_finite (ν : Measure G) [ν.IsHaarMeasure]
    (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    IsFiniteMeasure (artinFiniteUnitCutoffHaar ν U) := by
  constructor
  rw [artinFiniteUnitCutoffHaar_mass ν U hUo]
  exact hUc.measure_lt_top

instance artinFiniteCutoffSecondCountable [SecondCountableTopology G] (U : Subgroup G) :
    SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology

def artinFiniteNormCutoffModelHaar (ν : Measure G) (U : Subgroup G) (n : ℕ) :
    Measure (U × artinComplexNormKernel n) :=
  (artinFiniteUnitCutoffHaar ν U).prod (artinComplexNormKernelHaar n)

theorem artinFiniteNormCutoffModelHaar_isHaar [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) [ν.IsHaarMeasure]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) (n : ℕ) :
    (artinFiniteNormCutoffModelHaar ν U n).IsHaarMeasure := by
  letI : LocallyCompactSpace U := hUo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI := artinFiniteUnitCutoffHaar_isHaar ν U hUo
  unfold artinFiniteNormCutoffModelHaar
  infer_instance

variable (χ : G →* Multiplicative ℝ) (U : Subgroup G) (n : ℕ)
  (hU : ∀ g ∈ U, χ g = 1)

theorem artinFiniteNormCutoffHaar_isHaar
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (hUo : IsOpen (U : Set G)) :
    (μ.comap (artinFiniteNormCutoffEmbedding χ U n hU)).IsHaarMeasure :=
  Measure.IsHaarMeasure.comap (mH := inferInstance) μ (artinFiniteNormCutoffEmbedding_isOpenEmbedding χ U n hU hUo)

/-- The positive factor is determined by the actual full-kernel Haar and finite Haar. -/
def artinFiniteNormCutoffHaarFactor [LocallyCompactSpace G] [SecondCountableTopology G]
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUo : IsOpen (U : Set G)) : NNReal := by
  letI := artinFiniteNormCutoffHaar_isHaar χ U n hU μ hUo
  letI := artinFiniteNormCutoffModelHaar_isHaar ν U hUo n
  exact Measure.haarScalarFactor (μ.comap (artinFiniteNormCutoffEmbedding χ U n hU))
    (artinFiniteNormCutoffModelHaar ν U n)

theorem artinFiniteNormCutoffHaarFactor_pos [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure] (hUo : IsOpen (U : Set G)) :
    0 < (artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℝ) := by
  letI := artinFiniteNormCutoffHaar_isHaar χ U n hU μ hUo
  letI := artinFiniteNormCutoffModelHaar_isHaar ν U hUo n
  exact artinHaarNormalization_pos _ _

theorem artinFiniteNormCutoffHaar_normalization [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure] (hUo : IsOpen (U : Set G)) :
    μ.comap (artinFiniteNormCutoffEmbedding χ U n hU) =
      artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo •
        artinFiniteNormCutoffModelHaar ν U n := by
  letI : LocallyCompactSpace U := hUo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI := artinFiniteNormCutoffHaar_isHaar χ U n hU μ hUo
  letI := artinFiniteNormCutoffModelHaar_isHaar ν U hUo n
  exact artinHaarNormalization_measure _ _

/-- Restricting full-kernel Haar to the open cutoff is exactly the embedded pullback. -/
theorem artinFiniteNormCutoffHaar_map_comap
    (μ : Measure (artinFiniteComplexNormKernel χ n)) (hUo : IsOpen (U : Set G)) :
    Measure.map (artinFiniteNormCutoffEmbedding χ U n hU)
      (μ.comap (artinFiniteNormCutoffEmbedding χ U n hU)) =
        μ.restrict {z | z.1.1 ∈ U} := by
  rw [(artinFiniteNormCutoffEmbedding_isOpenEmbedding χ U n hU hUo).measurableEmbedding.map_comap,
    artinFiniteNormCutoffEmbedding_range]

theorem artinFiniteNormCutoffHaar_integral [LocallyCompactSpace G]
    [SecondCountableTopology G]
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure] (hUo : IsOpen (U : Set G))
    (f : artinFiniteComplexNormKernel χ n → ℂ) :
    (∫ z in {z | z.1.1 ∈ U}, f z ∂μ) =
      (artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℂ) *
        ∫ p, f (artinFiniteNormCutoffEmbedding χ U n hU p)
          ∂artinFiniteNormCutoffModelHaar ν U n := by
  rw [← artinFiniteNormCutoffHaar_map_comap χ U n hU μ hUo,
    (artinFiniteNormCutoffEmbedding_isOpenEmbedding χ U n hU hUo).measurableEmbedding.integral_map]
  rw [artinFiniteNormCutoffHaar_normalization χ U n hU μ ν hUo,
    integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, Complex.real_smul]

end
end SimultaneousPrimitiveRoots

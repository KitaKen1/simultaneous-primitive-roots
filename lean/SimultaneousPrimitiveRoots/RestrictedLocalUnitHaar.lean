module

public import SimultaneousPrimitiveRoots.RestrictedLocalLogNorm

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Topology
noncomputable section

variable {ι : Type*} (F : ι → Type*)
  [∀ i, NontriviallyNormedField (F i)] [∀ i, IsUltrametricDist (F i)]

instance artinRestrictedLocalUnits_measurable :
    MeasurableSpace (ArtinRestrictedLocalUnits F) := borel _

instance artinRestrictedLocalUnits_borel :
    BorelSpace (ArtinRestrictedLocalUnits F) := ⟨rfl⟩

theorem artinRestrictedLocalFullNormKernel_isClosed (d : ι → ℝ) (n : ℕ) :
    IsClosed (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n :
      Set (ArtinRestrictedLocalUnits F × (Fin (n + 1) → ℂˣ))) :=
  artinFiniteComplexNormKernel_isClosed _ _ (artinRestrictedLocalLogNorm_continuous F d)

theorem artinRestrictedLocalCutoffEmbedding_isOpen (d : ι → ℝ) (n : ℕ) :
    IsOpenEmbedding (artinFiniteNormCutoffEmbedding (artinRestrictedLocalLogNorm F d)
      (artinRestrictedLocalUnitCutoff F) n (artinRestrictedLocalLogNorm_cutoff F d)) :=
  artinFiniteNormCutoffEmbedding_isOpenEmbedding _ _ _ _
    (artinRestrictedLocalUnitCutoff_isOpen F)

theorem artinRestrictedLocalUnitCutoffHaar_isHaar
    (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure] :
    (artinFiniteUnitCutoffHaar ν (artinRestrictedLocalUnitCutoff F)).IsHaarMeasure :=
  artinFiniteUnitCutoffHaar_isHaar ν _ (artinRestrictedLocalUnitCutoff_isOpen F)

theorem artinRestrictedLocalUnitCutoffHaar_finite [∀ i, ProperSpace (F i)]
    (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure] :
    IsFiniteMeasure (artinFiniteUnitCutoffHaar ν (artinRestrictedLocalUnitCutoff F)) :=
  artinFiniteUnitCutoffHaar_finite ν _ (artinRestrictedLocalUnitCutoff_isCompact F)
    (artinRestrictedLocalUnitCutoff_isOpen F)

/-- Haar existence is supplied by the proved local compactness, not an analytic input. -/
theorem artinRestrictedLocalHaar_exists [∀ i, ProperSpace (F i)] :
    ∃ ν : Measure (ArtinRestrictedLocalUnits F), ν.IsHaarMeasure :=
  ⟨Measure.haar, inferInstance⟩

instance artinRestrictedLocalFullNormKernel_locallyCompact [∀ i, ProperSpace (F i)]
    (d : ι → ℝ) (n : ℕ) :
    LocallyCompactSpace (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n) :=
  (artinRestrictedLocalFullNormKernel_isClosed F d n).locallyCompactSpace

theorem artinRestrictedLocalFullKernelHaar_exists [∀ i, ProperSpace (F i)]
    (d : ι → ℝ) (n : ℕ) :
    ∃ μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n),
      μ.IsHaarMeasure :=
  ⟨Measure.haar, inferInstance⟩

variable [Countable ι] [∀ i, ProperSpace (F i)]
  [∀ i, SecondCountableTopology (F i)ˣ]

/-- Actual full-kernel Haar pulls back to a positive multiple of the cutoff product Haar. -/
theorem artinRestrictedLocalCutoffHaar_normalization (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure] :
    μ.comap (artinFiniteNormCutoffEmbedding (artinRestrictedLocalLogNorm F d)
      (artinRestrictedLocalUnitCutoff F) n (artinRestrictedLocalLogNorm_cutoff F d)) =
      artinFiniteNormCutoffHaarFactor (artinRestrictedLocalLogNorm F d)
        (artinRestrictedLocalUnitCutoff F) n (artinRestrictedLocalLogNorm_cutoff F d)
        μ ν (artinRestrictedLocalUnitCutoff_isOpen F) •
        artinFiniteNormCutoffModelHaar ν (artinRestrictedLocalUnitCutoff F) n :=
  artinFiniteNormCutoffHaar_normalization _ _ _ _ μ ν
    (artinRestrictedLocalUnitCutoff_isOpen F)

theorem artinRestrictedLocalCutoffBesselC_pos (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) :
    0 < artinFiniteNormCutoffBesselC (artinRestrictedLocalLogNorm F d)
      (artinRestrictedLocalUnitCutoff F) n (artinRestrictedLocalLogNorm_cutoff F d)
      μ ν (artinRestrictedLocalUnitCutoff_isOpen F) c :=
  artinFiniteNormCutoffBesselC_pos _ _ _ _ μ ν
    (artinRestrictedLocalUnitCutoff_isCompact F) (artinRestrictedLocalUnitCutoff_isOpen F) hc

theorem artinRestrictedLocalCutoffBessel_mellin_convergent (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinFiniteNormCutoffBesselProfile (artinRestrictedLocalLogNorm F d)
      (artinRestrictedLocalUnitCutoff F) n μ c) s :=
  artinFiniteNormCutoffBesselProfile_mellin_convergent _ _ _
    (artinRestrictedLocalLogNorm_cutoff F d) μ ν
    (artinRestrictedLocalUnitCutoff_isCompact F) (artinRestrictedLocalUnitCutoff_isOpen F) hc hs

theorem artinRestrictedLocalUnitCutoff_mass_pos
    (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure] :
    0 < artinFiniteSheetMass ν (artinRestrictedLocalUnitCutoff F) :=
  artinFiniteSheetMass_haar_subgroup_pos (artinRestrictedLocalUnitCutoff F)
    (artinRestrictedLocalUnitCutoff_isCompact F) (artinRestrictedLocalUnitCutoff_isOpen F)

theorem artinRestrictedLocalUnitCutoffBessel_mellin (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteNormCutoffBesselProfile (artinRestrictedLocalLogNorm F d)
      (artinRestrictedLocalUnitCutoff F) n μ c) s =
      (artinFiniteNormCutoffBesselC (artinRestrictedLocalLogNorm F d) (artinRestrictedLocalUnitCutoff F) n
        (artinRestrictedLocalLogNorm_cutoff F d) μ ν (artinRestrictedLocalUnitCutoff_isOpen F) c : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) :=
  artinFiniteNormCutoffBesselProfile_mellin _ _ _ (artinRestrictedLocalLogNorm_cutoff F d) μ ν
    (artinRestrictedLocalUnitCutoff_isCompact F) (artinRestrictedLocalUnitCutoff_isOpen F) hc hs

theorem artinRestrictedLocalUnitCutoffBessel_gaussian (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinRestrictedLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinRestrictedLocalUnits F)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel
      (artinFiniteNormCutoffBesselC (artinRestrictedLocalLogNorm F d) (artinRestrictedLocalUnitCutoff F) n
        (artinRestrictedLocalLogNorm_cutoff F d) μ ν (artinRestrictedLocalUnitCutoff_isOpen F) c)
      (artinFiniteBesselSheetA c) (n + 1) T *
      artinFiniteNormCutoffBesselProfile (artinRestrictedLocalLogNorm F d)
        (artinRestrictedLocalUnitCutoff F) n μ c (u * T) ∂artinPositiveMultiplicativeMeasure) =
      reflectionLogGaussian u :=
  artinFiniteNormCutoffBesselProfile_gaussian _ _ _ (artinRestrictedLocalLogNorm_cutoff F d) μ ν
    (artinRestrictedLocalUnitCutoff_isCompact F) (artinRestrictedLocalUnitCutoff_isOpen F) hc hu

end
end SimultaneousPrimitiveRoots

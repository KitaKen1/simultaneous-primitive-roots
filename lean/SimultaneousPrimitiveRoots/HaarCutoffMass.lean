module

public import SimultaneousPrimitiveRoots.FiniteHaarBesselSheet

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable section

theorem artinFiniteSheetMass_compact_open_pos {Ω : Type*} [TopologicalSpace Ω]
    [MeasurableSpace Ω] {ν : Measure Ω} [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {U : Set Ω}
    (hUc : IsCompact U) (hUo : IsOpen U) (hne : U.Nonempty) :
    0 < artinFiniteSheetMass ν U :=
  artinFiniteSheetMass_pos (hUo.measure_ne_zero ν hne) hUc.measure_ne_top

/-- A compact open subgroup has a strictly positive finite mass for actual Haar measure.
Applying this to the paper's local unit cutoffs still requires their compactness and openness. -/
theorem artinFiniteSheetMass_haar_subgroup_pos {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] {ν : Measure G} [ν.IsHaarMeasure]
    (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    0 < artinFiniteSheetMass ν (K : Set G) :=
  artinFiniteSheetMass_compact_open_pos hKc hKo ⟨1, K.one_mem⟩

/-- The cutoff mass in a finite product is the product of the actual local masses. -/
theorem artinFiniteSheetMass_pi {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)]
    (U : ∀ i, Set (Ω i)) :
    artinFiniteSheetMass (Measure.pi ν) (Set.pi Set.univ U) =
      ∏ i, artinFiniteSheetMass (ν i) (U i) := by
  simp only [artinFiniteSheetMass, Measure.pi_pi, ENNReal.toReal_prod]

theorem artinFiniteSheetMass_pi_compact_open_pos {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, TopologicalSpace (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)] [∀ i, (ν i).IsOpenPosMeasure]
    [∀ i, IsFiniteMeasureOnCompacts (ν i)] {U : ∀ i, Set (Ω i)}
    (hUc : ∀ i, IsCompact (U i)) (hUo : ∀ i, IsOpen (U i)) (hne : ∀ i, (U i).Nonempty) :
    0 < artinFiniteSheetMass (Measure.pi ν) (Set.pi Set.univ U) := by
  rw [artinFiniteSheetMass_pi]
  exact Finset.prod_pos (fun i _ => artinFiniteSheetMass_compact_open_pos
    (hUc i) (hUo i) (hne i))

/-- A probability-normalized angular factor contributes exactly one to the cutoff mass. -/
theorem artinFiniteSheetMass_prod_probability {Ω Θ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] (ν : Measure Ω) (η : Measure Θ)
    [SigmaFinite η] [IsProbabilityMeasure η] (U : Set Ω) :
    artinFiniteSheetMass (ν.prod η) (U ×ˢ Set.univ) = artinFiniteSheetMass ν U := by
  simp [artinFiniteSheetMass, Measure.prod_prod]

theorem artinFiniteHaarBesselSheetProfile_gaussian_compact_open
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] {ν : Measure Ω}
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set Ω}
    (hUc : IsCompact U) (hUo : IsOpen U) (hne : U.Nonempty)
    {n : ℕ} {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteSheetMass ν U * artinFiniteBesselSheetC c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinFiniteHaarBesselSheetProfile ν U c (u * T)
          ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u :=
  artinFiniteHaarBesselSheetProfile_gaussian_smoothing
    (hUo.measure_ne_zero ν hne) hUc.measure_ne_top hc hu

/-- Actual finite products of compact open cutoffs give the Gaussian formula in this model.
The paper's local cutoffs and local-field Haar normalization must still be identified. -/
theorem artinFiniteHaarBesselSheetProfile_gaussian_pi_compact_open
    {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, TopologicalSpace (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] (ν : ∀ i, Measure (Ω i)) [∀ i, SigmaFinite (ν i)]
    [∀ i, (ν i).IsOpenPosMeasure] [∀ i, IsFiniteMeasureOnCompacts (ν i)]
    {U : ∀ i, Set (Ω i)} (hUc : ∀ i, IsCompact (U i)) (hUo : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel
      ((∏ i, artinFiniteSheetMass (ν i) (U i)) * artinFiniteBesselSheetC c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinFiniteHaarBesselSheetProfile (Measure.pi ν) (Set.pi Set.univ U) c (u * T)
          ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  rw [← artinFiniteSheetMass_pi ν U]
  apply artinFiniteHaarBesselSheetProfile_gaussian_smoothing _ _ hc hu
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hUo i).measure_ne_zero (ν i) (hne i))
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top (fun i _ => (hUc i).measure_ne_top)

end
end SimultaneousPrimitiveRoots

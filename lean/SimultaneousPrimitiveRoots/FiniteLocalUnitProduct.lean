module

public import SimultaneousPrimitiveRoots.NonarchimedeanUnitCutoff

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set
noncomputable section

variable {ι : Type*} [Fintype ι] (F : ι → Type*)
  [∀ i, NontriviallyNormedField (F i)] [∀ i, IsUltrametricDist (F i)]

/-- A finite family of actual nonarchimedean local groups; not all finite adeles. -/
def artinFiniteLocalUnitCutoff : Subgroup (∀ i, (F i)ˣ) :=
  Subgroup.pi Set.univ (fun i => artinLocalUnitCutoff (F i))

theorem artinFiniteLocalUnitCutoff_mem (z : ∀ i, (F i)ˣ) :
    z ∈ artinFiniteLocalUnitCutoff F ↔ ∀ i, ‖(z i : F i)‖ = 1 := by
  simp [artinFiniteLocalUnitCutoff, Subgroup.mem_pi, artinLocalUnitCutoff_mem]

theorem artinFiniteLocalUnitCutoff_isOpen :
    IsOpen (artinFiniteLocalUnitCutoff F : Set (∀ i, (F i)ˣ)) := by
  change IsOpen (Set.pi Set.univ (fun i => (artinLocalUnitCutoff (F i) : Set (F i)ˣ)))
  exact isOpen_set_pi Set.finite_univ (fun i _ => artinLocalUnitCutoff_isOpen (F i))

theorem artinFiniteLocalUnitCutoff_isCompact [∀ i, ProperSpace (F i)] :
    IsCompact (artinFiniteLocalUnitCutoff F : Set (∀ i, (F i)ˣ)) := by
  change IsCompact (Set.pi Set.univ (fun i => (artinLocalUnitCutoff (F i) : Set (F i)ˣ)))
  exact isCompact_univ_pi (fun i => artinLocalUnitCutoff_isCompact (F i))

/-- The actual product log-norm, allowing place-dependent normalization exponents. -/
def artinFiniteLocalLogNorm (d : ι → ℝ) : (∀ i, (F i)ˣ) →* Multiplicative ℝ :=
  ∏ i, (artinLocalLogNorm (F i) (d i)).comp (Pi.evalMonoidHom _ i)

theorem artinFiniteLocalLogNorm_apply (d : ι → ℝ) (z : ∀ i, (F i)ˣ) :
    artinFiniteLocalLogNorm F d z =
      Multiplicative.ofAdd (∑ i, d i * Real.log ‖(z i : F i)‖) := by
  simp [artinFiniteLocalLogNorm, artinLocalLogNorm]

theorem artinFiniteLocalLogNorm_continuous (d : ι → ℝ) :
    Continuous (artinFiniteLocalLogNorm F d) := by
  change Continuous (fun z => artinFiniteLocalLogNorm F d z)
  simp_rw [artinFiniteLocalLogNorm_apply]
  apply continuous_ofAdd.comp
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul
    ((Units.continuous_val.comp (continuous_apply i)).norm.log
      (fun z => norm_ne_zero_iff.mpr (z i).ne_zero)))

theorem artinFiniteLocalLogNorm_cutoff (d : ι → ℝ) :
    ∀ z ∈ artinFiniteLocalUnitCutoff F, artinFiniteLocalLogNorm F d z = 1 := by
  intro z hz
  have hn := (artinFiniteLocalUnitCutoff_mem F z).mp hz
  simp [artinFiniteLocalLogNorm_apply, hn]

variable [∀ i, ProperSpace (F i)] [∀ i, MeasurableSpace (F i)ˣ]
  [∀ i, BorelSpace (F i)ˣ] [∀ i, SecondCountableTopology (F i)ˣ]

theorem artinFiniteLocalUnitCutoff_mass_pos
    (ν : Measure (∀ i, (F i)ˣ)) [ν.IsHaarMeasure] :
    0 < artinFiniteSheetMass ν (artinFiniteLocalUnitCutoff F) :=
  artinFiniteSheetMass_haar_subgroup_pos (artinFiniteLocalUnitCutoff F)
    (artinFiniteLocalUnitCutoff_isCompact F) (artinFiniteLocalUnitCutoff_isOpen F)

theorem artinFiniteLocalUnitCutoffBessel_mellin (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinFiniteLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (∀ i, (F i)ˣ)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteNormCutoffBesselProfile (artinFiniteLocalLogNorm F d)
      (artinFiniteLocalUnitCutoff F) n μ c) s =
      (artinFiniteNormCutoffBesselC (artinFiniteLocalLogNorm F d) (artinFiniteLocalUnitCutoff F) n
        (artinFiniteLocalLogNorm_cutoff F d) μ ν (artinFiniteLocalUnitCutoff_isOpen F) c : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) :=
  artinFiniteNormCutoffBesselProfile_mellin _ _ _ (artinFiniteLocalLogNorm_cutoff F d) μ ν
    (artinFiniteLocalUnitCutoff_isCompact F) (artinFiniteLocalUnitCutoff_isOpen F) hc hs

theorem artinFiniteLocalUnitCutoffBessel_gaussian (d : ι → ℝ) (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinFiniteLocalLogNorm F d) n))
    [μ.IsHaarMeasure] (ν : Measure (∀ i, (F i)ˣ)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel
      (artinFiniteNormCutoffBesselC (artinFiniteLocalLogNorm F d) (artinFiniteLocalUnitCutoff F) n
        (artinFiniteLocalLogNorm_cutoff F d) μ ν (artinFiniteLocalUnitCutoff_isOpen F) c)
      (artinFiniteBesselSheetA c) (n + 1) T *
      artinFiniteNormCutoffBesselProfile (artinFiniteLocalLogNorm F d)
        (artinFiniteLocalUnitCutoff F) n μ c (u * T) ∂artinPositiveMultiplicativeMeasure) =
      reflectionLogGaussian u :=
  artinFiniteNormCutoffBesselProfile_gaussian _ _ _ (artinFiniteLocalLogNorm_cutoff F d) μ ν
    (artinFiniteLocalUnitCutoff_isCompact F) (artinFiniteLocalUnitCutoff_isOpen F) hc hu

end
end SimultaneousPrimitiveRoots

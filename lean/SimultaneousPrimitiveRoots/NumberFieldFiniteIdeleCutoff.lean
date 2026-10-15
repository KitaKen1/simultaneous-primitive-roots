module

public import SimultaneousPrimitiveRoots.NumberFieldFiniteCompletionCompact

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory Set Topology
open scoped WithZero Valued
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- All actual finite completions, restricted by their actual integral units. -/
abbrev ArtinNumberFieldFiniteUnits :=
  ArtinRestrictedLocalUnits (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

def artinNumberFieldFiniteUnitCutoff : Subgroup (ArtinNumberFieldFiniteUnits K) :=
  artinRestrictedLocalUnitCutoff (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

/-- The existing place norm is already N(v)^(-ord_v), so every weight here is one. -/
def artinNumberFieldFiniteLogNorm : ArtinNumberFieldFiniteUnits K →* Multiplicative ℝ :=
  artinRestrictedLocalLogNorm (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) (fun _ => 1)

theorem artinNumberFieldFiniteUnitCutoff_mem (z : ArtinNumberFieldFiniteUnits K) :
    z ∈ artinNumberFieldFiniteUnitCutoff K ↔
      ∀ v, ‖(z v : v.adicCompletion K)‖ = 1 :=
  artinRestrictedLocalUnitCutoff_mem _ _

theorem artinNumberFieldFiniteUnitCutoff_isOpen :
    IsOpen (artinNumberFieldFiniteUnitCutoff K : Set (ArtinNumberFieldFiniteUnits K)) :=
  artinRestrictedLocalUnitCutoff_isOpen _

theorem artinNumberFieldFiniteUnitCutoff_isCompact :
    IsCompact (artinNumberFieldFiniteUnitCutoff K : Set (ArtinNumberFieldFiniteUnits K)) :=
  artinRestrictedLocalUnitCutoff_isCompact _

theorem artinNumberFieldFiniteUnits_secondCountable :
    SecondCountableTopology (ArtinNumberFieldFiniteUnits K) := inferInstance

theorem artinNumberFieldFiniteUnits_locallyCompact :
    LocallyCompactSpace (ArtinNumberFieldFiniteUnits K) := inferInstance

theorem artinNumberFieldFiniteLogNorm_apply (z : ArtinNumberFieldFiniteUnits K) :
    artinNumberFieldFiniteLogNorm K z =
      Multiplicative.ofAdd (∑ᶠ v, Real.log ‖(z v : v.adicCompletion K)‖) := by
  simp [artinNumberFieldFiniteLogNorm, artinRestrictedLocalLogNorm_apply]

theorem artinNumberFieldFiniteLogNorm_continuous :
    Continuous (artinNumberFieldFiniteLogNorm K) :=
  artinRestrictedLocalLogNorm_continuous _ _

theorem artinNumberFieldFiniteLogNorm_cutoff :
    ∀ z ∈ artinNumberFieldFiniteUnitCutoff K, artinNumberFieldFiniteLogNorm K z = 1 :=
  artinRestrictedLocalLogNorm_cutoff _ _

theorem artinNumberFieldFiniteHaar_exists :
    ∃ ν : Measure (ArtinNumberFieldFiniteUnits K), ν.IsHaarMeasure :=
  artinRestrictedLocalHaar_exists _

theorem artinNumberFieldFiniteUnitCutoffHaar_finite
    (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure] :
    IsFiniteMeasure (artinFiniteUnitCutoffHaar ν (artinNumberFieldFiniteUnitCutoff K)) :=
  artinRestrictedLocalUnitCutoffHaar_finite _ ν

theorem artinNumberFieldFiniteFullKernelHaar_exists (n : ℕ) :
    ∃ μ : Measure (artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) n),
      μ.IsHaarMeasure :=
  artinRestrictedLocalFullKernelHaar_exists _ _ _

/-- The finite factors are actual number-field completions; the archimedean factor is still a
complex-place model. Identifying the paper's Whittaker/theta profile is a separate step. -/
theorem artinNumberFieldFiniteUnitCutoffBessel_mellin (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteNormCutoffBesselProfile (artinNumberFieldFiniteLogNorm K)
      (artinNumberFieldFiniteUnitCutoff K) n μ c) s =
      (artinFiniteNormCutoffBesselC (artinNumberFieldFiniteLogNorm K)
        (artinNumberFieldFiniteUnitCutoff K) n (artinNumberFieldFiniteLogNorm_cutoff K)
        μ ν (artinNumberFieldFiniteUnitCutoff_isOpen K) c : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) :=
  artinRestrictedLocalUnitCutoffBessel_mellin _ _ _ μ ν hc hs

theorem artinNumberFieldFiniteUnitCutoffBessel_gaussian (n : ℕ)
    (μ : Measure (artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) n))
    [μ.IsHaarMeasure] (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel
      (artinFiniteNormCutoffBesselC (artinNumberFieldFiniteLogNorm K)
        (artinNumberFieldFiniteUnitCutoff K) n (artinNumberFieldFiniteLogNorm_cutoff K)
        μ ν (artinNumberFieldFiniteUnitCutoff_isOpen K) c)
      (artinFiniteBesselSheetA c) (n + 1) T *
      artinFiniteNormCutoffBesselProfile (artinNumberFieldFiniteLogNorm K)
        (artinNumberFieldFiniteUnitCutoff K) n μ c (u * T) ∂artinPositiveMultiplicativeMeasure) =
      reflectionLogGaussian u :=
  artinRestrictedLocalUnitCutoffBessel_gaussian _ _ _ μ ν hc hu

end
end SimultaneousPrimitiveRoots

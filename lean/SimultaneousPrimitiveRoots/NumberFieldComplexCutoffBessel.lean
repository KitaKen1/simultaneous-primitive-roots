module

public import SimultaneousPrimitiveRoots.NumberFieldComplexNormKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField NumberField.InfinitePlace MeasureTheory Set Topology
open scoped Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K] (hr : 0 < nrComplexPlaces K)

/-- Transport the norm sheet in the actual completion product, keeping its finite part fixed. -/
def artinNumberFieldComplexNormSheetTransport (u : ℝ)
    (z : artinNumberFieldFiniteComplexNormKernel K) : ArtinNumberFieldFiniteComplexGroup K :=
  (z.1.1, (artinNumberFieldComplexUnitsEquiv K hr).symm
    ((artinFiniteComplexNormSheetTransport (artinNumberFieldFiniteLogNorm K)
      (nrComplexPlaces K - 1) u (artinNumberFieldFiniteComplexNormKernelEquiv K hr z)).2))

theorem artinNumberFieldComplexNormSheetTransport_model (u : ℝ)
    (z : artinNumberFieldFiniteComplexNormKernel K) :
    artinNumberFieldFiniteComplexUnitsEquiv K hr (artinNumberFieldComplexNormSheetTransport K hr u z) =
      artinFiniteComplexNormSheetTransport (artinNumberFieldFiniteLogNorm K)
        (nrComplexPlaces K - 1) u (artinNumberFieldFiniteComplexNormKernelEquiv K hr z) := by
  apply Prod.ext
  · rfl
  · exact (artinNumberFieldComplexUnitsEquiv K hr).apply_symm_apply _

theorem artinNumberFieldComplexNormSheetTransport_norm {u : ℝ} (hu : 0 < u)
    (z : artinNumberFieldFiniteComplexNormKernel K) :
    Real.exp (Multiplicative.toAdd (artinNumberFieldFiniteComplexNorm K
      (artinNumberFieldComplexNormSheetTransport K hr u z))) = u := by
  rw [← artinNumberFieldFiniteComplexUnitsEquiv_norm K hr,
    artinNumberFieldComplexNormSheetTransport_model]
  exact artinFiniteComplexNormSheetTransport_norm _ _ hu _

/-- Actual full-kernel Haar integral, with all complex-place completion norms in the integrand. -/
def artinNumberFieldComplexCutoffBesselProfile
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K))
    (c : ArtinNumberFieldComplexPlaces K → ℝ) (u : ℝ) : ℂ :=
  ∫ z in {z | z.1.1 ∈ artinNumberFieldFiniteUnitCutoff K},
    ∏ v : ArtinNumberFieldComplexPlaces K, artinBesselLocalProfile (c v)
      (‖((artinNumberFieldComplexNormSheetTransport K hr u z).2 v : v.1.Completion)‖ ^ 2) ∂μ

set_option maxHeartbeats 800000 in
theorem artinNumberFieldComplexCutoffBesselProfile_model
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K))
    (c : ArtinNumberFieldComplexPlaces K → ℝ) (u : ℝ) :
    artinNumberFieldComplexCutoffBesselProfile K hr μ c u =
      artinFiniteNormCutoffBesselProfile (artinNumberFieldFiniteLogNorm K)
        (artinNumberFieldFiniteUnitCutoff K) (nrComplexPlaces K - 1)
        (artinNumberFieldComplexKernelModelHaar K hr μ)
        (fun i => c (artinNumberFieldComplexPlaceIndex K hr i)) u := by
  have hm : MeasurableEmbedding (artinNumberFieldFiniteComplexNormKernelEquiv K hr :
      artinNumberFieldFiniteComplexNormKernel K →
        artinFiniteComplexNormKernel (artinNumberFieldFiniteLogNorm K) (nrComplexPlaces K - 1)) :=
    (artinNumberFieldFiniteComplexNormKernelEquiv K hr).toHomeomorph.measurableEmbedding
  rw [artinFiniteNormCutoffBesselProfile, artinNumberFieldComplexKernelModelHaar,
    hm.setIntegral_map]
  change (∫ z in {z | z.1.1 ∈ artinNumberFieldFiniteUnitCutoff K}, _ ∂μ) =
    ∫ z in {z | z.1.1 ∈ artinNumberFieldFiniteUnitCutoff K}, _ ∂μ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [← artinNumberFieldComplexUnitsEquiv_bessel_product K hr c
      (artinNumberFieldComplexNormSheetTransport K hr u z).2]
    have h := congrArg Prod.snd (artinNumberFieldComplexNormSheetTransport_model K hr u z)
    change artinNumberFieldComplexUnitsEquiv K hr
      (artinNumberFieldComplexNormSheetTransport K hr u z).2 = _ at h
    rw [h])

def artinNumberFieldComplexCutoffBesselA (c : ArtinNumberFieldComplexPlaces K → ℝ) : ℝ :=
  artinFiniteBesselSheetA (fun i => c (artinNumberFieldComplexPlaceIndex K hr i))

def artinNumberFieldComplexCutoffBesselC
    (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) [μ.IsHaarMeasure]
    (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
    (c : ArtinNumberFieldComplexPlaces K → ℝ) : ℝ :=
  artinFiniteNormCutoffBesselC (artinNumberFieldFiniteLogNorm K)
    (artinNumberFieldFiniteUnitCutoff K) (nrComplexPlaces K - 1)
    (artinNumberFieldFiniteLogNorm_cutoff K) (artinNumberFieldComplexKernelModelHaar K hr μ)
    ν (artinNumberFieldFiniteUnitCutoff_isOpen K)
    (fun i => c (artinNumberFieldComplexPlaceIndex K hr i))

theorem artinNumberFieldComplexCutoffBesselA_pos
    {c : ArtinNumberFieldComplexPlaces K → ℝ} (hc : ∀ v, 0 < c v) :
    0 < artinNumberFieldComplexCutoffBesselA K hr c :=
  (artinFiniteBesselSheet_constants_pos (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i))).2

variable (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) [μ.IsHaarMeasure]
  (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
  {c : ArtinNumberFieldComplexPlaces K → ℝ} (hc : ∀ v, 0 < c v)

include μ ν hc

theorem artinNumberFieldComplexCutoffBesselC_pos :
    0 < artinNumberFieldComplexCutoffBesselC K hr μ ν c :=
  artinFiniteNormCutoffBesselC_pos _ _ _ (artinNumberFieldFiniteLogNorm_cutoff K) _ _
    (artinNumberFieldFiniteUnitCutoff_isCompact K) (artinNumberFieldFiniteUnitCutoff_isOpen K)
    (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i))

theorem artinNumberFieldComplexCutoffBessel_mellin_convergent
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinNumberFieldComplexCutoffBesselProfile K hr μ c) s := by
  rw [funext (artinNumberFieldComplexCutoffBesselProfile_model K hr μ c)]
  exact artinFiniteNormCutoffBesselProfile_mellin_convergent _ _ _
    (artinNumberFieldFiniteLogNorm_cutoff K) _ ν
    (artinNumberFieldFiniteUnitCutoff_isCompact K) (artinNumberFieldFiniteUnitCutoff_isOpen K)
    (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i)) hs

theorem artinNumberFieldComplexCutoffBessel_mellin
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinNumberFieldComplexCutoffBesselProfile K hr μ c) s =
      (artinNumberFieldComplexCutoffBesselC K hr μ ν c : ℂ) *
        (artinNumberFieldComplexCutoffBesselA K hr c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ nrComplexPlaces K := by
  rw [funext (artinNumberFieldComplexCutoffBesselProfile_model K hr μ c)]
  simpa only [artinNumberFieldComplexCutoffBesselC, artinNumberFieldComplexCutoffBesselA,
    Nat.sub_add_cancel hr] using
    artinNumberFieldFiniteUnitCutoffBessel_mellin K (nrComplexPlaces K - 1) _ ν
      (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i)) hs

theorem artinNumberFieldComplexCutoffBessel_gaussian {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinNumberFieldComplexCutoffBesselC K hr μ ν c)
      (artinNumberFieldComplexCutoffBesselA K hr c) (nrComplexPlaces K) T *
        artinNumberFieldComplexCutoffBesselProfile K hr μ c (u * T)
      ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  simp_rw [artinNumberFieldComplexCutoffBesselProfile_model]
  simpa only [artinNumberFieldComplexCutoffBesselC, artinNumberFieldComplexCutoffBesselA,
    Nat.sub_add_cancel hr] using
    artinNumberFieldFiniteUnitCutoffBessel_gaussian K (nrComplexPlaces K - 1) _ ν
      (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i)) hu

end
end SimultaneousPrimitiveRoots

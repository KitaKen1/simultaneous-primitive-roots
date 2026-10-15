module

public import SimultaneousPrimitiveRoots.FiniteBesselSheetBounds
public import SimultaneousPrimitiveRoots.NumberFieldComplexCutoffBessel
public import SimultaneousPrimitiveRoots.ReflectionProfileFubini

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SimultaneousPrimitiveRoots

open NumberField InfinitePlace MeasureTheory Set IsDedekindDomain
open scoped Topology
noncomputable section

variable (K : Type*) [Field K] [NumberField K] (hr : 0 < nrComplexPlaces K)
  (μ : Measure (artinNumberFieldFiniteComplexNormKernel K)) [μ.IsHaarMeasure]
  (ν : Measure (ArtinNumberFieldFiniteUnits K)) [ν.IsHaarMeasure]
  {c : ArtinNumberFieldComplexPlaces K → ℝ} (hc : ∀ v, 0 < c v)

include μ ν hc

/-- The actual full-kernel Haar integral has a proved global power bound;
no bound on its defining fiber integral is supplied as a hypothesis. -/
theorem artinNumberFieldComplexCutoffBessel_regular {σ : ℝ}
    (hσ : -(5 / 6 : ℝ) < σ) :
    ContinuousOn (artinNumberFieldComplexCutoffBesselProfile K hr μ c) (Ioi 0) ∧
      ∃ M, 0 < M ∧ ∀ u, 0 < u →
        ‖artinNumberFieldComplexCutoffBesselProfile K hr μ c u‖ ≤ M * u ^ (-σ) := by
  rw [funext (artinNumberFieldComplexCutoffBesselProfile_model K hr μ c),
    funext (artinFiniteNormCutoffBesselProfile_factor _ _ _
      (artinNumberFieldFiniteLogNorm_cutoff K) _ ν
      (artinNumberFieldFiniteUnitCutoff_isCompact K)
      (artinNumberFieldFiniteUnitCutoff_isOpen K) _)]
  have h := artinFiniteBesselSheetProfile_regular
    (fun i => hc (artinNumberFieldComplexPlaceIndex K hr i)) hσ
  simpa only [one_mul] using artinProfile_scale_regular zero_lt_one _ h.1 h.2

theorem artinNumberFieldComplexCutoffBessel_continuousOn :
    ContinuousOn (artinNumberFieldComplexCutoffBesselProfile K hr μ c) (Ioi 0) :=
  (artinNumberFieldComplexCutoffBessel_regular K hr μ ν hc (σ := 0) (by norm_num)).1

theorem artinNumberFieldComplexCutoffBessel_two_ended {α A : ℝ}
    (hα : α < 5 / 6) (hA : 0 < A) :
    ∃ M, 0 < M ∧ ∀ u, 0 < u →
      ‖artinNumberFieldComplexCutoffBesselProfile K hr μ c u‖ ≤
        M * min (u ^ α) (u ^ (-A)) := by
  obtain ⟨M₁, hM₁, hb₁⟩ := (artinNumberFieldComplexCutoffBessel_regular K hr μ ν hc
    (σ := -α) (by linarith)).2
  obtain ⟨M₂, hM₂, hb₂⟩ := (artinNumberFieldComplexCutoffBessel_regular K hr μ ν hc
    (σ := A) (by linarith)).2
  refine ⟨max M₁ M₂, lt_of_lt_of_le hM₁ (le_max_left _ _), fun u hu => ?_⟩
  rw [mul_min_of_nonneg _ _ (le_of_lt (lt_of_lt_of_le hM₁ (le_max_left _ _)))]
  apply le_min
  · simpa only [neg_neg] using (hb₁ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_left M₁ M₂) (Real.rpow_nonneg hu.le (-(-α))))
  · exact (hb₂ u hu).trans
      (mul_le_mul_of_nonneg_right (le_max_right M₁ M₂) (Real.rpow_nonneg hu.le (-A)))

omit hc

/-- Combine finitely many independently derived profile bounds by a finite sum.
The common constant may depend on the field, Haar, family and exponent. -/
theorem artinNumberFieldComplexCutoffBessel_family_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ArtinNumberFieldComplexPlaces K → ℝ) (hc : ∀ i v, 0 < c i v)
    {σ : ℝ} (hσ : -(5 / 6 : ℝ) < σ) :
    ∃ M, 0 < M ∧ ∀ i u, 0 < u →
      ‖artinNumberFieldComplexCutoffBesselProfile K hr μ (c i) u‖ ≤ M * u ^ (-σ) := by
  classical
  have h (i : ι) := (artinNumberFieldComplexCutoffBessel_regular K hr μ ν (hc i) hσ).2
  choose M hM hb using h
  have hsum₀ : 0 ≤ ∑ i, M i := Finset.sum_nonneg (fun i _ => (hM i).le)
  refine ⟨1 + ∑ i, M i, by linarith, fun i u hu => ?_⟩
  have hle : M i ≤ 1 + ∑ j, M j := by
    have hsum := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => (hM j).le) (Finset.mem_univ i)
    linarith
  exact (hb i u hu).trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hu.le _))

/-- Actual ideal/exponent indices may select any member of this fixed finite
K-profile family. The envelope and all profile continuity are derived. -/
theorem artinNumberFieldBessel_reflection_integral_norm_summable
    {ι : Type*} [Fintype ι]
    (c : ι → ArtinNumberFieldComplexPlaces K → ℝ) (hc : ∀ i v, 0 < c i v)
    (s : Finset (HeightOneSpectrum (𝓞 K)))
    (pick : ReflectionIdealIndices K s → ι) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    {σ t : ℝ} (hσ : 1 / 2 < σ) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x) :
    (∀ x, Integrable (reflectionProfileTerm K s κ a
      (fun x => artinNumberFieldComplexCutoffBesselProfile K hr μ (c (pick x))) t x)
      artinPositiveMultiplicativeMeasure) ∧
      Summable (fun x => ∫ T, ‖reflectionProfileTerm K s κ a
        (fun x => artinNumberFieldComplexCutoffBesselProfile K hr μ (c (pick x))) t x T‖
        ∂artinPositiveMultiplicativeMeasure) := by
  obtain ⟨M, hM, hb⟩ := artinNumberFieldComplexCutoffBessel_family_bound K hr μ ν c hc
    (show -(5 / 6 : ℝ) < σ by linarith)
  exact reflectionProfile_integral_norm_summable K s hκ a _
    (fun x => artinNumberFieldComplexCutoffBessel_continuousOn K hr μ ν (hc (pick x)))
    hσ ht ha (fun x u hu => hb (pick x) u hu)

theorem artinNumberFieldBessel_reflection_integral_tsum
    {ι : Type*} [Fintype ι]
    (c : ι → ArtinNumberFieldComplexPlaces K → ℝ) (hc : ∀ i v, 0 < c i v)
    (s : Finset (HeightOneSpectrum (𝓞 K)))
    (pick : ReflectionIdealIndices K s → ι) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    {σ t : ℝ} (hσ : 1 / 2 < σ) (ht : 0 < t)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x) :
    (∑' x, ∫ T, reflectionProfileTerm K s κ a
      (fun x => artinNumberFieldComplexCutoffBesselProfile K hr μ (c (pick x))) t x T
      ∂artinPositiveMultiplicativeMeasure) =
      ∫ T, (∑' x, reflectionProfileTerm K s κ a
        (fun x => artinNumberFieldComplexCutoffBesselProfile K hr μ (c (pick x))) t x T)
        ∂artinPositiveMultiplicativeMeasure := by
  let := reflectionIdealIndices_countable K s
  have h := artinNumberFieldBessel_reflection_integral_norm_summable K hr μ ν c hc
    s pick hκ a hσ ht ha
  exact integral_tsum_of_summable_integral_norm h.1 h.2

theorem artinNumberFieldBessel_reflection_absolute_integral_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ArtinNumberFieldComplexPlaces K → ℝ) (hc : ∀ i v, 0 < c i v)
    (s : Finset (HeightOneSpectrum (𝓞 K)))
    (pick : ReflectionIdealIndices K s → ι) {κ : ℝ → ℂ}
    (hκ : ReflectionKernelDecay κ) (a : ReflectionIdealIndices K s → ℂ)
    {σ : ℝ} (hσ : 1 / 2 < σ)
    (ha : ∀ x, ‖a x‖ ≤ reflectionIdealAmplitude K s x) :
    ∃ M, 0 < M ∧ ∀ t, 0 < t →
      (∫ T, (∑' x, ‖reflectionProfileTerm K s κ a
        (fun x => artinNumberFieldComplexCutoffBesselProfile K hr μ (c (pick x))) t x T‖)
        ∂artinPositiveMultiplicativeMeasure) ≤
        M * t ^ σ * artinKernelMoment κ σ *
          ∑' x, admissibleFrozenTripleTerm K s σ x := by
  obtain ⟨M, hM, hb⟩ := artinNumberFieldComplexCutoffBessel_family_bound K hr μ ν c hc
    (show -(5 / 6 : ℝ) < σ by linarith)
  refine ⟨M, hM, fun t ht => ?_⟩
  exact reflectionProfile_absolute_integral_le K s hκ a _
    (fun x => artinNumberFieldComplexCutoffBessel_continuousOn K hr μ ν (hc (pick x)))
    hσ hM.le ht ha (fun x u hu => hb (pick x) u hu)

end
end SimultaneousPrimitiveRoots

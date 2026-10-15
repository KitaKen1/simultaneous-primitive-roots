module

public import SimultaneousPrimitiveRoots.NumberFieldFrozenMajorant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain MeasureTheory
noncomputable section

theorem numberField_ideals_countable (K : Type*) [Field K] [NumberField K] :
    Countable (Ideal (𝓞 K)) := by
  letI (n : ℕ) : Finite {I : Ideal (𝓞 K) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  exact Countable.of_equiv _ (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => I.absNorm))

theorem numberField_frozenIndices_countable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    Countable ((s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K)) := by
  letI := numberField_ideals_countable K
  infer_instance

/-- Derive convergence of integral norms from the proved scalar series.
The measurable profile envelope is a separate input, not an asserted
Whittaker or theta estimate. The measure can include the dT/T weight. -/
theorem frozenMajorant_integral_norm_summable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M μ)
    (F : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ numberFieldFrozenMajorantTerm K s σ x * M t) :
    (∀ x, Integrable (F x) μ) ∧
      Summable (fun x => ∫ t, ‖F x t‖ ∂μ) := by
  have hi (x) : Integrable (F x) μ :=
    (hM.const_mul _).mono' (hF x) (Filter.Eventually.of_forall (hbound x))
  refine ⟨hi, ?_⟩
  apply ((numberFieldFrozenMajorantTerm_summable K s hσ).mul_right
    (∫ t, M t ∂μ)).of_nonneg_of_le
  · intro x
    exact integral_nonneg fun _ => norm_nonneg _
  · intro x
    calc
      _ ≤ ∫ t, numberFieldFrozenMajorantTerm K s σ x * M t ∂μ :=
        integral_mono (hi x).norm (hM.const_mul _) (hbound x)
      _ = _ := integral_const_mul _ _

/-- All exchanges of the sum over frozen exponents and the two ideals
with integration follow once the profile envelope is supplied. -/
theorem frozenMajorant_integral_tsum
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M μ)
    (F : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ numberFieldFrozenMajorantTerm K s σ x * M t) :
    (∑' x, ∫ t, F x t ∂μ) = ∫ t, (∑' x, F x t) ∂μ := by
  letI := numberField_frozenIndices_countable K s
  have h := frozenMajorant_integral_norm_summable K s hσ μ M hM0 hM F hF hbound
  exact integral_tsum_of_summable_integral_norm h.1 h.2

/-- The total absolute integral has the actual Dirichlet sum as its
constant. This is stronger than just postulating a summable integral bound. -/
theorem frozenMajorant_total_integral_norm_le
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (M : X → ℝ)
    (hM0 : ∀ t, 0 ≤ M t) (hM : Integrable M μ)
    (F : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K) → X → ℂ)
    (hF : ∀ x, AEStronglyMeasurable (F x) μ)
    (hbound : ∀ x t, ‖F x t‖ ≤ numberFieldFrozenMajorantTerm K s σ x * M t) :
    (∑' x, ∫ t, ‖F x t‖ ∂μ) ≤
      (∑' x, numberFieldFrozenMajorantTerm K s σ x) * ∫ t, M t ∂μ := by
  have h := frozenMajorant_integral_norm_summable K s hσ μ M hM0 hM F hF hbound
  have hi (x) : (∫ t, ‖F x t‖ ∂μ) ≤
      numberFieldFrozenMajorantTerm K s σ x * ∫ t, M t ∂μ := by
    calc
      _ ≤ ∫ t, numberFieldFrozenMajorantTerm K s σ x * M t ∂μ :=
        integral_mono (h.1 x).norm (hM.const_mul _) (hbound x)
      _ = _ := integral_const_mul _ _
  have hb := (numberFieldFrozenMajorantTerm_summable K s hσ).mul_right (∫ t, M t ∂μ)
  simpa only [tsum_mul_right] using h.2.tsum_le_tsum hi hb

end
end SimultaneousPrimitiveRoots

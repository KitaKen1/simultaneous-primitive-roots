module

public import SimultaneousPrimitiveRoots.ProgressionSieveOptimization
public import SimultaneousPrimitiveRoots.GaussianPrimePowerCounting

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

/-- All three AP/cyclotomic upper bounds now have unconditional constants. -/
theorem exists_progression_upper_bounds {η : ℝ} (hη : η < 1 / 5) :
    ∃ C Cg Ce : ℝ, 0 ≤ C ∧ 0 ≤ Cg ∧ 0 ≤ Ce ∧
      UniformProgressionUpperBound η C ∧ UniformGaussianProgressionUpperBound η Cg ∧
      UniformCyclotomicGaussianUpperBound η Ce := by
  obtain ⟨C, hC, hAP⟩ := exists_progressionChebyshevUpperBound
  obtain ⟨hp, hg, he⟩ := progression_upper_bounds_of_chebyshev hη hC hAP
  refine ⟨6 * C + 1, gaussianAbelConstant * C + 1, gaussianAbelConstant * C + 3,
    by positivity, ?_, ?_, hp, hg, he⟩ <;>
    nlinarith [gaussianAbelConstant_pos]

theorem exists_uniformProgressionUpperBound {η : ℝ} (hη : η < 1 / 5) :
    ∃ C : ℝ, 0 ≤ C ∧ UniformProgressionUpperBound η C := by
  obtain ⟨C, Cg, Ce, hC, _, _, hp, _, _⟩ := exists_progression_upper_bounds hη
  exact ⟨C, hC, hp⟩

theorem exists_uniformGaussianProgressionUpperBound {η : ℝ} (hη : η < 1 / 5) :
    ∃ C : ℝ, 0 ≤ C ∧ UniformGaussianProgressionUpperBound η C := by
  obtain ⟨Cp, C, Ce, _, hC, _, _, hg, _⟩ := exists_progression_upper_bounds hη
  exact ⟨C, hC, hg⟩

theorem exists_uniformCyclotomicGaussianUpperBound {η : ℝ} (hη : η < 1 / 5) :
    ∃ C : ℝ, 0 ≤ C ∧ UniformCyclotomicGaussianUpperBound η C := by
  obtain ⟨Cp, Cg, C, _, _, hC, _, _, he⟩ := exists_progression_upper_bounds hη
  exact ⟨C, hC, he⟩

/-- The constant is chosen before A, B, and Q. No KR hypothesis is needed here. -/
theorem exists_uniform_sparseBadPowerResidueBound {η : ℝ} (hη : η < 1 / 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : Finset ℕ) (B : Set ℕ) (Q : ℝ → ℕ),
      SparseBadPowerResidueBound A η C B Q := by
  obtain ⟨C, hC, hp⟩ := exists_uniformProgressionUpperBound hη
  exact ⟨C, hC, sparseBadPowerResidueBound_of_progression hp⟩

/-- The sieve discharges the bad-q estimate; supply, KR, and the small/large-good
analytic counts are still explicit hypotheses. -/
theorem mainClaim_of_gaussian_full_good_bounds {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηfifth : η < 1 / 5)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hgood : ∀ A : Finset ℕ, Admissible A →
      ∃ K C : ℝ, ∃ B : Set ℕ, ∃ Q : ℝ → ℕ,
        0 ≤ K ∧ 0 ≤ C ∧ Summable (badReciprocalWeight B) ∧
        Filter.Tendsto Q Filter.atTop Filter.atTop ∧
        SmallExponentPowerResidueBound A η K Q ∧ GaussianFullLargeGoodTraceBound A δ η C B Q) :
    MainClaim := by
  obtain ⟨Cbad, hCb, hbad⟩ := exists_uniform_sparseBadPowerResidueBound hηfifth
  apply mainClaim_of_gaussian_full_sparse_bounds hη hηδ (by linarith) hsupply
  intro A hA
  obtain ⟨K, C, B, Q, hK, hC, hB, hQ, hs, hg⟩ := hgood A hA
  exact ⟨K, C, Cbad, B, Q, hK, hC, hCb, hB, hQ, hs, hg, hbad A B Q⟩

end
end SimultaneousPrimitiveRoots

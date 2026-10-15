module

public import SimultaneousPrimitiveRoots.SlowCutoff
public import SimultaneousPrimitiveRoots.ProgressionSieveConsequences

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter
noncomputable section

/-- A bound valid for every good prime is compatible with any slowly
growing small/large cutoff. -/
theorem gaussianFullLargeGoodTraceBound_of_all_good {A : Finset ℕ} {δ η C : ℝ}
    {B : Set ℕ}
    (h : GaussianFullLargeGoodTraceBound A δ η C B (fun _ => 0)) (Q : ℝ → ℕ) :
    GaussianFullLargeGoodTraceBound A δ η C B Q := by
  filter_upwards [h] with x hx
  intro a ha q ha2 hq haq _ hgood hcut
  exact hx a ha q ha2 hq haq hq.pos hgood hcut

/-- This closing route replaces a quantitative uniform small-q theorem
by fixed-q eventual estimates. Supply, KR and the actual good-prime
Gaussian upper bounds remain explicit arithmetic/analytic inputs. -/
theorem mainClaim_of_fixed_counts_and_all_good {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηfifth : η < 1 / 5)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hfixed : ∀ A : Finset ℕ, Admissible A → ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : ℕ, ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, q.Prime → a < q →
        ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
          C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))))
    (hgood : ∀ A : Finset ℕ, Admissible A → ∃ C : ℝ, ∃ B : Set ℕ,
      0 ≤ C ∧ Summable (badReciprocalWeight B) ∧
        GaussianFullLargeGoodTraceBound A δ η C B (fun _ => 0)) : MainClaim := by
  apply mainClaim_of_gaussian_full_good_bounds hη hηδ hηfifth hsupply
  intro A hA
  obtain ⟨C0, hC0, hc⟩ := hfixed A hA
  obtain ⟨C, B, hC, hB, hg⟩ := hgood A hA
  obtain ⟨Q, hQ, hs⟩ := exists_smallExponentPowerResidueBound_of_fixed_counts A η C0 hC0 hc
  exact ⟨(A.card : ℝ) * C0, C, B, Q,
    mul_nonneg (Nat.cast_nonneg _) hC0, hC, hB, hQ, hs,
    gaussianFullLargeGoodTraceBound_of_all_good hg Q⟩

end
end SimultaneousPrimitiveRoots

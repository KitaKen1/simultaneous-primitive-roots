module

public import SimultaneousPrimitiveRoots.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.KummerUniformDeletionBridge

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

/-- The zero list is the actual critical-strip zero carrier of the supplied
entire full quotient, with finite natural multiplicities. Entireness, uniform
mass/gap and the actual signed formula remain explicit inputs. -/
theorem kummerFullQuotientGaussianUpperInputs_of_indexed_zeros {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {x δ M R : ℝ}
    (hw : Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)))
    (hm : (∑' i : fullQuotientZeroIndex H,
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤
        M * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))
    (hg : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ)
    (hf : primeKummerGaussianFullSignedTrace a q x ≤
      artinGaussianZeroRemainder (fullQuotientIndexedZero H) x / ((q : ℝ) - 1) +
        R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    Countable (fullQuotientZeroIndex H) ∧ KummerFullQuotientGaussianUpperInputs a q x δ M R := by
  refine ⟨numberFieldEntireFullQuotientContinuation_countable_zeroIndex
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH, ?_⟩
  exact ⟨fullQuotientZeroIndex H, fullQuotientIndexedZero H,
    fullQuotientIndexedZero_strip H, hw, hm, hg, hf⟩

end
end SimultaneousPrimitiveRoots

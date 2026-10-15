module

public import SimultaneousPrimitiveRoots.SparseExceptionAggregation

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter

/-- All primes in the progression 1 mod q, without a power-residue condition. -/
noncomputable def dyadicProgressionPrimes (q : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor (2 * x) + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ q ∣ p - 1

theorem powerResidueExceptionPrimes_subset_progression (a q : ℕ) (x : ℝ) :
    powerResidueExceptionPrimes a q x ⊆ dyadicProgressionPrimes q x := by
  classical
  intro p hp
  obtain ⟨hpr, hprime, hpx, hp2x, _, hqd, _⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpr, hprime, hpx, hp2x, hqd⟩

theorem powerResidueExceptionPrimes_card_le_progression (a q : ℕ) (x : ℝ) :
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      ((dyadicProgressionPrimes q x).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (powerResidueExceptionPrimes_subset_progression a q x)

/-- The AP upper bound needed in research_note_ja.md. Its constant-existence
theorem is proved in ProgressionSieveConsequences using an actual AP sieve. -/
def UniformProgressionUpperBound (η C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, q.Prime → q ≤ Nat.floor (2 * x ^ η) →
    ((dyadicProgressionPrimes q x).card : ℝ) ≤ C * (x / Real.log x) * (1 / (q : ℝ))

theorem sparseBadPowerResidueBound_of_progression {η C : ℝ}
    (h : UniformProgressionUpperBound η C) (A : Finset ℕ) (B : Set ℕ) (Q : ℝ → ℕ) :
    SparseBadPowerResidueBound A η C B Q := by
  filter_upwards [h] with x hx
  intro a _ q hq _ _ hcut
  exact (powerResidueExceptionPrimes_card_le_progression a q x).trans (hx q hq hcut)

/-- The Gaussian cutoff is below the finite height 2q^2 for large q.
This verifies only the real inequality, not a theorem about Hecke zeros. -/
theorem researchNote_height_below_quadratic {L δ q : ℝ}
    (hL : 0 ≤ L) (hδ : δ < 1 / 2) (hq : 0 < q) (hlarge : L < q ^ 4) :
    Real.sqrt (8 * δ * L) < 2 * q ^ 2 := by
  apply (Real.sqrt_lt' (by positivity : 0 < 2 * q ^ 2)).2
  have hprod : δ * L ≤ (1 / 2 : ℝ) * L := mul_le_mul_of_nonneg_right hδ.le hL
  nlinarith [sq_nonneg q]

theorem researchNote_reflection_exponent_gap (a b : ℝ) :
    (a + b / 2 - 1 / 2) - (a / 2 + (1 - a) / 6) =
      b / 2 - 2 * (1 - a) / 3 := by ring

theorem researchNote_crude_rows_exponent_gap (a b : ℝ) :
    (a / 2 - b + 3 * (1 - a) / 2) - (a / 2 + (1 - a) / 6) =
      4 * (1 - a) / 3 - b := by ring

/-- Exponent tuning cannot make both of these particular coarse bounds smaller
than the main row. It does not contradict the original stronger estimates. -/
theorem researchNote_crude_rows_and_reflection_incompatible (a b : ℝ) :
    ¬ (a + b / 2 - 1 / 2 < a / 2 + (1 - a) / 6 ∧
      a / 2 - b + 3 * (1 - a) / 2 < a / 2 + (1 - a) / 6) := by
  rintro ⟨hr, hn⟩
  linarith

end SimultaneousPrimitiveRoots

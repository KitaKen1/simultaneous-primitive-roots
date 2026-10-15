module

public import SimultaneousPrimitiveRoots.KummerPrimeSplitting
public import SimultaneousPrimitiveRoots.ConditionalMain

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Ideal Filter

/-- The dyadic count of rational primes with the maximal possible number of
prime ideals in the given number field. -/
noncomputable def dyadicCompletelySplitPrimes (K : Type*) [Field K] [NumberField K]
    (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
      ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K

theorem powerResidueExceptionPrimes_eq_restrictedKummerSplit {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) :
    powerResidueExceptionPrimes a q x =
      (dyadicCompletelySplitPrimes (PrimeKummerField a q) x).filter
        (fun p => ¬ p ∣ a ∧ q ∣ p - 1) := by
  classical
  ext p
  simp only [powerResidueExceptionPrimes, dyadicCompletelySplitPrimes, Finset.mem_filter]
  constructor
  · rintro ⟨hpr, hp, hx, h2x, hpa, hqp, hpow⟩
    let : Fact p.Prime := ⟨hp⟩
    exact ⟨⟨hpr, hp, hx, h2x, (primeKummer_prime_splitsCompletely_iff hqp).mpr hpow⟩,
      hpa, hqp⟩
  · rintro ⟨⟨hpr, hp, hx, h2x, hs⟩, hpa, hqp⟩
    let : Fact p.Prime := ⟨hp⟩
    exact ⟨hpr, hp, hx, h2x, hpa, hqp, (primeKummer_prime_splitsCompletely_iff hqp).mp hs⟩

theorem powerResidueExceptionPrimes_subset_kummerSplit {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) :
    powerResidueExceptionPrimes a q x ⊆ dyadicCompletelySplitPrimes (PrimeKummerField a q) x := by
  rw [powerResidueExceptionPrimes_eq_restrictedKummerSplit x]
  exact Finset.filter_subset _ _

theorem powerResidueExceptionPrimes_card_le_kummerSplit {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x : ℝ) :
    (powerResidueExceptionPrimes a q x).card ≤
      (dyadicCompletelySplitPrimes (PrimeKummerField a q) x).card :=
  Finset.card_le_card (powerResidueExceptionPrimes_subset_kummerSplit x)

/-- An unproved analytic target about actual complete-splitting counts. The
single eventual quantifier precedes the moving range of q. -/
def UniformKummerSplitPrimeBound (A : Finset ℕ) (δ η C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ≤ ⌊2 * x ^ η⌋₊ →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    ((dyadicCompletelySplitPrimes (PrimeKummerField a q) x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x

theorem uniformPowerResidueBound_of_kummer_counts {A : Finset ℕ} {δ η C : ℝ}
    (hA : ∀ a ∈ A, 2 ≤ a) (hc : UniformKummerSplitPrimeBound A δ η C) :
    UniformPowerResidueBound A δ η C := by
  filter_upwards [hc] with x hx
  intro a ha q hq haq hcut
  let : Fact (2 ≤ a) := ⟨hA a ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  have hle : ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      (dyadicCompletelySplitPrimes (PrimeKummerField a q) x).card := by
    exact_mod_cast powerResidueExceptionPrimes_card_le_kummerSplit x
  exact hle.trans (hx a ha q (hA a ha) hq haq hcut)

theorem mainClaim_of_kummer_count_bounds {δ η : ℝ} (hη : 0 < η) (hηδ : η < δ)
    (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hkummer : ∀ A : Finset ℕ, Admissible A →
      ∃ C : ℝ, 0 ≤ C ∧ UniformKummerSplitPrimeBound A δ η C) : MainClaim := by
  apply mainClaim_of_analytic_bounds hη hηhalf hηδ hsupply
  intro A hA
  obtain ⟨C, hC, hc⟩ := hkummer A hA
  exact ⟨C, hC, uniformPowerResidueBound_of_kummer_counts hA.2.1 hc⟩

end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.NumberFieldZetaQuotient
public import SimultaneousPrimitiveRoots.KummerIncompleteLSeries

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- A single actual continuation for the common nonprincipal power.
It is defined from the two actual corrected Dedekind continuations. -/
def primeKummerIncompletePowerContinuation (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] : ℂ → ℂ :=
  numberFieldIncompleteZetaQuotient (PrimeKummerField a q) (CyclotomicField q ℚ)
    (primeKummerTopBadPrimes a q) (primeKummerBaseBadPrimes a q)

theorem primeKummerIncompletePowerContinuation_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompletePowerContinuation a q s =
      (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) := by
  rw [primeKummerIncompletePowerContinuation, numberFieldIncompleteZetaQuotient_eq _ _ _ _ hs]
  exact (primeKummerIncompleteEulerL_pow_eq_zeta_quotient a q χ hχ hs).symm

theorem primeKummerIncompletePowerContinuation_at_one (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    primeKummerIncompletePowerContinuation a q 1 =
      numberFieldIncompleteZetaResidue (PrimeKummerField a q) (primeKummerTopBadPrimes a q) /
        numberFieldIncompleteZetaResidue (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) :=
  numberFieldIncompleteZetaQuotient_at_one _ _ _ _

/-- Actual pointwise nonvanishing on the whole closed boundary, with
no common-width or growing-q quantitative estimate. -/
theorem primeKummerIncompletePowerContinuation_ne_zero (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 ≤ s.re) :
    primeKummerIncompletePowerContinuation a q s ≠ 0 :=
  numberFieldIncompleteZetaQuotient_ne_zero _ _ _ _ hs

theorem primeKummerIncompletePowerContinuation_differentiableAt (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (primeKummerIncompletePowerContinuation a q) s :=
  numberFieldIncompleteZetaQuotient_differentiableAt _ _ _ _ hs

/-- Every boundary point has an open nonvanishing holomorphic
continuation neighborhood, simultaneously matching every nonprincipal
character power. The neighborhood depends on a,q and the point. -/
theorem primeKummerIncompletePowerContinuation_exists_neighborhood (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 ≤ s.re) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧
      DifferentiableOn ℂ (primeKummerIncompletePowerContinuation a q) U ∧
      (∀ z ∈ U, primeKummerIncompletePowerContinuation a q z ≠ 0) ∧
      ∀ χ : PrimeKummerCharacter a q, χ ≠ 1 → ∀ z ∈ U, 1 < z.re →
        primeKummerIncompletePowerContinuation a q z =
          (primeKummerIncompleteEulerL a q χ z) ^ (q - 1) := by
  obtain ⟨U, hUopen, hsU, hdU, hnU⟩ :=
    numberFieldIncompleteZetaQuotient_exists_neighborhood (PrimeKummerField a q)
      (CyclotomicField q ℚ) (primeKummerTopBadPrimes a q) (primeKummerBaseBadPrimes a q) hs
  exact ⟨U, hUopen, hsU, hdU, hnU, fun χ hχ _ _ hz =>
    primeKummerIncompletePowerContinuation_eq a q χ hχ hz⟩

theorem primeKummerIncompletePowerContinuation_logDeriv_eq (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    logDeriv (primeKummerIncompletePowerContinuation a q) s =
      logDeriv (numberFieldIncompleteZeta (PrimeKummerField a q) (primeKummerTopBadPrimes a q)) s -
        logDeriv (numberFieldIncompleteZeta (CyclotomicField q ℚ)
          (primeKummerBaseBadPrimes a q)) s :=
  numberFieldIncompleteZetaQuotient_logDeriv_eq _ _ _ _ hs

theorem primeKummerIncompletePowerContinuation_logDeriv_continuousOn (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    ContinuousOn (logDeriv (primeKummerIncompletePowerContinuation a q)) {s : ℂ | 1 ≤ s.re} :=
  numberFieldIncompleteZetaQuotient_logDeriv_continuousOn _ _ _ _

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.NumberFieldPrimePowerDirichlet

@[expose] public section

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The signed series uses the disjoint union of actual top and base
prime powers. A top term is positive in its coefficient; a base term has
a minus sign. Both omit precisely the primes over a*q. -/
def primeKummerSignedPrimePowerTerm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (s : ℂ) :
    ((HeightOneSpectrum (𝓞 (PrimeKummerField a q)) × ℕ) ⊕
      (HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) × ℕ)) → ℂ :=
  Sum.elim
    (fun pe => numberFieldDeletedPrimePowerTerm (PrimeKummerField a q)
      (primeKummerTopBadPrimes a q) s pe / ((q - 1 : ℕ) : ℂ))
    (fun pe => -numberFieldDeletedPrimePowerTerm (CyclotomicField q ℚ)
      (primeKummerBaseBadPrimes a q) s pe / ((q - 1 : ℕ) : ℂ))

/-- Actual coefficient identity for the common signed logarithmic
derivative on the half-plane of absolute convergence. -/
theorem primeKummerSignedLogDerivative_eq_primePowerSeries (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    primeKummerSignedLogDerivative a q s =
      (numberFieldDeletedPrimePowerSeries (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s -
        numberFieldDeletedPrimePowerSeries (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) s) /
          ((q - 1 : ℕ) : ℂ) := by
  rw [primeKummerSignedLogDerivative_eq_deleted a q hs,
    numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv _ _ hs,
    numberFieldDeletedPrimePowerSeries_eq_neg_logDeriv _ _ hs]
  ring

/-- HasSum certifies absolute convergence of the actual two-field
prime-power terms to the actual signed logarithmic derivative. -/
theorem primeKummerSignedPrimePowerTerm_hasSum (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    HasSum (primeKummerSignedPrimePowerTerm a q s) (primeKummerSignedLogDerivative a q s) := by
  have hK := (numberFieldDeletedPrimePowerTerm_hasSum (PrimeKummerField a q)
    (primeKummerTopBadPrimes a q) hs).div_const ((q - 1 : ℕ) : ℂ)
  have hE := (numberFieldDeletedPrimePowerTerm_hasSum (CyclotomicField q ℚ)
    (primeKummerBaseBadPrimes a q) hs).neg.div_const ((q - 1 : ℕ) : ℂ)
  have hsum : HasSum (primeKummerSignedPrimePowerTerm a q s)
      ((-logDeriv (numberFieldIncompleteZeta (PrimeKummerField a q)
          (primeKummerTopBadPrimes a q)) s) / ((q - 1 : ℕ) : ℂ) +
        (-(-logDeriv (numberFieldIncompleteZeta (CyclotomicField q ℚ)
          (primeKummerBaseBadPrimes a q)) s)) / ((q - 1 : ℕ) : ℂ)) :=
    HasSum.sum hK hE
  convert hsum using 1
  rw [primeKummerSignedLogDerivative_eq_deleted a q hs]
  ring

theorem primeKummerSignedPrimePowerTerm_summable (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    Summable (primeKummerSignedPrimePowerTerm a q s) :=
  (primeKummerSignedPrimePowerTerm_hasSum a q hs).summable

theorem primeKummerSignedPrimePowerTerm_tsum (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    (∑' pe, primeKummerSignedPrimePowerTerm a q s pe) = primeKummerSignedLogDerivative a q s :=
  (primeKummerSignedPrimePowerTerm_hasSum a q hs).tsum_eq

end
end SimultaneousPrimitiveRoots

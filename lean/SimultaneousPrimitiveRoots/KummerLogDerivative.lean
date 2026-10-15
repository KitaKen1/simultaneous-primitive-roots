module

public import SimultaneousPrimitiveRoots.KummerBoundaryCompact

@[expose] public section

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The exact finite logarithmic-derivative correction from deleted primes. -/
def numberFieldDeletedLogCorrection (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∑ P ∈ S, Complex.log (P.asIdeal.absNorm : ℂ) / ((P.asIdeal.absNorm : ℂ) ^ s - 1)

theorem numberFieldDeletedLogCorrection_differentiableOn (K : Type*) [Field K]
    [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DifferentiableOn ℂ (numberFieldDeletedLogCorrection K S) {s : ℂ | 0 < s.re} :=
  TauCeti.differentiableOn_sum_log_absNorm_div_cpow_sub_one S

theorem numberFieldIncompleteZeta_logDeriv_eq (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (numberFieldIncompleteZeta K S) s =
      logDeriv (dedekindZeta K) s + numberFieldDeletedLogCorrection K S s :=
  TauCeti.logDeriv_LSeries_ofBadPrimes S hs

/-- The signed common-factor logarithmic derivative. It is not a positive
prime count, and no zero sum or explicit formula is assumed in this definition. -/
def primeKummerSignedLogDerivative (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (s : ℂ) : ℂ :=
  -logDeriv (primeKummerIncompletePowerContinuation a q) s / ((q - 1 : ℕ) : ℂ)

theorem primeKummerSignedLogDerivative_eq_deleted (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    primeKummerSignedLogDerivative a q s =
      (-logDeriv (numberFieldIncompleteZeta (PrimeKummerField a q)
          (primeKummerTopBadPrimes a q)) s +
        logDeriv (numberFieldIncompleteZeta (CyclotomicField q ℚ)
          (primeKummerBaseBadPrimes a q)) s) / ((q - 1 : ℕ) : ℂ) := by
  simp only [primeKummerSignedLogDerivative,
    primeKummerIncompletePowerContinuation_logDeriv_eq a q hs, neg_sub]
  ring

/-- Finite corrections appear with their exact signs, including primes
over a*q. No ramified Hecke factor identity is claimed. -/
theorem primeKummerSignedLogDerivative_eq_full (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 < s.re) :
    primeKummerSignedLogDerivative a q s =
      (-logDeriv (dedekindZeta (PrimeKummerField a q)) s +
        logDeriv (dedekindZeta (CyclotomicField q ℚ)) s -
        numberFieldDeletedLogCorrection (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s +
        numberFieldDeletedLogCorrection (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) s) /
          ((q - 1 : ℕ) : ℂ) := by
  rw [primeKummerSignedLogDerivative_eq_deleted a q hs,
    numberFieldIncompleteZeta_logDeriv_eq _ _ hs, numberFieldIncompleteZeta_logDeriv_eq _ _ hs]
  ring

theorem primeKummerSignedLogDerivative_continuousOn (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    ContinuousOn (primeKummerSignedLogDerivative a q) {s : ℂ | 1 ≤ s.re} :=
  (primeKummerIncompletePowerContinuation_logDeriv_continuousOn a q).neg.div_const _

theorem primeKummerSignedLogDerivative_differentiableAt (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (primeKummerSignedLogDerivative a q) s := by
  obtain ⟨U, ho, hsU, hd, hn, _⟩ :=
    primeKummerIncompletePowerContinuation_exists_neighborhood a q hs
  exact (((hd.deriv ho).differentiableAt (ho.mem_nhds hsU)).div
    (hd.differentiableAt (ho.mem_nhds hsU)) (hn s hsU)).neg.div_const _

/-- The divisor q-1 from the common power gives the exact norm scaling. -/
theorem primeKummerSignedLogDerivative_norm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (s : ℂ) :
    ‖primeKummerSignedLogDerivative a q s‖ =
      ‖logDeriv (primeKummerIncompletePowerContinuation a q) s‖ / ((q - 1 : ℕ) : ℝ) := by
  simp [primeKummerSignedLogDerivative]

/-- Compact-tube bounds transfer to the actual signed logarithmic
derivative, preserving dependence on the bounded family. -/
theorem primeKummerSignedLogDerivative_bounded_family (A : Finset ℕ) (N : ℕ) (T : ℝ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧ ∀ a ∈ A, ∀ q : ℕ,
      ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q, q ≤ N →
      let : Fact (2 ≤ a) := ⟨ha⟩
      let : Fact q.Prime := ⟨hq⟩
      let : Fact (a < q) := ⟨haq⟩
      ∀ s : ℂ, 1 - ε ≤ s.re → s.re ≤ 1 + ε → |s.im| ≤ T →
        ‖primeKummerSignedLogDerivative a q s‖ ≤ M / ((q - 1 : ℕ) : ℝ) := by
  obtain ⟨ε, M, hε, hM, h⟩ := primeKummerPower_bounded_family_rectangle A N T
  refine ⟨ε, M, hε, hM, ?_⟩
  intro a haA q ha hq haq hqN
  dsimp only
  intro s hl hr ht
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  rw [primeKummerSignedLogDerivative_norm]
  exact div_le_div_of_nonneg_right (h a haA q ha hq haq hqN s hl hr ht).2.2.2.2
    (Nat.cast_nonneg _)

end
end SimultaneousPrimitiveRoots

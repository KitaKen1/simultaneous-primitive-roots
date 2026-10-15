module

public import SimultaneousPrimitiveRoots.TailAggregation
public import SimultaneousPrimitiveRoots.AsymptoticAssembly
public import SimultaneousPrimitiveRoots.PerfectPowerCutoff

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics

/-- The marked-prime supply input for fixed admissible progressions.
Each modulus is fixed before x tends to infinity; theta does not depend on it. -/
def CandidateSupplyBound (A : Finset ℕ) (η θ : ℝ) : Prop :=
  ∀ Y H : ℕ, ∀ R : Finset ℕ, 0 < H →
    (∀ u ∈ R, u < H ∧ u.Coprime H) → ProgressionConditions A Y H R →
      ∀ᶠ x : ℝ in atTop,
        θ * ((R.card : ℝ) / Nat.totient H) * (x / Real.log x) ≤
          ((factorCandidates η H R x).card : ℝ)

/-- Close the entire finite and asymptotic reduction while retaining the two
unproved analytic inputs as explicit hypotheses. -/
theorem positiveDyadicLowerBound_of_analytic_bounds {A : Finset ℕ}
    (hA : Admissible A) {δ η θ C : ℝ}
    (hη : 0 < η) (hηhalf : η < 1 / 2) (hηδ : η < δ)
    (hθ : 0 < θ) (hC : 0 ≤ C)
    (hsupply : CandidateSupplyBound A η θ)
    (hsplit : UniformPowerResidueBound A δ η C) :
    PositiveDyadicLowerBound A := by
  classical
  let K : ℝ := (A.card : ℝ) * C
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hC
  obtain ⟨M, hM, hselector⟩ := exists_selector_with_progressionConditions hA.2.1 hA.2.2
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  obtain ⟨T, hTlarge⟩ := exists_nat_gt
    (max 1 (max (4 * K * (Nat.totient M : ℝ) / θ) ((A.sup id : ℕ) : ℝ)))
  have hTreal : 1 < (T : ℝ) := (le_max_left _ _).trans_lt hTlarge
  have hT : 1 ≤ T := by exact_mod_cast hTreal.le
  have hTpos : 0 < (T : ℝ) := by linarith
  have hlarge : 4 * K * (Nat.totient M : ℝ) ≤ θ * (T : ℝ) := by
    have hd : 4 * K * (Nat.totient M : ℝ) / θ < (T : ℝ) :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have := (div_lt_iff₀ hθ).mp hd
    nlinarith
  have hbase_cutoff : ∀ a ∈ A, a ≤ 2 * T ^ 2 + 1 := by
    intro a ha
    have hsup : ((A.sup id : ℕ) : ℝ) < (T : ℝ) :=
      (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have hnat : A.sup id < T := by exact_mod_cast hsup
    have haT : a < T := (Finset.le_sup (f := id) ha).trans_lt hnat
    have hTpow : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) T
    omega
  have _hperfect := no_large_perfect_power_exponents hA.2.1 hbase_cutoff
  obtain ⟨H, R, hH, _, hdensity, hregular, hprogressions⟩ := hselector T hT
  have hgap : K / (2 * (T : ℝ) ^ 2 + 1) <
      θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) :=
    positive_parameter_difference hθ hphi hTpos hlarge
  have hsup := hsupply (2 * T ^ 2 + 1) H R hH hregular hprogressions
  have htail := powerResidueExceptionUnion_eventually_bound
    (Y := 2 * T ^ 2 + 1) (by omega) hbase_cutoff hC hη.le hsplit
  have hsmall := smallOrderExceptionUnion_isLittleO hA.2.1 hηhalf
  have herror := splittingErrorEnvelope_isLittleO hK hη.le hηδ
  have hremainder : (fun x : ℝ =>
      -((A.biUnion fun a => smallOrderExceptionPrimes a η x).card : ℝ) -
        splittingErrorEnvelope K δ η x) =o[atTop] (fun x => x / Real.log x) := by
    simpa using hsmall.neg_left.sub herror
  apply positiveDyadicLowerBound_of_asymptotic_gap hgap hremainder
  filter_upwards [hsup, htail, eventually_ge_atTop (3 : ℝ)] with x hxSupply hxTail hx
  have hscale : 0 ≤ x / Real.log x := by
    exact div_nonneg (by linarith) (Real.log_pos (by linarith)).le
  have hlower : θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) * (x / Real.log x) ≤
      ((factorCandidates η H R x).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdensity hθ.le) hscale
    have heq : θ * (1 / (2 * (Nat.totient M : ℝ) * (T : ℝ))) =
        θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by ring
    rw [heq] at hmul
    exact hmul.trans hxSupply
  have hc := factorCandidates_sub_exceptions_le_primeCount (η := η) hA.2.1 hx hprogressions
  have htail' : ((powerResidueExceptionUnion A (2 * T ^ 2 + 1) η x).card : ℝ) ≤
      (K / (2 * (T : ℝ) ^ 2 + 1)) * (x / Real.log x) + splittingErrorEnvelope K δ η x := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hxTail
  nlinarith

/-- This implication does not assert either analytic input. -/
theorem mainClaim_of_analytic_bounds {δ η : ℝ}
    (hη : 0 < η) (hηhalf : η < 1 / 2) (hηδ : η < δ)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsplit : ∀ A : Finset ℕ, Admissible A →
      ∃ C : ℝ, 0 ≤ C ∧ UniformPowerResidueBound A δ η C) :
    MainClaim := by
  intro A hA
  obtain ⟨θ, hθ, hSupply⟩ := hsupply A hA
  obtain ⟨C, hC, hSplit⟩ := hsplit A hA
  exact positiveDyadicLowerBound_of_analytic_bounds hA hη hηhalf hηδ hθ hC hSupply hSplit

theorem mainClaim_of_fixed_analytic_bounds
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A (1 / 4000000) θ)
    (hsplit : ∀ A : Finset ℕ, Admissible A →
      ∃ C : ℝ, 0 ≤ C ∧ UniformPowerResidueBound A (1 / 1000000) (1 / 4000000) C) :
    MainClaim :=
  mainClaim_of_analytic_bounds (by norm_num) (by norm_num) (by norm_num) hsupply hsplit

end SimultaneousPrimitiveRoots

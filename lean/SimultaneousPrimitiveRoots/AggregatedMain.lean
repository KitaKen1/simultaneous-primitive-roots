module

public import SimultaneousPrimitiveRoots.ConditionalMain

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics

/-- A weaker analytic target: bound only the actual union of exceptions.
K is independent of Y; the little-o remainder and its onset may depend on Y.
No individual q estimate or fixed zero-free width is assumed by this interface. -/
def AggregatedPowerResidueBound (A : Finset ℕ) (η K : ℝ) : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → (∀ a ∈ A, a ≤ Y) →
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x => x / Real.log x) ∧
      ∀ᶠ x : ℝ in atTop, ((powerResidueExceptionUnion A Y η x).card : ℝ) ≤
        (K / (Y : ℝ)) * (x / Real.log x) + E x

/-- An average over q suffices; it need not imply a bound for every individual q. -/
def SummedPowerResidueBound (A : Finset ℕ) (η K : ℝ) : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → (∀ a ∈ A, a ≤ Y) →
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x => x / Real.log x) ∧
      ∀ᶠ x : ℝ in atTop,
        (∑ a ∈ A, ∑ q ∈ mediumObstructionPrimes Y η x,
          ((powerResidueExceptionPrimes a q x).card : ℝ)) ≤
            (K / (Y : ℝ)) * (x / Real.log x) + E x

theorem aggregatedPowerResidueBound_of_summed {A : Finset ℕ} {η K : ℝ}
    (h : SummedPowerResidueBound A η K) : AggregatedPowerResidueBound A η K := by
  intro Y hY hbase
  obtain ⟨E, hE, hbound⟩ := h Y hY hbase
  refine ⟨E, hE, ?_⟩
  filter_upwards [hbound] with x hx
  exact (powerResidueExceptionUnion_card_le_sum A Y η x).trans hx

theorem aggregatedPowerResidueBound_of_uniform {A : Finset ℕ} {δ η C : ℝ}
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hηδ : η < δ)
    (h : UniformPowerResidueBound A δ η C) :
    AggregatedPowerResidueBound A η ((A.card : ℝ) * C) := by
  intro Y hY hbase
  refine ⟨splittingErrorEnvelope ((A.card : ℝ) * C) δ η,
    splittingErrorEnvelope_isLittleO (mul_nonneg (Nat.cast_nonneg _) hC) hη hηδ,
    powerResidueExceptionUnion_eventually_bound hY hbase hC hη h⟩

/-- Close the target from an aggregate exception estimate, without requiring
uniform bounds for individual exponents or specifying a zero-free width. -/
theorem positiveDyadicLowerBound_of_aggregated_bounds {A : Finset ℕ}
    (hA : Admissible A) {η θ K : ℝ}
    (hηhalf : η < 1 / 2) (hθ : 0 < θ) (_hK : 0 ≤ K)
    (hsupply : CandidateSupplyBound A η θ)
    (haggregate : AggregatedPowerResidueBound A η K) :
    PositiveDyadicLowerBound A := by
  classical
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
  obtain ⟨H, R, hH, _, hdensity, hregular, hprogressions⟩ := hselector T hT
  have hgap : K / (2 * (T : ℝ) ^ 2 + 1) <
      θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) :=
    positive_parameter_difference hθ hphi hTpos hlarge
  have hsup := hsupply (2 * T ^ 2 + 1) H R hH hregular hprogressions
  obtain ⟨E, hE, htail⟩ := haggregate (2 * T ^ 2 + 1) (by omega) hbase_cutoff
  have hsmall := smallOrderExceptionUnion_isLittleO hA.2.1 hηhalf
  have hremainder : (fun x : ℝ =>
      -((A.biUnion fun a => smallOrderExceptionPrimes a η x).card : ℝ) - E x)
        =o[atTop] (fun x => x / Real.log x) := by
    simpa using hsmall.neg_left.sub hE
  apply positiveDyadicLowerBound_of_asymptotic_gap hgap hremainder
  filter_upwards [hsup, htail, eventually_ge_atTop (3 : ℝ)] with x hxSupply hxTail hx
  have hscale : 0 ≤ x / Real.log x :=
    div_nonneg (by linarith) (Real.log_pos (by linarith)).le
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
      (K / (2 * (T : ℝ) ^ 2 + 1)) * (x / Real.log x) + E x := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hxTail
  nlinarith

theorem mainClaim_of_aggregated_bounds {η : ℝ} (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (haggregate : ∀ A : Finset ℕ, Admissible A →
      ∃ K : ℝ, 0 ≤ K ∧ AggregatedPowerResidueBound A η K) : MainClaim := by
  intro A hA
  obtain ⟨θ, hθ, hSupply⟩ := hsupply A hA
  obtain ⟨K, hK, hAggregate⟩ := haggregate A hA
  exact positiveDyadicLowerBound_of_aggregated_bounds hA hηhalf hθ hK hSupply hAggregate

theorem mainClaim_of_summed_bounds {η : ℝ} (hηhalf : η < 1 / 2)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hsummed : ∀ A : Finset ℕ, Admissible A →
      ∃ K : ℝ, 0 ≤ K ∧ SummedPowerResidueBound A η K) : MainClaim := by
  apply mainClaim_of_aggregated_bounds hηhalf hsupply
  intro A hA
  obtain ⟨K, hK, hSum⟩ := hsummed A hA
  exact ⟨K, hK, aggregatedPowerResidueBound_of_summed hSum⟩

end SimultaneousPrimitiveRoots

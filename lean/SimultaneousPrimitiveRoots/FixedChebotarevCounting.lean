module

public import SimultaneousPrimitiveRoots.NumberFieldChebotarev
public import SimultaneousPrimitiveRoots.KummerCounting
public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import SimultaneousPrimitiveRoots.SlowCutoffMain
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter NumberField IsDedekindDomain TauCeti
open scoped NumberField
noncomputable section
open Classical

def rationalPrimeIdeal (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem rationalPrimeIdeal_absNorm (p : ℕ) (hp : p.Prime) :
    Ideal.absNorm (rationalPrimeIdeal p hp).asIdeal = p := by
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)

/-- Transport complete-splitting sets from the integer base to the
isomorphic ring of integers of Q, retaining the exact prime ideals. -/
theorem rationalPrimeIdeal_primesOver_eq (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (hp : p.Prime) :
    (rationalPrimeIdeal p hp).asIdeal.primesOver (𝓞 K) =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  let v := rationalPrimeIdeal p hp
  have hself : v.asIdeal.under (𝓞 ℚ) = v.asIdeal := by ext z; rfl
  have hn : Ideal.absNorm (v.asIdeal.under ℤ) = p := by
    have h := Ideal.absNorm_under_ringOfIntegers_rat v.asIdeal
    rw [hself, rationalPrimeIdeal_absNorm] at h
    exact h.symm
  have hI := Int.ideal_span_absNorm_eq_self (v.asIdeal.under ℤ)
  rw [hn] at hI
  have h := Ideal.primesOver_under_ringOfIntegers_rat_eq
    (S := 𝓞 K) (p := v.asIdeal.under ℤ) v.asIdeal
  rw [hself, ← hI] at h
  exact h

/-- Inject actual rational completely split primes into the identity
Frobenius prime-ideal carrier over Q. -/
theorem dyadicCompletelySplitPrimes_card_le_frobeniusPrimeCount
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] (x : ℝ) :
    (dyadicCompletelySplitPrimes K x).card ≤ Chebotarev.frobeniusPrimeCount ℚ K 1 (2 * x) := by
  let S := dyadicCompletelySplitPrimes K x
  have hprime {p : ℕ} (hp : p ∈ S) : p.Prime :=
    (Finset.mem_filter.mp hp).2.1
  let f : {p // p ∈ S} → HeightOneSpectrum (𝓞 ℚ) :=
    fun p => rationalPrimeIdeal p.1 (hprime p.2)
  have hf : Function.Injective f := by
    intro p t h
    apply Subtype.ext
    have hn := congrArg (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) h
    simpa only [f, rationalPrimeIdeal_absNorm] using hn
  have hsub : S.attach.image f ⊆
      (primesLE ℚ (2 * x)).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ K 1) := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hp, _, h2x, hs⟩ := Finset.mem_filter.mp p.2
    apply Finset.mem_filter.mpr
    constructor
    · simpa only [mem_normLE, f, rationalPrimeIdeal_absNorm] using h2x
    · apply Chebotarev.mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank.mpr
      simpa only [f, rationalPrimeIdeal_primesOver_eq] using hs
  have hcount : Chebotarev.frobeniusPrimeCount ℚ K 1 (2 * x) =
      ((primesLE ℚ (2 * x)).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ K 1)).card := by
    rw [Chebotarev.frobeniusPrimeCount_eq_card]
    change Nat.card (↥{v : HeightOneSpectrum (𝓞 ℚ) |
      v ∈ Chebotarev.frobeniusPrimeSet ℚ K 1 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ 2 * x}) = _
    rw [Nat.card_coe_set_eq]
    have hset : {v : HeightOneSpectrum (𝓞 ℚ) |
        v ∈ Chebotarev.frobeniusPrimeSet ℚ K 1 ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ 2 * x} =
        ↑((primesLE ℚ (2 * x)).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ K 1)) := by
      ext v
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, mem_normLE]
      tauto
    rw [hset, Set.ncard_coe_finset]
  change S.card ≤ _
  calc
    S.card = (S.attach.image f).card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_attach]
    _ ≤ ((primesLE ℚ (2 * x)).filter
        (· ∈ Chebotarev.frobeniusPrimeSet ℚ K 1)).card := Finset.card_le_card hsub
    _ = _ := hcount.symm

/-- A fixed-field dyadic complete-splitting bound with the universal
coefficient 4. The onset is allowed to depend on the field. -/
theorem dyadicCompletelySplitPrimes_eventually_le (K : Type*)
    [Field K] [NumberField K] [IsGalois ℚ K] :
    ∀ᶠ x : ℝ in atTop, ((dyadicCompletelySplitPrimes K x).card : ℝ) ≤
      4 * (x / Real.log x) * (1 / (Module.finrank ℚ K : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have h := ht.eventually (fixed_frobeniusPrimeCount_one_eventually_le ℚ K)
  filter_upwards [h, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogs : Real.log x ≤ Real.log (2 * x) :=
    Real.log_le_log (by linarith) (by linarith)
  have hc : ((dyadicCompletelySplitPrimes K x).card : ℝ) ≤
      Chebotarev.frobeniusPrimeCount ℚ K 1 (2 * x) := by
    exact_mod_cast dyadicCompletelySplitPrimes_card_le_frobeniusPrimeCount K x
  calc
    _ ≤ 2 * ((2 * x) / Real.log (2 * x)) *
        (1 / (Module.finrank ℚ K : ℝ)) := hc.trans hx
    _ ≤ 2 * ((2 * x) / Real.log x) * (1 / (Module.finrank ℚ K : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- Fixed-q actual exceptional-prime counts, now without an analytic
counting hypothesis. Only the usual arithmetic Kummer conditions remain. -/
theorem fixed_powerResidueExceptionPrimes_eventually_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    ∀ᶠ x : ℝ in atTop, ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      4 * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  filter_upwards [dyadicCompletelySplitPrimes_eventually_le (PrimeKummerField a q)] with x hx
  have hc : ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      (dyadicCompletelySplitPrimes (PrimeKummerField a q) x).card := by
    exact_mod_cast powerResidueExceptionPrimes_card_le_kummerSplit x
  have hd : (Module.finrank ℚ (PrimeKummerField a q) : ℝ) =
      (q : ℝ) * ((q : ℝ) - 1) := by
    rw [primeKummerField_absolute_degree ha.out hq.out haq.out]
    simp only [Nat.cast_mul, Nat.cast_sub hq.out.one_le, Nat.cast_one]
  rw [hd] at hx
  exact hc.trans hx

/-- Coefficient 4 works simultaneously for a finite set of bases and
every fixed prime q; each eventual threshold may still depend on q. -/
theorem fixed_powerResidueCounts_finset (A : Finset ℕ) (hA : ∀ a ∈ A, 2 ≤ a) :
    ∀ q : ℕ, ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, q.Prime → a < q →
      ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
        4 * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) := by
  intro q
  apply (eventually_all_finset A).mpr
  intro a ha
  by_cases hp : q.Prime
  · by_cases haq : a < q
    · let : Fact (2 ≤ a) := ⟨hA a ha⟩
      let : Fact q.Prime := ⟨hp⟩
      let : Fact (a < q) := ⟨haq⟩
      filter_upwards [fixed_powerResidueExceptionPrimes_eventually_le a q] with x hx
      exact fun _ _ => hx
    · exact Eventually.of_forall fun _ _ h => (haq h).elim
  · exact Eventually.of_forall fun _ h _ => (hp h).elim

/-- The complete small-exponent input is now proved unconditionally for
finite bases >=2, with one slowly growing cutoff shared by every Y. -/
theorem exists_smallExponentPowerResidueBound (A : Finset ℕ) (η : ℝ)
    (hA : ∀ a ∈ A, 2 ≤ a) :
    ∃ Q : ℝ → ℕ, Tendsto Q atTop atTop ∧
      SmallExponentPowerResidueBound A η ((A.card : ℝ) * 4) Q :=
  exists_smallExponentPowerResidueBound_of_fixed_counts A η 4 (by norm_num)
    (fixed_powerResidueCounts_finset A hA)

/-- Fixed-q counting has been discharged. Supply S, KR and actual
uniform good-prime Gaussian bounds are the remaining inputs. -/
theorem mainClaim_of_all_good_gaussian_bounds {δ η : ℝ} (hη : 0 ≤ η)
    (hηδ : η < δ) (hηfifth : η < 1 / 5)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hgood : ∀ A : Finset ℕ, Admissible A → ∃ C : ℝ, ∃ B : Set ℕ,
      0 ≤ C ∧ Summable (badReciprocalWeight B) ∧
        GaussianFullLargeGoodTraceBound A δ η C B (fun _ => 0)) : MainClaim := by
  apply mainClaim_of_fixed_counts_and_all_good hη hηδ hηfifth hsupply _ hgood
  intro A hA
  exact ⟨4, by norm_num, fixed_powerResidueCounts_finset A hA.2.1⟩

end
end SimultaneousPrimitiveRoots

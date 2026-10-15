module

public import SimultaneousPrimitiveRoots.CandidateReduction
public import SimultaneousPrimitiveRoots.SmallOrderAsymptotic
public import SimultaneousPrimitiveRoots.ProgressionSelector
public import SimultaneousPrimitiveRoots.Counting

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable def factorCandidates (η : ℝ) (H : ℕ) (R : Finset ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
      (∃ u ∈ R, p ≡ u [MOD H]) ∧
        ∃ Q r : ℕ, Q.Prime ∧ p - 1 = Q * r ∧ r ≤ ⌊2 * x ^ η⌋₊

noncomputable def powerResidueExceptionPrimes (a q : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ ¬ p ∣ a ∧
      q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1

noncomputable def mediumObstructionPrimes (Y : ℕ) (η x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x ^ η⌋₊ + 1)).filter fun q => q.Prime ∧ Y < q

noncomputable def powerResidueExceptionUnion (A : Finset ℕ) (Y : ℕ) (η x : ℝ) : Finset ℕ :=
  A.biUnion fun a => (mediumObstructionPrimes Y η x).biUnion fun q =>
    powerResidueExceptionPrimes a q x

def ProgressionConditions (A : Finset ℕ) (Y H : ℕ) (R : Finset ℕ) : Prop :=
  ∀ u ∈ R, ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
    (∀ a ∈ A, ¬ IsSquare (a : ZMod p)) ∧
      ∀ q : ℕ, q.Prime → 3 ≤ q → q ≤ Y → ¬ q ∣ p - 1

theorem nonsquare_natCast_not_dvd {a p : ℕ} (h : ¬ IsSquare (a : ZMod p)) :
    ¬ p ∣ a := by
  intro hdvd
  have hz := (ZMod.natCast_eq_zero_iff a p).mpr hdvd
  exact h ⟨0, by simp [hz]⟩

/-- Every failed candidate is captured by the two explicit finite exception sets. -/
theorem bad_factorCandidates_subset {A : Finset ℕ} {Y H : ℕ} {R : Finset ℕ}
    {η x : ℝ} (hpos : ∀ a ∈ A, 2 ≤ a) (hx : 3 ≤ x)
    (hR : ProgressionConditions A Y H R) :
    badCandidates A (factorCandidates η H R x) ⊆
      (A.biUnion fun a => smallOrderExceptionPrimes a η x) ∪
        powerResidueExceptionUnion A Y η x := by
  classical
  intro p hp
  obtain ⟨hpC, hpbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprange, hpprime, hpx, hp2x, hres, Q, r, hQ, hfactor, hrN⟩ :=
    Finset.mem_filter.mp hpC
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  obtain ⟨u, hu, hpu⟩ := hres
  obtain ⟨hsq, havoid⟩ := hR u hu p hpprime hp3 hpu
  have hf : ¬ ∀ a ∈ A, PrimitiveRootMod a p := fun hall => hpbad ⟨hpprime, hall⟩
  push Not at hf
  obtain ⟨a, haA, hafail⟩ := hf
  have ha : ¬ p ∣ a := nonsquare_natCast_not_dvd (hsq a haA)
  have havoid' : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≤ Y → ¬ q ∣ p - 1 := by
    intro q hq hq2 hqY
    exact havoid q hq (by have := hq.two_le; omega) hqY
  rcases candidate_failure_cases hpprime (by omega) (hpos a haA) ha (hsq a haA)
    havoid' hQ hfactor hrN hafail with hsmall | ⟨q, hq, hqY, hqN, hqp, hpow⟩
  · apply Finset.mem_union.mpr
    apply Or.inl
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haA, ?_⟩
    exact Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, hsmall⟩
  · apply Finset.mem_union.mpr
    apply Or.inr
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haA, Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hqY⟩
    · exact Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, hp2x, ha, hqp, hpow⟩

theorem factorCandidates_sub_exceptions_le_primeCount {A : Finset ℕ}
    {Y H : ℕ} {R : Finset ℕ} {η x : ℝ} (hpos : ∀ a ∈ A, 2 ≤ a) (hx : 3 ≤ x)
    (hR : ProgressionConditions A Y H R) :
    ((factorCandidates η H R x).card : ℝ) -
      ((A.biUnion fun a => smallOrderExceptionPrimes a η x).card : ℝ) -
        (powerResidueExceptionUnion A Y η x).card ≤ primeCount A x := by
  classical
  have hb := Finset.card_le_card (bad_factorCandidates_subset (η := η) hpos hx hR)
  have hu := Finset.card_union_le
    (A.biUnion fun a => smallOrderExceptionPrimes a η x) (powerResidueExceptionUnion A Y η x)
  have hreal : ((badCandidates A (factorCandidates η H R x)).card : ℝ) ≤
      ((A.biUnion fun a => smallOrderExceptionPrimes a η x).card : ℝ) +
        (powerResidueExceptionUnion A Y η x).card := by
    exact_mod_cast hb.trans hu
  have hc := candidates_sub_bad_le_primeCount (A := A) (C := factorCandidates η H R x)
    (fun p hp => ⟨(Finset.mem_filter.mp hp).2.2.1, (Finset.mem_filter.mp hp).2.2.2.1⟩)
  linarith

theorem exists_selector_with_progressionConditions {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) :
    ∃ M : ℕ, 0 < M ∧ ∀ T : ℕ, 1 ≤ T → ∃ H : ℕ, ∃ R : Finset ℕ,
      0 < H ∧ R.Nonempty ∧
        1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) ≤ (R.card : ℝ) / Nat.totient H ∧
          (∀ u ∈ R, u < H ∧ u.Coprime H) ∧
            ProgressionConditions A (2 * T ^ 2 + 1) H R := by
  obtain ⟨M, hM, hselector⟩ := exists_progression_selector hpos hSQ
  refine ⟨M, hM, ?_⟩
  intro T hT
  obtain ⟨H, R, hH, hR, hden, hprops⟩ := hselector T hT
  exact ⟨H, R, hH, hR, hden, fun u hu => ⟨(hprops u hu).1, (hprops u hu).2.1⟩,
    fun u hu => (hprops u hu).2.2⟩

end SimultaneousPrimitiveRoots

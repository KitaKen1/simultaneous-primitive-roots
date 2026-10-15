module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionGeneric
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SlotMassAll

/-!
# [P] Lemma 7.2 with the class: the summed progression remainders

The three fields of `ExtractionOpenLeaves d H b q q₀` (`Extraction/Open.lean`) that state [P]
Lemma 7.2 (`lem:progressions`, `[P-07:0077–0192]`) with the class `u + 1 ≡ b (mod H)`
(`[PUB-tex:0518–0522]`), for `0 < H`, `(b, H) = 1` and `0 < q < 1`:

* `progressionSlots : MertensReciprocal → ProgressionSlots d H b q`, for every number `d` of slots;
* `progressionUnit : MertensReciprocal → ProgressionUnit H b q`;
* `progressionUnitOne : MertensReciprocal → ProgressionUnit 1 1 q`.

Both forms are instances of `progression_generic` (`Extraction/ProgressionGeneric.lean`); the
auxiliary declarations of the files `Extraction/Progression*.lean` are in the namespace
`Extraction.Progression`.

* **With the long-prime statistic.** The family is the set of the ordered tuples `𝔩` of distinct
  slot primes with `ℓ_𝔩 = ∏_i 𝔩_i`: `f_x(u) = #{𝔩 : ℓ_𝔩 ∣ u}`, `C_x = ∑_𝔩 1/ℓ_𝔩`. The prime factors
  of `ℓ_𝔩` are slot primes, hence `≥ x^ε` with `ε > c₀` ("every `ℓ_i > x^{c₀}`, so `(ℓ, r) = 1`",
  `[P-07:0150–0151]`); there are at most `x^{1-ε} C_x` tuples (`[P-07:0170–0171]`,
  `EndpointProof.card_slotTuples_le`) and `C_x = O_ε(1)` (`EndpointProof.slotMassBounded d`, from
  Chebyshev's bound). So `δ = ε - c₀`. Only `c₀ < ε` is used, not `c₀ < ε/2`.
* **Without tuple factors.** The family is the single integer `1` ("when `f_x = 1`, use `ℓ = 1`
  and the stronger bound `x^{c₀ + o(1)}`", `[P-07:0177–0178]`), with `δ = 1 - c₀`. Only `c₀ < 1`
  is used, not `c₀ < 1/4`.

Differences from the manuscript's proof (see the files `Extraction/Progression*.lean`):

* the expansion of the weights over tuples of divisor primes and Bonferroni's inequalities
  (`[P-07:0096–0138]`) are replaced by the Möbius expansion of an arbitrary bounded function of the
  band primes dividing `u`, truncated at degree `⌊L^{.01}⌋`, with a binomial error envelope of
  degree `⌊L^{.01}⌋ + 1` (`Extraction/ProgressionExpansion.lean`); so the structure of the weight
  and the disjointness of the arrays are not used;
* in (ext:crt-count) the variable is `u` itself (modulus `H r ℓ d'`, dilation `1`), not `y = u/ℓ`
  (`Extraction/ProgressionCount.lean`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-- **[P] Lemma 7.2 with the class, with the long-prime statistic** (`[P-07:0077–0192]`), for
every number of slots: the field `progressionSlots` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem progressionSlots (d H b : ℕ) (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} (hq : 0 < q)
    (hq1 : q < 1) : MertensReciprocal → ProgressionSlots d H b q := by
  intro hM ε hε c₀ hc₀ hc₀ε Φ hΦ n K 𝔄 _ A _
  obtain ⟨Bs, xs, hBs⟩ := EndpointProof.slotMassBounded d ε hε
  have hθ : c₀ < ε := by linarith
  obtain ⟨M, x₀, hgen⟩ := progression_generic H b hH hb hq hq1 hM hc₀ hθ (sub_pos.mpr hθ) hΦ 𝔄
    A (max Bs 0)
  refine ⟨M, max (max x₀ xs) 1, fun x hx a a' S hS => ?_⟩
  have hx₀ : x₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxs : xs ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hmass : slotMass S ≤ max Bs 0 := (hBs x hxs S hS).trans (le_max_left _ _)
  have hpos : ∀ 𝔩 ∈ slotTuples S, 0 < ∏ i, 𝔩 i := fun 𝔩 h𝔩 =>
    (EndpointProof.slotTuple_facts hS h𝔩).2.1
  have hbig : ∀ 𝔩 ∈ slotTuples S, ∀ p : ℕ, p.Prime → p ∣ ∏ i, 𝔩 i → x ^ ε ≤ (p : ℝ) := by
    intro 𝔩 h𝔩 p hp hdvd
    have hmem := (EndpointProof.slotTuple_facts hS h𝔩).1
    obtain ⟨i, -, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime 𝔩).mp hdvd
    have e : p = 𝔩 i := (Nat.prime_dvd_prime_iff_eq hp (hS.prime i _ (hmem i))).mp hpi
    rw [e]
    exact hS.lower i _ (hmem i)
  have hcard : ((slotTuples S).card : ℝ) ≤ max Bs 0 * x ^ (1 - c₀ - (ε - c₀)) := by
    have h1 := EndpointProof.card_slotTuples_le hS
    have hxp : 0 ≤ x ^ (1 - ε) := Real.rpow_nonneg hx0 _
    rw [show (1 - c₀ - (ε - c₀) : ℝ) = 1 - ε by ring]
    calc ((slotTuples S).card : ℝ) ≤ x ^ (1 - ε) * slotMass S := h1
      _ ≤ x ^ (1 - ε) * max Bs 0 := mul_le_mul_of_nonneg_left hmass hxp
      _ = max Bs 0 * x ^ (1 - ε) := mul_comm _ _
  have hgen' : ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => (∑ 𝔩 ∈ slotTuples S, if (∏ i, 𝔩 i) ∣ u then (1 : ℝ) else 0) *
            pairWeight q 𝔄 x a a' u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * slotMass S *
          modelMean (familyPrimes 𝔄 x) (pairWeight q 𝔄 x a a') else 0)| ≤
      M * x * Real.log x ^ (-A) :=
    hgen x hx₀ a a' (Fin d → ℕ) (slotTuples S) (fun 𝔩 => ∏ i, 𝔩 i) hpos hbig hcard hmass
  have hfun : (fun u : ℕ => (slotCount S u : ℝ) * pairWeight q 𝔄 x a a' u) =
      fun u => (∑ 𝔩 ∈ slotTuples S, if (∏ i, 𝔩 i) ∣ u then (1 : ℝ) else 0) *
        pairWeight q 𝔄 x a a' u := by
    funext u
    rw [Finset.sum_boole]
    rfl
  rw [← hfun] at hgen'
  exact hgen'

/-- **[P] Lemma 7.2 with the class, without tuple factors** (`[P-07:0090, 0177–0178]`): the field
`progressionUnit` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem progressionUnit (H b : ℕ) (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} (hq : 0 < q)
    (hq1 : q < 1) : MertensReciprocal → ProgressionUnit H b q := by
  intro hM c₀ hc₀ hc₀4 Φ hΦ n K 𝔄 _ A _
  obtain ⟨M, x₀, hgen⟩ := progression_generic H b hH hb hq hq1 hM hc₀ (lt_add_one c₀)
    (by linarith : (0 : ℝ) < 1 - c₀) hΦ 𝔄 A 1
  refine ⟨M, x₀, fun x hx a a' => ?_⟩
  have hbig : ∀ i ∈ (Finset.univ : Finset Unit), ∀ p : ℕ, p.Prime → p ∣ 1 →
      x ^ (c₀ + 1) ≤ (p : ℝ) :=
    fun _ _ p hp hdvd => absurd (Nat.dvd_one.mp hdvd) hp.ne_one
  have hcard : (((Finset.univ : Finset Unit).card : ℕ) : ℝ) ≤
      1 * x ^ (1 - c₀ - (1 - c₀)) := by
    refine le_of_eq ?_
    rw [show (1 - c₀ - (1 - c₀) : ℝ) = 0 by ring, Real.rpow_zero, Finset.card_univ,
      Fintype.card_unit, Nat.cast_one, one_mul]
  have hone : (∑ _i ∈ (Finset.univ : Finset Unit), 1 / ((1 : ℕ) : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, Nat.cast_one, div_one, one_smul]
  have hgen' : ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => (∑ _i ∈ (Finset.univ : Finset Unit), if 1 ∣ u then (1 : ℝ) else 0) *
            pairWeight q 𝔄 x a a' u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) *
          (∑ _i ∈ (Finset.univ : Finset Unit), 1 / ((1 : ℕ) : ℝ)) *
            modelMean (familyPrimes 𝔄 x) (pairWeight q 𝔄 x a a') else 0)| ≤
      M * x * Real.log x ^ (-A) :=
    hgen x hx a a' Unit Finset.univ (fun _ => 1) (fun _ _ => one_pos) hbig hcard (le_of_eq hone)
  have hfun : (fun u : ℕ =>
      (∑ _i ∈ (Finset.univ : Finset Unit), if 1 ∣ u then (1 : ℝ) else 0) *
        pairWeight q 𝔄 x a a' u) = fun u => 1 * pairWeight q 𝔄 x a a' u := by
    funext u
    rw [if_pos (one_dvd u), Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul]
  rw [hfun, hone] at hgen'
  exact hgen'

/-- **[P] Lemma 7.2 without class and without tuple factors**: the field `progressionUnitOne` of
`ExtractionOpenLeaves d H b q q₀`. -/
theorem progressionUnitOne {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    MertensReciprocal → ProgressionUnit 1 1 q :=
  progressionUnit 1 1 one_pos (Nat.coprime_one_left 1) hq hq1

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# Sanity lemmas for the objects of the extraction

Small proved facts that check the definitions of `Extraction/Objects.lean` against the manuscript
and that the leaves will use. None of them is a hypothesis of the proved chain.

* The model: `modelMean_empty`, `modelMean_nonneg`.
* Arrays: `familyPrimes_single`, the monomials `pairWeight_none_none`, `pairWeight_some_none`,
  `pairWeight_some_some`, and `arrayDeviation_eq`: `Z` is the combination of the monomials
  `1, 𝒲_a, 𝒲_a 𝒲_{a'}` with coefficients `1, -2/(n m_a), 1/(n² m_a m_{a'})`
  (`[P-07:0637–0640, 0649–0651]`).
* Coins: `coinProb_nonneg`, `coinWeight_nonneg`, `failedMass_nonneg`, `retainedMass_nonneg`,
  `failedMass_le_one`, and the expansion of the failure factors (ext:active-term)
  `[P-07:0525–0530]`: `coinWeight_expand`, `retainedMass_expand`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-! ### The model -/

/-- With no primes the model is the evaluation at `1`. -/
theorem modelMean_empty (F : ℕ → ℝ) : modelMean ∅ F = F 1 := by
  unfold modelMean
  rw [Finset.powerset_empty, Finset.sum_singleton]
  simp

/-- The model expectation of a nonnegative function is nonnegative (the weights
`∏_{p ∈ T} 1/p · ∏_{p ∉ T} (1 - 1/p)` are nonnegative when `P` consists of positive integers). -/
theorem modelMean_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) :
    0 ≤ modelMean P F := by
  unfold modelMean
  refine Finset.sum_nonneg fun T _ => ?_
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p _ => by positivity)
    (Finset.prod_nonneg fun p hp => ?_)) (hF _)
  have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hpP
  have h2 : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr h1
  linarith

/-! ### Arrays and monomials -/

/-- The primes of the family consisting of one array are the primes of the array. -/
theorem familyPrimes_single {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) :
    familyPrimes (fun _ : Fin 1 => 𝔞) x = arrayPrimes 𝔞 x := by
  unfold familyPrimes
  rw [Finset.univ_unique, Finset.singleton_biUnion]

theorem pairWeight_none_none (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (u : ℕ) :
    pairWeight q 𝔄 x none none u = 1 := by
  simp [pairWeight, optWeight]

theorem pairWeight_some_none (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ)
    (a : Fin n) (u : ℕ) : pairWeight q 𝔄 x (some a) none u = markedWeight q (𝔄 a) x u := by
  simp [pairWeight, optWeight]

theorem pairWeight_some_some (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ)
    (a a' : Fin n) (u : ℕ) :
    pairWeight q 𝔄 x (some a) (some a') u =
      markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u := by
  simp [pairWeight, optWeight]

theorem arrayDeviation_nonneg (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (u : ℕ) :
    0 ≤ arrayDeviation q 𝔄 x u := by
  unfold arrayDeviation
  exact sq_nonneg _

/-- **`Z` as a combination of the monomials of Lemma 7.2** (`[P-07:0649–0651]`: "the square and
all its cross terms lie within Lemma 7.2"), with the coefficients `1`, `-2/(n m_a)` and
`1/(n² m_a m_{a'})`. No hypothesis on `n` or on the `m_a` is needed (division by zero is `0` on
both sides). -/
theorem arrayDeviation_eq (q : ℝ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K) (x : ℝ) (u : ℕ) :
    arrayDeviation q 𝔄 x u =
      pairWeight q 𝔄 x none none u -
        2 / (n : ℝ) * ∑ a, 1 / arrayMean q (𝔄 a) x * pairWeight q 𝔄 x (some a) none u +
        1 / (n : ℝ) ^ 2 * ∑ a, ∑ a', 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
          pairWeight q 𝔄 x (some a) (some a') u := by
  have h1 : ∑ a, 1 / arrayMean q (𝔄 a) x * pairWeight q 𝔄 x (some a) none u =
      ∑ a, normWeight q (𝔄 a) x u :=
    Finset.sum_congr rfl fun a _ => by
      rw [pairWeight_some_none]
      unfold normWeight
      ring
  have h2 : ∑ a, ∑ a', 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
      pairWeight q 𝔄 x (some a) (some a') u = (∑ a, normWeight q (𝔄 a) x u) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [pairWeight_some_some]
    unfold normWeight
    ring
  rw [h1, h2, pairWeight_none_none]
  unfold arrayDeviation
  ring

/-! ### Coins -/

theorem coinProb_nonneg (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (hc₁ : 0 ≤ c₁) (hq₀ : 0 ≤ q₀) (j u : ℕ)
    (g : 𝔊.Index) : 0 ≤ coinProb 𝔊 c₁ q₀ j u g := by
  unfold coinProb
  exact mul_nonneg (mul_nonneg hc₁ (markFactor_nonneg hq₀ _ _))
    (markFactor_nonneg (div_nonneg hq₀ (Nat.cast_nonneg j)) _ _)

theorem coinWeight_nonneg (𝔊 : ActiveGroups) {s : 𝔊.Index → ℝ} (h0 : ∀ g, 0 ≤ s g)
    (h1 : ∀ g, s g ≤ 1) (S : Finset 𝔊.Index) : 0 ≤ coinWeight 𝔊 s S := by
  unfold coinWeight
  exact mul_nonneg (Finset.prod_nonneg fun g _ => h0 g)
    (Finset.prod_nonneg fun g _ => sub_nonneg.mpr (h1 g))

/-- If the coin probabilities at `u` are in `[0, 1]`, the failed mass is nonnegative. -/
theorem failedMass_nonneg (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (c₂ : ℝ) {j : ℕ} (x : ℝ) {u : ℕ}
    (h0 : ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j u g) (h1 : ∀ g, coinProb 𝔊 c₁ q₀ j u g ≤ 1) :
    0 ≤ failedMass 𝔊 c₁ c₂ q₀ j x u := by
  unfold failedMass
  exact Finset.sum_nonneg fun S _ => coinWeight_nonneg 𝔊 h0 h1 S

/-- If the coin probabilities at `u` are in `[0, 1]`, the retained mass is nonnegative. -/
theorem retainedMass_nonneg (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (c₂ : ℝ) {j : ℕ} (x : ℝ) {u : ℕ}
    (h0 : ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j u g) (h1 : ∀ g, coinProb 𝔊 c₁ q₀ j u g ≤ 1) :
    0 ≤ retainedMass 𝔊 c₁ c₂ q₀ j x u := by
  unfold retainedMass
  exact Finset.sum_nonneg fun S _ => coinWeight_nonneg 𝔊 h0 h1 S

/-- The failed mass is a probability. -/
theorem failedMass_le_one (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (c₂ : ℝ) {j : ℕ} (x : ℝ) {u : ℕ}
    (h0 : ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j u g) (h1 : ∀ g, coinProb 𝔊 c₁ q₀ j u g ≤ 1) :
    failedMass 𝔊 c₁ c₂ q₀ j x u ≤ 1 := by
  have hsum := retainedMass_add_failedMass 𝔊 c₁ c₂ q₀ j x u
  have hret := retainedMass_nonneg 𝔊 c₂ x h0 h1
  linarith

/-- **Expansion of the failure factors** (`[P-07:0525–0530]`, (ext:active-term)):
`∏_{g ∈ S} s_g ∏_{g ∉ S} (1 - s_g) = ∑_{T ⊆ 𝒞 ∖ S} (-1)^{|T|} ∏_{g ∈ S ∪ T} s_g`. -/
theorem coinWeight_expand (𝔊 : ActiveGroups) (s : 𝔊.Index → ℝ) (S : Finset 𝔊.Index) :
    coinWeight 𝔊 s S = ∑ T ∈ Sᶜ.powerset, (-1) ^ T.card * ∏ g ∈ S ∪ T, s g := by
  have hexp : ∏ g ∈ Sᶜ, (1 - s g) = ∑ T ∈ Sᶜ.powerset, (-1) ^ T.card * ∏ g ∈ T, s g := by
    have h := Finset.prod_add (fun g => -s g) (fun _ => (1 : ℝ)) Sᶜ
    have h1 : ∏ g ∈ Sᶜ, (1 - s g) = ∏ g ∈ Sᶜ, (-s g + 1) :=
      Finset.prod_congr rfl fun g _ => by ring
    rw [h1, h]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
  unfold coinWeight
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hdisj : Disjoint S T :=
    Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) disjoint_compl_right
  rw [Finset.prod_union hdisj]
  ring

/-- The retained mass as a signed sum of products over the active sets `P = S ∪ T`
(`[P-07:0524–0530]`); there are at most `3^{|𝒞|}` terms. -/
theorem retainedMass_expand (𝔊 : ActiveGroups) (c₁ c₂ q₀ : ℝ) (j : ℕ) (x : ℝ) (u : ℕ) :
    retainedMass 𝔊 c₁ c₂ q₀ j x u =
      ∑ S ∈ goodSets 𝔊 c₂ x, ∑ T ∈ Sᶜ.powerset,
        (-1) ^ T.card * ∏ g ∈ S ∪ T, coinProb 𝔊 c₁ q₀ j u g := by
  unfold retainedMass
  exact Finset.sum_congr rfl fun S _ => coinWeight_expand 𝔊 _ S

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

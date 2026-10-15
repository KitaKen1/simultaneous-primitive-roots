module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# Truncated divisor expansions with a binomial envelope

The combinatorial part of [P] Lemma 7.2 (`[P-07:0095–0146]`). The manuscript expands the array
weights over tuples of divisor primes and truncates the remaining product by Bonferroni's
inequalities. Here the same truncation is done for an arbitrary bounded function `F` of the set of
the marked primes dividing `u`, by Möbius inversion on the Boolean lattice:

* `moebiusReal F D = ∑_{D' ⊆ D} (-1)^{|D ∖ D'|} F(D')`, with `|a(D)| ≤ 2^{|D|} sup |F|`
  (`abs_moebiusReal_le`) and `a_F(D ∪ {p}) = a_{Δ_p F}(D)` for the difference
  `Δ_p F(T) = F(T ∪ {p}) - F(T)` (`moebiusReal_insert`).
* `truncExpansion k F T = ∑_{D ⊆ T, |D| < k} a(D)`, the expansion through degree `k - 1`.
* **The envelope** (`abs_sub_truncExpansion_le`): `|F(T) - truncExpansion k F T| ≤ 2^k sup|F| ·
  #{E ⊆ T : |E| = k}`. This replaces "Bonferroni inequalities … bound the error in absolute value
  by the nonnegative term of degree `h_0 + 1`" (`[P-07:0127–0129]`): the error envelope is a
  nonnegative divisor sum of degree exactly `k`. The proof is the induction
  `E_{k+1}(F, T ∪ {p}) = E_{k+1}(F, T) + E_k(Δ_p F, T)` and Pascal's rule.
* `abs_weighted_sub_truncated_le`: the same for a weighted sum `∑_i w_i F(S_i)`, `w_i ≥ 0`.
* `modelWeight P T`: the probability of the configuration `T` in the independent model
  (`modelMean_eq_sum_modelWeight`); `sum_modelWeight_superset`: the probability that all the primes
  of `D` divide is `∏_{p ∈ D} 1/p`.
* **Comparison** (`abs_weighted_sub_model_le`): if the weighted counts
  `∑_{i : D ⊆ S_i} w_i` are `X ∏_{p ∈ D} 1/p + O(C')` for all `D ⊆ P` with `|D| ≤ k`, then
  `∑_i w_i F(S_i) = X · M_P(F) + O(sup|F| · (C' · #terms + X · tail))`.
* Rankin's bounds for the two error terms (`sum_two_pow_card_le`, `sum_powersetCard_prod_le`,
  `prod_one_add_div_le_exp_mul`).

The auxiliary declarations of the proof of Lemma 7.2 (this file and the other files
`Extraction/Progression*.lean`) are in the namespace `Extraction.Progression`; the statements for
the fields of `ExtractionOpenLeaves` are in `Extraction/ProgressionSlotsProof.lean`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

noncomputable section

/-! ### Möbius inversion on the subsets of a finite set -/

theorem insert_sdiff_insert_of_notMem {p : ℕ} {D D' : Finset ℕ} (hp : p ∉ D) :
    insert p D \ insert p D' = D \ D' := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Or.inr h1, ?_⟩
    rintro (h | h)
    · rw [h] at h1
      exact hp h1
    · exact h2 h

/-- The Möbius inverse of a real set function on the Boolean lattice:
`a(D) = ∑_{D' ⊆ D} (-1)^{|D ∖ D'|} F(D')`. -/
def moebiusReal (F : Finset ℕ → ℝ) (D : Finset ℕ) : ℝ :=
  ∑ D' ∈ D.powerset, (-1 : ℝ) ^ (D \ D').card * F D'

theorem moebiusReal_empty (F : Finset ℕ → ℝ) : moebiusReal F ∅ = F ∅ := by
  unfold moebiusReal
  rw [Finset.powerset_empty, Finset.sum_singleton, Finset.sdiff_self, Finset.card_empty, pow_zero,
    one_mul]

/-- `a_F(D ∪ {p}) = a_{Δ_p F}(D)` with `Δ_p F(T) = F(T ∪ {p}) - F(T)`. -/
theorem moebiusReal_insert (F : Finset ℕ → ℝ) {p : ℕ} {D : Finset ℕ} (hp : p ∉ D) :
    moebiusReal F (insert p D) = moebiusReal (fun T => F (insert p T) - F T) D := by
  unfold moebiusReal
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun D' hD' => ?_
  have hD'D : D' ⊆ D := Finset.mem_powerset.mp hD'
  have hpD' : p ∉ D' := fun h => hp (hD'D h)
  have hpd : p ∉ D \ D' := fun h => hp (Finset.mem_sdiff.mp h).1
  rw [Finset.insert_sdiff_of_notMem D hpD', insert_sdiff_insert_of_notMem hp,
    Finset.card_insert_of_notMem hpd, pow_succ]
  ring

/-- `|a(D)| ≤ 2^{|D|} H_b` when `|F| ≤ H_b` on the subsets of `D`. -/
theorem abs_moebiusReal_le {F : Finset ℕ → ℝ} {Hb : ℝ} {D : Finset ℕ}
    (hF : ∀ D' ⊆ D, |F D'| ≤ Hb) : |moebiusReal F D| ≤ 2 ^ D.card * Hb := by
  unfold moebiusReal
  calc |∑ D' ∈ D.powerset, (-1 : ℝ) ^ (D \ D').card * F D'|
      ≤ ∑ D' ∈ D.powerset, |(-1 : ℝ) ^ (D \ D').card * F D'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _D' ∈ D.powerset, Hb := Finset.sum_le_sum fun D' hD' => by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact hF D' (Finset.mem_powerset.mp hD')
    _ = 2 ^ D.card * Hb := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-! ### The truncated expansion -/

/-- The divisor expansion of `F` through degree `k - 1`: `∑_{D ⊆ T, |D| < k} a(D)`. -/
def truncExpansion (k : ℕ) (F : Finset ℕ → ℝ) (T : Finset ℕ) : ℝ :=
  ∑ D ∈ T.powerset.filter (fun D => D.card < k), moebiusReal F D

theorem truncExpansion_zero (F : Finset ℕ → ℝ) (T : Finset ℕ) : truncExpansion 0 F T = 0 := by
  unfold truncExpansion
  exact Finset.sum_eq_zero fun D hD => absurd (Finset.mem_filter.mp hD).2 (Nat.not_lt_zero _)

theorem truncExpansion_succ_empty (k : ℕ) (F : Finset ℕ → ℝ) :
    truncExpansion (k + 1) F ∅ = F ∅ := by
  unfold truncExpansion
  have h : (∅ : Finset ℕ).powerset.filter (fun D => D.card < k + 1) = {∅} := by
    rw [Finset.powerset_empty]
    refine Finset.filter_true_of_mem fun D hD => ?_
    rw [Finset.mem_singleton.mp hD, Finset.card_empty]
    exact Nat.succ_pos k
  rw [h, Finset.sum_singleton, moebiusReal_empty]

/-- The recursion of the truncated expansion: the subsets of `T ∪ {p}` either avoid `p` or are
`D ∪ {p}` with one element fewer. -/
theorem truncExpansion_succ_insert (k : ℕ) (F : Finset ℕ → ℝ) {p : ℕ} {T : Finset ℕ}
    (hp : p ∉ T) :
    truncExpansion (k + 1) F (insert p T) =
      truncExpansion (k + 1) F T + truncExpansion k (fun D => F (insert p D) - F D) T := by
  unfold truncExpansion
  simp only [Finset.sum_filter]
  rw [Finset.sum_powerset_insert hp]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun D hD => ?_)
  have hpD : p ∉ D := fun h => hp (Finset.mem_powerset.mp hD h)
  rw [Finset.card_insert_of_notMem hpD, moebiusReal_insert F hpD]
  by_cases h : D.card < k
  · rw [if_pos h, if_pos (by omega : D.card + 1 < k + 1)]
  · rw [if_neg h, if_neg (by omega : ¬ D.card + 1 < k + 1)]

/-- **The binomial envelope of the truncation**: if `|F| ≤ H_b` on the subsets of `T`, then
`|F(T) - ∑_{D ⊆ T, |D| < k} a(D)| ≤ 2^k H_b C(|T|, k)`. -/
theorem abs_sub_truncExpansion_le (T : Finset ℕ) :
    ∀ (k : ℕ) (F : Finset ℕ → ℝ) (Hb : ℝ), (∀ D ⊆ T, |F D| ≤ Hb) →
      |F T - truncExpansion k F T| ≤ 2 ^ k * Hb * (T.card.choose k : ℝ) := by
  induction T using Finset.induction_on with
  | empty =>
    intro k F Hb hF
    have h0 : |F ∅| ≤ Hb := hF ∅ (Finset.Subset.refl _)
    have hHb : 0 ≤ Hb := (abs_nonneg _).trans h0
    cases k with
    | zero =>
      rw [truncExpansion_zero, sub_zero, pow_zero, one_mul, Finset.card_empty,
        Nat.choose_zero_right, Nat.cast_one, mul_one]
      exact h0
    | succ k =>
      rw [truncExpansion_succ_empty, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) hHb) (Nat.cast_nonneg _)
  | @insert p T hp ih =>
    intro k F Hb hF
    cases k with
    | zero =>
      rw [truncExpansion_zero, sub_zero, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
        mul_one]
      exact hF _ (Finset.Subset.refl _)
    | succ k =>
      have hF1 : ∀ D ⊆ T, |F D| ≤ Hb := fun D hD => hF D (hD.trans (Finset.subset_insert p T))
      have hF2 : ∀ D ⊆ T, |F (insert p D) - F D| ≤ 2 * Hb := fun D hD => by
        have h1 := hF (insert p D) (Finset.insert_subset_insert p hD)
        have h2 := hF1 D hD
        have h3 := abs_sub (F (insert p D)) (F D)
        linarith
      have e1 := ih (k + 1) F Hb hF1
      have e2 := ih k (fun D => F (insert p D) - F D) (2 * Hb) hF2
      have hsplit : F (insert p T) -
          (truncExpansion (k + 1) F T + truncExpansion k (fun D => F (insert p D) - F D) T) =
          (F T - truncExpansion (k + 1) F T) +
            ((F (insert p T) - F T) - truncExpansion k (fun D => F (insert p D) - F D) T) := by
        ring
      rw [truncExpansion_succ_insert k F hp, hsplit, Finset.card_insert_of_notMem hp,
        Nat.choose_succ_succ', Nat.cast_add]
      calc |(F T - truncExpansion (k + 1) F T) +
            ((F (insert p T) - F T) - truncExpansion k (fun D => F (insert p D) - F D) T)|
          ≤ |F T - truncExpansion (k + 1) F T| +
            |(F (insert p T) - F T) - truncExpansion k (fun D => F (insert p D) - F D) T| :=
            abs_add_le _ _
        _ ≤ 2 ^ (k + 1) * Hb * (T.card.choose (k + 1) : ℝ) +
            2 ^ k * (2 * Hb) * (T.card.choose k : ℝ) := add_le_add e1 e2
        _ = 2 ^ (k + 1) * Hb * ((T.card.choose k : ℝ) + (T.card.choose (k + 1) : ℝ)) := by
            ring

/-! ### Weighted sums -/

/-- `∑_{D ⊆ P, |D| < k, D ⊆ S} c(D) = ∑_{D ⊆ S, |D| < k} c(D)` for `S ⊆ P`. -/
theorem sum_filter_card_lt_subset {P S : Finset ℕ} (hS : S ⊆ P) (k : ℕ) (c : Finset ℕ → ℝ) :
    ∑ D ∈ P.powerset.filter (fun D => D.card < k), (if D ⊆ S then c D else 0) =
      ∑ D ∈ S.powerset.filter (fun D => D.card < k), c D := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.trans hS, h2⟩, h1⟩

/-- `C(|S|, k) = #{E ⊆ P : |E| = k, E ⊆ S}` for `S ⊆ P`. -/
theorem choose_card_eq_sum {P S : Finset ℕ} (hS : S ⊆ P) (k : ℕ) :
    (S.card.choose k : ℝ) = ∑ E ∈ P.powersetCard k, (if E ⊆ S then (1 : ℝ) else 0) := by
  have h : (P.powersetCard k).filter (fun E => E ⊆ S) = S.powersetCard k := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans hS, h2⟩, h1⟩
  rw [Finset.sum_boole, h, Finset.card_powersetCard]

/-- **The truncated expansion of a weighted sum**: for weights `w_i ≥ 0` and sets `S_i ⊆ P`,
`|∑_i w_i F(S_i) - ∑_{D ⊆ P, |D| < k} a(D) ∑_{i : D ⊆ S_i} w_i|
  ≤ 2^k H_b ∑_{E ⊆ P, |E| = k} ∑_{i : E ⊆ S_i} w_i`. -/
theorem abs_weighted_sub_truncated_le {ι : Type*} (I : Finset ι) (w : ι → ℝ)
    (S : ι → Finset ℕ) (P : Finset ℕ) (k : ℕ) (F : Finset ℕ → ℝ) (Hb : ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hS : ∀ i ∈ I, S i ⊆ P) (hF : ∀ D ⊆ P, |F D| ≤ Hb) :
    |∑ i ∈ I, w i * F (S i) -
        ∑ D ∈ P.powerset.filter (fun D => D.card < k),
          moebiusReal F D * ∑ i ∈ I, (if D ⊆ S i then w i else 0)| ≤
      2 ^ k * Hb * ∑ E ∈ P.powersetCard k, ∑ i ∈ I, (if E ⊆ S i then w i else 0) := by
  have hmain : ∑ D ∈ P.powerset.filter (fun D => D.card < k),
      moebiusReal F D * ∑ i ∈ I, (if D ⊆ S i then w i else 0) =
      ∑ i ∈ I, w i * truncExpansion k F (S i) := by
    calc ∑ D ∈ P.powerset.filter (fun D => D.card < k),
          moebiusReal F D * ∑ i ∈ I, (if D ⊆ S i then w i else 0)
        = ∑ D ∈ P.powerset.filter (fun D => D.card < k),
            ∑ i ∈ I, (if D ⊆ S i then w i * moebiusReal F D else 0) :=
          Finset.sum_congr rfl fun D _ => by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : D ⊆ S i
            · rw [if_pos h, if_pos h, mul_comm]
            · rw [if_neg h, if_neg h, mul_zero]
      _ = ∑ i ∈ I, ∑ D ∈ P.powerset.filter (fun D => D.card < k),
            (if D ⊆ S i then w i * moebiusReal F D else 0) := Finset.sum_comm
      _ = ∑ i ∈ I, w i * truncExpansion k F (S i) :=
          Finset.sum_congr rfl fun i hi => by
            rw [sum_filter_card_lt_subset (hS i hi) k (fun D => w i * moebiusReal F D)]
            unfold truncExpansion
            rw [Finset.mul_sum]
  have hE : ∀ i ∈ I, ∑ E ∈ P.powersetCard k, (if E ⊆ S i then w i else 0) =
      w i * ((S i).card.choose k : ℝ) := by
    intro i hi
    rw [choose_card_eq_sum (hS i hi) k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    by_cases h : E ⊆ S i
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hmain, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ I, (w i * F (S i) - w i * truncExpansion k F (S i))|
      ≤ ∑ i ∈ I, |w i * F (S i) - w i * truncExpansion k F (S i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, 2 ^ k * Hb * (w i * ((S i).card.choose k : ℝ)) :=
        Finset.sum_le_sum fun i hi => by
          have h1 := abs_sub_truncExpansion_le (S i) k F Hb
            (fun D hD => hF D (hD.trans (hS i hi)))
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
          calc w i * |F (S i) - truncExpansion k F (S i)|
              ≤ w i * (2 ^ k * Hb * ((S i).card.choose k : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 (hw i hi)
            _ = 2 ^ k * Hb * (w i * ((S i).card.choose k : ℝ)) := by ring
    _ = 2 ^ k * Hb * ∑ E ∈ P.powersetCard k, ∑ i ∈ I, (if E ⊆ S i then w i else 0) := by
        rw [Finset.sum_comm, Finset.sum_congr rfl hE, Finset.mul_sum]

/-! ### The independent model as a weighted sum -/

/-- The probability of the configuration `T ⊆ P` in the independent divisor model on `P`. -/
def modelWeight (P T : Finset ℕ) : ℝ :=
  (∏ p ∈ T, (1 / (p : ℝ))) * ∏ p ∈ P \ T, (1 - 1 / (p : ℝ))

theorem modelMean_eq_sum_modelWeight (P : Finset ℕ) (G : ℕ → ℝ) :
    modelMean P G = ∑ T ∈ P.powerset, modelWeight P T * G (∏ p ∈ T, p) :=
  rfl

theorem modelWeight_nonneg {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) (T : Finset ℕ) :
    0 ≤ modelWeight P T := by
  unfold modelWeight
  refine mul_nonneg (Finset.prod_nonneg fun p _ => by positivity)
    (Finset.prod_nonneg fun p hp => ?_)
  have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hpP
  have h2 : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr h1
  linarith

/-- The model is a probability. -/
theorem sum_modelWeight (P : Finset ℕ) : ∑ T ∈ P.powerset, modelWeight P T = 1 :=
  calc ∑ T ∈ P.powerset, modelWeight P T
      = ∑ T ∈ P.powerset, modelWeight P T * 1 :=
        Finset.sum_congr rfl fun _ _ => (mul_one _).symm
    _ = modelMean P (fun _ => (1 : ℝ)) := rfl
    _ = 1 := modelMean_const P 1

/-- **The marginals of the model**: the probability that all the primes of `D ⊆ P` divide is
`∏_{p ∈ D} 1/p`. -/
theorem sum_modelWeight_superset {P D : Finset ℕ} (hD : D ⊆ P) :
    ∑ T ∈ P.powerset, (if D ⊆ T then modelWeight P T else 0) = ∏ p ∈ D, (1 / (p : ℝ)) := by
  rw [← Finset.sum_filter]
  have hre : ∑ T ∈ P.powerset.filter (fun T => D ⊆ T), modelWeight P T =
      ∑ E ∈ (P \ D).powerset, (∏ p ∈ D, (1 / (p : ℝ))) * modelWeight (P \ D) E := by
    refine Finset.sum_nbij' (fun T => T \ D) (fun E => E ∪ D) ?_ ?_ ?_ ?_ ?_
    · intro T hT
      have h1 : T ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff h1 (Finset.Subset.refl D))
    · intro E hE
      have hE' : E ⊆ P \ D := Finset.mem_powerset.mp hE
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.union_subset (hE'.trans Finset.sdiff_subset) hD),
          Finset.subset_union_right⟩
    · intro T hT
      exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp hT).2
    · intro E hE
      have hE' : E ⊆ P \ D := Finset.mem_powerset.mp hE
      have hdisj : Disjoint E D := Finset.disjoint_of_subset_left hE' Finset.sdiff_disjoint
      exact Finset.union_sdiff_cancel_right hdisj
    · intro T hT
      have hDT : D ⊆ T := (Finset.mem_filter.mp hT).2
      have h1 : ∏ p ∈ T, (1 / (p : ℝ)) =
          (∏ p ∈ T \ D, (1 / (p : ℝ))) * ∏ p ∈ D, (1 / (p : ℝ)) :=
        (Finset.prod_sdiff hDT).symm
      have h2 : (P \ D) \ (T \ D) = P \ T := by
        ext a
        simp only [Finset.mem_sdiff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, fun h => h3 ⟨h, h2⟩⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun h => h2 (hDT h)⟩, fun h => h2 h.1⟩
      show modelWeight P T = (∏ p ∈ D, (1 / (p : ℝ))) * modelWeight (P \ D) (T \ D)
      unfold modelWeight
      rw [h1, h2]
      ring
  rw [hre, ← Finset.mul_sum, sum_modelWeight, mul_one]

/-! ### Comparison of a weighted sum with the model -/

/-- **Comparison with the model.** Let `w_i ≥ 0` be weights and `S_i ⊆ P` sets, and suppose the
weighted counts of the supersets of every `D ⊆ P`, `|D| ≤ k`, are `X ∏_{p ∈ D} 1/p` up to `C'`.
Then for `|F| ≤ H_b`,

`|∑_i w_i F(S_i) - X M_P(F)| ≤ H_b (C' (∑_{|D| < k} 2^{|D|} + ∑_{|E| = k} 2^{|E|})
    + 2 X ∑_{|E| = k} ∏_{p ∈ E} 2/p)`. -/
theorem abs_weighted_sub_model_le {ι : Type*} (I : Finset ι) (w : ι → ℝ) (S : ι → Finset ℕ)
    (P : Finset ℕ) (k : ℕ) (F : Finset ℕ → ℝ) (Hb X C' : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hw : ∀ i ∈ I, 0 ≤ w i) (hS : ∀ i ∈ I, S i ⊆ P)
    (hF : ∀ D ⊆ P, |F D| ≤ Hb) (hX : 0 ≤ X)
    (hcount : ∀ D ⊆ P, D.card ≤ k →
      |∑ i ∈ I, (if D ⊆ S i then w i else 0) - X * ∏ p ∈ D, (1 / (p : ℝ))| ≤ C') :
    |∑ i ∈ I, w i * F (S i) - X * ∑ T ∈ P.powerset, modelWeight P T * F T| ≤
      Hb * (C' * (∑ D ∈ P.powerset.filter (fun D => D.card < k), (2 : ℝ) ^ D.card +
          ∑ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card) +
        2 * X * ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ))) := by
  have hHb : 0 ≤ Hb := (abs_nonneg _).trans (hF ∅ (Finset.empty_subset P))
  have h1 := abs_weighted_sub_truncated_le I w S P k F Hb hw hS hF
  have h2 : |∑ T ∈ P.powerset, modelWeight P T * F T -
        ∑ D ∈ P.powerset.filter (fun D => D.card < k),
          moebiusReal F D * ∑ T ∈ P.powerset, (if D ⊆ T then modelWeight P T else 0)| ≤
      2 ^ k * Hb * ∑ E ∈ P.powersetCard k, ∑ T ∈ P.powerset,
        (if E ⊆ T then modelWeight P T else 0) :=
    abs_weighted_sub_truncated_le P.powerset (modelWeight P) (fun T => T) P k F Hb
      (fun T _ => modelWeight_nonneg hP T) (fun _ hT => Finset.mem_powerset.mp hT) hF
  have hD𝒟 : ∀ D ∈ P.powerset.filter (fun D => D.card < k), D ⊆ P ∧ D.card ≤ k := fun D hD =>
    ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1, (Finset.mem_filter.mp hD).2.le⟩
  have hEℰ : ∀ E ∈ P.powersetCard k, E ⊆ P ∧ E.card = k := fun E hE =>
    Finset.mem_powersetCard.mp hE
  -- the marginals of the model
  have hm1 : ∑ D ∈ P.powerset.filter (fun D => D.card < k),
      moebiusReal F D * ∑ T ∈ P.powerset, (if D ⊆ T then modelWeight P T else 0) =
      ∑ D ∈ P.powerset.filter (fun D => D.card < k),
        moebiusReal F D * ∏ p ∈ D, (1 / (p : ℝ)) :=
    Finset.sum_congr rfl fun D hD => by rw [sum_modelWeight_superset (hD𝒟 D hD).1]
  have hm2 : ∑ E ∈ P.powersetCard k, ∑ T ∈ P.powerset, (if E ⊆ T then modelWeight P T else 0) =
      ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (1 / (p : ℝ)) :=
    Finset.sum_congr rfl fun E hE => sum_modelWeight_superset (hEℰ E hE).1
  rw [hm1, hm2] at h2
  -- abbreviations
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i ∈ I, w i * F (S i) := ⟨_, rfl⟩
  obtain ⟨Mo, hMo⟩ : ∃ Mo : ℝ, Mo = ∑ T ∈ P.powerset, modelWeight P T * F T := ⟨_, rfl⟩
  obtain ⟨Tw, hTw⟩ : ∃ Tw : ℝ, Tw = ∑ D ∈ P.powerset.filter (fun D => D.card < k),
      moebiusReal F D * ∑ i ∈ I, (if D ⊆ S i then w i else 0) := ⟨_, rfl⟩
  obtain ⟨Tm, hTm⟩ : ∃ Tm : ℝ, Tm = ∑ D ∈ P.powerset.filter (fun D => D.card < k),
      moebiusReal F D * ∏ p ∈ D, (1 / (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Ew, hEw⟩ : ∃ Ew : ℝ, Ew = ∑ E ∈ P.powersetCard k,
      ∑ i ∈ I, (if E ⊆ S i then w i else 0) := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : ℝ, Em = ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (1 / (p : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℝ, N1 = ∑ D ∈ P.powerset.filter (fun D => D.card < k),
      (2 : ℝ) ^ D.card := ⟨_, rfl⟩
  rw [← hA, ← hTw, ← hEw] at h1
  rw [← hMo, ← hTm, ← hEm] at h2
  rw [← hA, ← hMo, ← hN1]
  -- the truncated sums
  have hmid : |Tw - X * Tm| ≤ Hb * (C' * N1) := by
    have e : Tw - X * Tm = ∑ D ∈ P.powerset.filter (fun D => D.card < k),
        moebiusReal F D * (∑ i ∈ I, (if D ⊆ S i then w i else 0) -
          X * ∏ p ∈ D, (1 / (p : ℝ))) := by
      rw [hTw, hTm, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun D _ => by ring
    rw [e, hN1, Finset.mul_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun D hD => ?_)
    obtain ⟨hDP, hDk⟩ := hD𝒟 D hD
    have ha : |moebiusReal F D| ≤ 2 ^ D.card * Hb :=
      abs_moebiusReal_le fun D' hD' => hF D' (hD'.trans hDP)
    have hc := hcount D hDP hDk
    rw [abs_mul]
    calc |moebiusReal F D| * |∑ i ∈ I, (if D ⊆ S i then w i else 0) -
          X * ∏ p ∈ D, (1 / (p : ℝ))|
        ≤ 2 ^ D.card * Hb * C' :=
          mul_le_mul ha hc (abs_nonneg _) (mul_nonneg (pow_nonneg zero_le_two _) hHb)
      _ = Hb * (C' * 2 ^ D.card) := by ring
  -- the envelope of the count
  have hEw' : Ew ≤ X * Em + C' * ((P.powersetCard k).card : ℝ) := by
    have e : X * Em + C' * ((P.powersetCard k).card : ℝ) =
        ∑ E ∈ P.powersetCard k, (X * ∏ p ∈ E, (1 / (p : ℝ)) + C') := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hEm, Finset.mul_sum]
      ring
    rw [e, hEw]
    refine Finset.sum_le_sum fun E hE => ?_
    obtain ⟨hEP, hEk⟩ := hEℰ E hE
    have hc := (abs_le.mp (hcount E hEP hEk.le)).2
    linarith
  have hcard : ∑ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card =
      2 ^ k * ((P.powersetCard k).card : ℝ) := by
    have h : ∀ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card = 2 ^ k := fun E hE => by
      rw [(hEℰ E hE).2]
    rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hprod : ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ)) = 2 ^ k * Em := by
    rw [hEm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [← (hEℰ E hE).2, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hcard, hprod]
  have hEm0 : 0 ≤ Em := by
    rw [hEm]
    exact Finset.sum_nonneg fun E _ => Finset.prod_nonneg fun p _ => by positivity
  have h2k : (0 : ℝ) ≤ 2 ^ k * Hb := mul_nonneg (pow_nonneg zero_le_two _) hHb
  have hkey : A - X * Mo = (A - Tw) + (Tw - X * Tm) - X * (Mo - Tm) := by ring
  have h3 : |X * (Mo - Tm)| ≤ X * (2 ^ k * Hb * Em) := by
    rw [abs_mul, abs_of_nonneg hX]
    exact mul_le_mul_of_nonneg_left h2 hX
  have h4 : 2 ^ k * Hb * Ew ≤ 2 ^ k * Hb * (X * Em + C' * ((P.powersetCard k).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hEw' h2k
  calc |A - X * Mo| = |(A - Tw) + (Tw - X * Tm) - X * (Mo - Tm)| := by rw [hkey]
    _ ≤ |(A - Tw) + (Tw - X * Tm)| + |X * (Mo - Tm)| := abs_sub _ _
    _ ≤ |A - Tw| + |Tw - X * Tm| + |X * (Mo - Tm)| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 2 ^ k * Hb * (X * Em + C' * ((P.powersetCard k).card : ℝ)) + Hb * (C' * N1) +
          X * (2 ^ k * Hb * Em) := add_le_add (add_le_add (h1.trans h4) hmid) h3
    _ = Hb * (C' * (N1 + 2 ^ k * ((P.powersetCard k).card : ℝ)) + 2 * X * (2 ^ k * Em)) := by
        ring

/-! ### Rankin's bounds -/

/-- `∏_{p ∈ T} (1 + c/p) ≤ exp(c V_T)` for `c ≥ 0`. -/
theorem prod_one_add_div_le_exp_mul (T : Finset ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∏ p ∈ T, (1 + c / (p : ℝ)) ≤ Real.exp (c * reciprocalMass T) := by
  unfold reciprocalMass
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
  · have h : 0 ≤ c / (p : ℝ) := div_nonneg hc (Nat.cast_nonneg p)
    linarith
  · calc 1 + c / (p : ℝ) = c * (1 / (p : ℝ)) + 1 := by ring
      _ ≤ Real.exp (c * (1 / (p : ℝ))) := Real.add_one_le_exp _

/-- **The number of terms** (Rankin with exponent `1`): if every `D` of a family of subsets of `P`
has product at most `Y`, then `∑_D 2^{|D|} ≤ Y ∏_{p ∈ P} (1 + 2/p)`. -/
theorem sum_two_pow_card_le {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) {𝒟 : Finset (Finset ℕ)}
    (h𝒟 : 𝒟 ⊆ P.powerset) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hY : ∀ D ∈ 𝒟, ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y) :
    ∑ D ∈ 𝒟, (2 : ℝ) ^ D.card ≤ Y * ∏ p ∈ P, (1 + 2 / (p : ℝ)) := by
  have hpt : ∀ D ∈ 𝒟, (2 : ℝ) ^ D.card ≤ Y * ∏ p ∈ D, (2 / (p : ℝ)) := by
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp (h𝒟 hD)
    have hpos : (0 : ℝ) < ((∏ p ∈ D, p : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Finset.prod_pos fun p hp => hP p (hDP hp))
    have e : ∏ p ∈ D, (2 / (p : ℝ)) = 2 ^ D.card / ((∏ p ∈ D, p : ℕ) : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
    rw [e, ← mul_div_assoc, le_div_iff₀ hpos]
    calc (2 : ℝ) ^ D.card * ((∏ p ∈ D, p : ℕ) : ℝ) ≤ 2 ^ D.card * Y :=
          mul_le_mul_of_nonneg_left (hY D hD) (pow_nonneg zero_le_two _)
      _ = Y * 2 ^ D.card := mul_comm _ _
  calc ∑ D ∈ 𝒟, (2 : ℝ) ^ D.card ≤ ∑ D ∈ 𝒟, Y * ∏ p ∈ D, (2 / (p : ℝ)) :=
        Finset.sum_le_sum hpt
    _ ≤ ∑ D ∈ P.powerset, Y * ∏ p ∈ D, (2 / (p : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg h𝒟 fun D _ _ =>
          mul_nonneg hY0 (Finset.prod_nonneg fun p _ =>
            div_nonneg zero_le_two (Nat.cast_nonneg p))
    _ = Y * ∏ p ∈ P, (1 + 2 / (p : ℝ)) := by rw [← Finset.mul_sum, Finset.prod_one_add]

/-- **The tail** (Rankin): `∑_{E ⊆ P, |E| = k} ∏_{p ∈ E} 2/p ≤ y^{-k} ∏_{p ∈ P} (1 + 2y/p)` for
`y > 0`. -/
theorem sum_powersetCard_prod_le (P : Finset ℕ) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ)) ≤
      (y ^ k)⁻¹ * ∏ p ∈ P, (1 + 2 * y / (p : ℝ)) := by
  have hyk : 0 < y ^ k := pow_pos hy k
  have hpt : ∀ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ)) =
      (y ^ k)⁻¹ * ∏ p ∈ E, (2 * y / (p : ℝ)) := by
    intro E hE
    have hcard : E.card = k := (Finset.mem_powersetCard.mp hE).2
    have e : ∏ p ∈ E, (2 * y / (p : ℝ)) = y ^ k * ∏ p ∈ E, (2 / (p : ℝ)) := by
      rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => by ring
    rw [e, ← mul_assoc, inv_mul_cancel₀ hyk.ne', one_mul]
  have hsub : P.powersetCard k ⊆ P.powerset := fun E hE =>
    Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hE).1
  calc ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ))
      = ∑ E ∈ P.powersetCard k, (y ^ k)⁻¹ * ∏ p ∈ E, (2 * y / (p : ℝ)) :=
        Finset.sum_congr rfl hpt
    _ = (y ^ k)⁻¹ * ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 * y / (p : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (y ^ k)⁻¹ * ∑ E ∈ P.powerset, ∏ p ∈ E, (2 * y / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun E _ _ =>
            Finset.prod_nonneg fun p _ =>
              div_nonneg (mul_nonneg zero_le_two hy.le) (Nat.cast_nonneg p))
          (inv_nonneg.mpr hyk.le)
    _ = (y ^ k)⁻¹ * ∏ p ∈ P, (1 + 2 * y / (p : ℝ)) := by rw [Finset.prod_one_add]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

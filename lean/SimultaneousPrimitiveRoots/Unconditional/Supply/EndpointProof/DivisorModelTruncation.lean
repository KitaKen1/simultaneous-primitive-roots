module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements

/-!
# Truncated divisor models of a function of the marked prime divisors

The combinatorial part of Lemma `lem:divisor-model` (`[P-06:0565–0633]`). Let `𝒬` be a finite set
of primes and `F` a function of finite sets of primes; think of `F(S) = H_marks(∏_{p ∈ S} p)`, so
that `H_marks(n) = F(S_n)` with `S_n = {p ∈ 𝒬 : p ∣ n}`.

* `moebiusCoeff F D = ∑_{D' ⊆ D} (-1)^{|D \ D'|} F(D')`, the Möbius inverse of `F` on the Boolean
  lattice; `sum_powerset_moebiusCoeff`: `∑_{D ⊆ S} a(D) = F(S)`. This is the full divisor expansion
  `H_marks(n) = ∑_{d' ∣ n} A_{d'}` of the manuscript (expand the damping
  `∏ (1 - (1 - q_p) 1_{p ∣ n})` over the unrepresented primes), with `A_{∏D} = a(D)`.
* `truncatedModel 𝒬 h F e`: the coefficient `A_e`, where `A_{∏D} = a(D)` for `D ⊆ 𝒬`, `|D| ≤ h`
  and `A_e = 0` otherwise ("truncate after `h_0 = ⌊L^{.01}⌋` additional primes"; the lists have a
  fixed number of primes, so truncating the number of additional primes is truncating `|D|`).
* `divisorSum_truncatedModel`: `∑_{e ∣ n} A_e = ∑_{D ⊆ S_n, |D| ≤ h} a(D)` for `n ≥ 1`.
* `pow_mul_normSq_sub_divisorSum_truncatedModel_le`: if `|F| ≤ H_b` then, for `β ≥ 1`,
  `β^h |F(S_n) - ∑_{e ∣ n} A_e|² ≤ (9β)^{|S_n|} H_b²` (the discarded part is
  `≤ 3^{|S_n|} H_b 1_{|S_n| > h}`: "the absolute pointwise error is bounded by
  `L^{C_9} 4^{ω_tot} 1_{ω_tot ≥ h_0}`").
* `exists_of_truncatedModel_ne_zero`: the support of `A`.
* `sum_norm_truncatedModel_div_le`: `∑_e |A_e| / e ≤ H_b ∏_{p ∈ 𝒬} (1 + 2/p)` ("The additional
  subset sums are at most `∏_{p in all groups} (1 + (1 - q_p)/p)`"; here with the cruder
  `|a(D)| ≤ 2^{|D|} H_b`).
* Auxiliary: `mem_of_prime_dvd_prod_primes`, `dvd_prod_filter_dvd_iff`,
  `prod_one_add_two_div_le_exp`, `reciprocalMass_union_le`, `reciprocalMass_biUnion_le`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Möbius inversion on the subsets of a finite set -/

/-- `∑_{E ⊆ T} (-1)^{|E|} = 1_{T = ∅}`. -/
theorem sum_powerset_neg_one_pow_card_eq (T : Finset ℕ) :
    ∑ E ∈ T.powerset, (-1 : ℂ) ^ E.card = if T = ∅ then 1 else 0 := by
  have h1 : ∑ E ∈ T.powerset, (-1 : ℂ) ^ E.card = ∏ _i ∈ T, (1 + (-1 : ℂ)) := by
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl fun E _ => (Finset.prod_const (-1 : ℂ)).symm
  rw [h1]
  by_cases hT : T = ∅
  · rw [if_pos hT, hT, Finset.prod_empty]
  · rw [if_neg hT]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    exact Finset.prod_eq_zero hi (add_neg_cancel (1 : ℂ))

/-- `∑_{D ⊆ S} 2^{|D|} = 3^{|S|}`. -/
theorem sum_powerset_two_pow_card (S : Finset ℕ) :
    ∑ D ∈ S.powerset, (2 : ℝ) ^ D.card = 3 ^ S.card := by
  have h1 : ∑ D ∈ S.powerset, (2 : ℝ) ^ D.card = ∏ _i ∈ S, (1 + (2 : ℝ)) := by
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl fun D _ => (Finset.prod_const (2 : ℝ)).symm
  have e3 : (1 + (2 : ℝ)) = 3 := by norm_num
  rw [h1, Finset.prod_const, e3]

/-- The Möbius inverse of a set function on the Boolean lattice:
`a(D) = ∑_{D' ⊆ D} (-1)^{|D \ D'|} F(D')`. -/
def moebiusCoeff (F : Finset ℕ → ℂ) (D : Finset ℕ) : ℂ :=
  ∑ D' ∈ D.powerset, (-1 : ℂ) ^ (D \ D').card * F D'

/-- **Möbius inversion on the Boolean lattice**: `∑_{D ⊆ S} a(D) = F(S)`. -/
theorem sum_powerset_moebiusCoeff (F : Finset ℕ → ℂ) (S : Finset ℕ) :
    ∑ D ∈ S.powerset, moebiusCoeff F D = F S := by
  have hinner : ∀ D' ∈ S.powerset,
      ∑ D ∈ S.powerset.filter (fun D => D' ⊆ D), (-1 : ℂ) ^ (D \ D').card * F D' =
        if S \ D' = ∅ then F D' else 0 := by
    intro D' hD'
    have hD'S : D' ⊆ S := Finset.mem_powerset.mp hD'
    have hre : ∑ D ∈ S.powerset.filter (fun D => D' ⊆ D), (-1 : ℂ) ^ (D \ D').card * F D' =
        ∑ E ∈ (S \ D').powerset, (-1 : ℂ) ^ E.card * F D' := by
      refine Finset.sum_nbij' (fun D => D \ D') (fun E => E ∪ D') ?_ ?_ ?_ ?_ ?_
      · intro D hD
        have h1 : D ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
        exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff h1 (Finset.Subset.refl D'))
      · intro E hE
        have hE' : E ⊆ S \ D' := Finset.mem_powerset.mp hE
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.union_subset (hE'.trans Finset.sdiff_subset) hD'S),
            Finset.subset_union_right⟩
      · intro D hD
        exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp hD).2
      · intro E hE
        have hE' : E ⊆ S \ D' := Finset.mem_powerset.mp hE
        have hdisj : Disjoint E D' := Finset.disjoint_of_subset_left hE' Finset.sdiff_disjoint
        exact Finset.union_sdiff_cancel_right hdisj
      · intro D _
        rfl
    rw [hre, ← Finset.sum_mul, sum_powerset_neg_one_pow_card_eq]
    by_cases h : S \ D' = ∅
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]
  unfold moebiusCoeff
  calc ∑ D ∈ S.powerset, ∑ D' ∈ D.powerset, (-1 : ℂ) ^ (D \ D').card * F D'
      = ∑ D' ∈ S.powerset, ∑ D ∈ S.powerset.filter (fun D => D' ⊆ D),
          (-1 : ℂ) ^ (D \ D').card * F D' := by
        refine Finset.sum_comm' fun D D' => ?_
        simp only [Finset.mem_powerset, Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2⟩, h2.trans h1⟩
        · rintro ⟨⟨h1, h2⟩, -⟩
          exact ⟨h1, h2⟩
    _ = ∑ D' ∈ S.powerset, (if S \ D' = ∅ then F D' else 0) := Finset.sum_congr rfl hinner
    _ = F S := by
        rw [Finset.sum_eq_single S]
        · rw [if_pos (Finset.sdiff_self S)]
        · intro D' hD' hne
          refine if_neg fun h => hne ?_
          exact Finset.Subset.antisymm (Finset.mem_powerset.mp hD')
            (Finset.sdiff_eq_empty_iff_subset.mp h)
        · intro h
          exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl S)) h

/-- `|a(D)| ≤ 2^{|D|} H_b` when `|F| ≤ H_b` on the subsets of `D`. -/
theorem norm_moebiusCoeff_le {F : Finset ℕ → ℂ} {Hb : ℝ} {D : Finset ℕ}
    (hF : ∀ D' ⊆ D, ‖F D'‖ ≤ Hb) : ‖moebiusCoeff F D‖ ≤ 2 ^ D.card * Hb := by
  unfold moebiusCoeff
  calc ‖∑ D' ∈ D.powerset, (-1 : ℂ) ^ (D \ D').card * F D'‖
      ≤ ∑ D' ∈ D.powerset, ‖(-1 : ℂ) ^ (D \ D').card * F D'‖ := norm_sum_le _ _
    _ ≤ ∑ _D' ∈ D.powerset, Hb := Finset.sum_le_sum fun D' hD' => by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact hF D' (Finset.mem_powerset.mp hD')
    _ = 2 ^ D.card * Hb := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

/-! ### Products of sets of primes -/

/-- A prime dividing a product of distinct primes is one of them. -/
theorem mem_of_prime_dvd_prod_primes {D : Finset ℕ} (hD : ∀ r ∈ D, r.Prime) {p : ℕ}
    (hp : p.Prime) (h : p ∣ ∏ r ∈ D, r) : p ∈ D := by
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun r : ℕ => r)).mp h
  have e : p = r := (Nat.prime_dvd_prime_iff_eq hp (hD r hr)).mp hpr
  rw [e]
  exact hr

/-- For a set `𝒬` of primes, a prime of `𝒬` divides `∏_{r ∈ 𝒬, r ∣ n} r` exactly when it divides
`n`. -/
theorem dvd_prod_filter_dvd_iff {𝒬 : Finset ℕ} (h𝒬 : ∀ p ∈ 𝒬, p.Prime) (n : ℕ) {p : ℕ}
    (hp : p ∈ 𝒬) : (p ∣ ∏ r ∈ 𝒬.filter (fun r => r ∣ n), r) ↔ p ∣ n := by
  constructor
  · intro h
    have hmem := mem_of_prime_dvd_prod_primes
      (fun r hr => h𝒬 r (Finset.mem_filter.mp hr).1) (h𝒬 p hp) h
    exact (Finset.mem_filter.mp hmem).2
  · intro h
    exact Finset.dvd_prod_of_mem (fun r : ℕ => r) (Finset.mem_filter.mpr ⟨hp, h⟩)

/-! ### The truncated model -/

/-- The coefficients of the truncated divisor model: `A_{∏D} = a(D)` for `D ⊆ 𝒬` with `|D| ≤ h`
(the map `D ↦ ∏D` is injective on sets of primes), and `A_e = 0` for all other `e`. -/
def truncatedModel (𝒬 : Finset ℕ) (h : ℕ) (F : Finset ℕ → ℂ) (e : ℕ) : ℂ :=
  ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
    if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0

/-- The support of the truncated model: products of at most `h` primes of `𝒬`. -/
theorem exists_of_truncatedModel_ne_zero {𝒬 : Finset ℕ} {h : ℕ} {F : Finset ℕ → ℂ} {e : ℕ}
    (he : truncatedModel 𝒬 h F e ≠ 0) :
    ∃ D : Finset ℕ, D ⊆ 𝒬 ∧ D.card ≤ h ∧ (∏ p ∈ D, p) = e := by
  by_contra hcon
  refine he ?_
  unfold truncatedModel
  refine Finset.sum_eq_zero fun D hD => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hD
  exact if_neg fun h3 => hcon ⟨D, Finset.mem_powerset.mp h1, h2, h3⟩

/-- **The divisor sum of the truncated model**: for `n ≥ 1`,
`∑_{e ∣ n} A_e = ∑_{D ⊆ S_n, |D| ≤ h} a(D)` with `S_n = {p ∈ 𝒬 : p ∣ n}`. -/
theorem divisorSum_truncatedModel {𝒬 : Finset ℕ} (h𝒬 : ∀ p ∈ 𝒬, p.Prime) (h : ℕ)
    (F : Finset ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    divisorSum (truncatedModel 𝒬 h F) n =
      ∑ D ∈ (𝒬.filter fun p => p ∣ n).powerset.filter (fun D => D.card ≤ h),
        moebiusCoeff F D := by
  have h1 : ∀ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
      ∑ e ∈ n.divisors, (if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0) =
        if (∏ p ∈ D, p) ∣ n then moebiusCoeff F D else 0 := by
    intro D _
    rw [Finset.sum_ite_eq]
    by_cases hd : (∏ p ∈ D, p) ∣ n
    · rw [if_pos hd, if_pos (Nat.mem_divisors.mpr ⟨hd, hn⟩)]
    · rw [if_neg hd,
        if_neg fun hm : (∏ p ∈ D, p) ∈ n.divisors => hd (Nat.mem_divisors.mp hm).1]
  have hset : (𝒬.powerset.filter (fun D => D.card ≤ h)).filter (fun D => (∏ p ∈ D, p) ∣ n) =
      (𝒬.filter fun p => p ∣ n).powerset.filter (fun D => D.card ≤ h) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hD𝒬, hcard⟩, hdvd⟩
      exact ⟨fun p hp => Finset.mem_filter.mpr
        ⟨hD𝒬 hp, (Finset.dvd_prod_of_mem (fun r : ℕ => r) hp).trans hdvd⟩, hcard⟩
    · rintro ⟨hDS, hcard⟩
      exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hDS hp)).1, hcard⟩,
        Finset.prod_primes_dvd n (fun p hp => (h𝒬 p (Finset.mem_filter.mp (hDS hp)).1).prime)
          (fun p hp => (Finset.mem_filter.mp (hDS hp)).2)⟩
  unfold divisorSum truncatedModel
  calc ∑ e ∈ n.divisors, ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
        (if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0)
      = ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h), ∑ e ∈ n.divisors,
          (if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0) := Finset.sum_comm
    _ = ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
          (if (∏ p ∈ D, p) ∣ n then moebiusCoeff F D else 0) := Finset.sum_congr rfl h1
    _ = ∑ D ∈ (𝒬.powerset.filter (fun D => D.card ≤ h)).filter
          (fun D => (∏ p ∈ D, p) ∣ n), moebiusCoeff F D := (Finset.sum_filter _ _).symm
    _ = ∑ D ∈ (𝒬.filter fun p => p ∣ n).powerset.filter (fun D => D.card ≤ h),
          moebiusCoeff F D := by rw [hset]

/-- **The pointwise error of the truncated model**: if `|F| ≤ H_b` on the subsets of `𝒬`, then for
`β ≥ 1` and `n ≥ 1`, with `S_n = {p ∈ 𝒬 : p ∣ n}`,
`β^h |F(S_n) - ∑_{e ∣ n} A_e|² ≤ (9β)^{|S_n|} H_b²`. -/
theorem pow_mul_normSq_sub_divisorSum_truncatedModel_le {𝒬 : Finset ℕ}
    (h𝒬 : ∀ p ∈ 𝒬, p.Prime) (h : ℕ) (F : Finset ℕ → ℂ) {Hb β : ℝ} (hHb : 0 ≤ Hb)
    (hβ : 1 ≤ β) (hF : ∀ D ⊆ 𝒬, ‖F D‖ ≤ Hb) {n : ℕ} (hn : n ≠ 0) :
    β ^ h * ‖F (𝒬.filter fun p => p ∣ n) - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2 ≤
      (9 * β) ^ (𝒬.filter fun p => p ∣ n).card * Hb ^ 2 := by
  have hdiv := divisorSum_truncatedModel h𝒬 h F hn
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = 𝒬.filter fun p => p ∣ n := ⟨_, rfl⟩
  rw [← hS] at hdiv ⊢
  have hS𝒬 : S ⊆ 𝒬 := by
    rw [hS]
    exact Finset.filter_subset _ _
  have hβ0 : 0 ≤ β := by linarith
  have herr : F S - divisorSum (truncatedModel 𝒬 h F) n =
      ∑ D ∈ S.powerset, (moebiusCoeff F D - if D.card ≤ h then moebiusCoeff F D else 0) := by
    rw [hdiv, Finset.sum_sub_distrib, sum_powerset_moebiusCoeff, ← Finset.sum_filter]
  rcases le_or_gt S.card h with hle | hgt
  · -- nothing is discarded
    have hzero : F S - divisorSum (truncatedModel 𝒬 h F) n = 0 := by
      rw [herr]
      refine Finset.sum_eq_zero fun D hD => ?_
      have hDle : D.card ≤ h := (Finset.card_le_card (Finset.mem_powerset.mp hD)).trans hle
      rw [if_pos hDle, sub_self]
    have e0 : β ^ h * ‖F S - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2 = 0 := by
      rw [hzero, norm_zero, zero_pow two_ne_zero, mul_zero]
    rw [e0]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hβ0) _) (sq_nonneg _)
  · have hnorm : ‖F S - divisorSum (truncatedModel 𝒬 h F) n‖ ≤ 3 ^ S.card * Hb := by
      rw [herr]
      calc ‖∑ D ∈ S.powerset,
            (moebiusCoeff F D - if D.card ≤ h then moebiusCoeff F D else 0)‖
          ≤ ∑ D ∈ S.powerset,
              ‖moebiusCoeff F D - if D.card ≤ h then moebiusCoeff F D else 0‖ :=
            norm_sum_le _ _
        _ ≤ ∑ D ∈ S.powerset, 2 ^ D.card * Hb := Finset.sum_le_sum fun D hD => by
            have hDS : D ⊆ S := Finset.mem_powerset.mp hD
            have hb : ‖moebiusCoeff F D‖ ≤ 2 ^ D.card * Hb :=
              norm_moebiusCoeff_le fun D' hD' => hF D' ((hD'.trans hDS).trans hS𝒬)
            by_cases hc : D.card ≤ h
            · rw [if_pos hc, sub_self, norm_zero]
              exact mul_nonneg (pow_nonneg zero_le_two _) hHb
            · rw [if_neg hc, sub_zero]
              exact hb
        _ = 3 ^ S.card * Hb := by rw [← Finset.sum_mul, sum_powerset_two_pow_card]
    have hβh : β ^ h ≤ β ^ S.card := pow_le_pow_right₀ hβ hgt.le
    have hsq : ‖F S - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2 ≤ (3 ^ S.card * Hb) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have e9 : ((3 : ℝ) ^ S.card) ^ 2 = 9 ^ S.card := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc β ^ h * ‖F S - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2
        ≤ β ^ S.card * (3 ^ S.card * Hb) ^ 2 :=
          mul_le_mul hβh hsq (sq_nonneg _) (pow_nonneg hβ0 _)
      _ = (9 * β) ^ S.card * Hb ^ 2 := by
          rw [mul_pow (3 ^ S.card) Hb 2, mul_pow 9 β S.card, e9]
          ring

/-- **The mass of the truncated model**: `∑_{1 ≤ e ≤ E} |A_e| / e ≤ H_b ∏_{p ∈ 𝒬} (1 + 2/p)` when
`|F| ≤ H_b` on the subsets of `𝒬`. -/
theorem sum_norm_truncatedModel_div_le {𝒬 : Finset ℕ} (h : ℕ) {F : Finset ℕ → ℂ} {Hb : ℝ}
    (hF : ∀ D ⊆ 𝒬, ‖F D‖ ≤ Hb) (E : ℕ) :
    ∑ e ∈ Finset.Icc 1 E, ‖truncatedModel 𝒬 h F e‖ / (e : ℝ) ≤
      Hb * ∏ p ∈ 𝒬, (1 + 2 / (p : ℝ)) := by
  have h1 : ∀ e ∈ Finset.Icc 1 E, ‖truncatedModel 𝒬 h F e‖ / (e : ℝ) ≤
      ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
        if (∏ p ∈ D, p) = e then ‖moebiusCoeff F D‖ / (e : ℝ) else 0 := by
    intro e _
    unfold truncatedModel
    calc ‖∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
          (if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0)‖ / (e : ℝ)
        ≤ (∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
            ‖if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0‖) / (e : ℝ) :=
          div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg e)
      _ = ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
            ‖if (∏ p ∈ D, p) = e then moebiusCoeff F D else 0‖ / (e : ℝ) :=
          Finset.sum_div _ _ _
      _ = ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
            if (∏ p ∈ D, p) = e then ‖moebiusCoeff F D‖ / (e : ℝ) else 0 :=
          Finset.sum_congr rfl fun D _ => by
            by_cases hD : (∏ p ∈ D, p) = e
            · rw [if_pos hD, if_pos hD]
            · rw [if_neg hD, if_neg hD, norm_zero, zero_div]
  have h2 : ∀ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
      ∑ e ∈ Finset.Icc 1 E, (if (∏ p ∈ D, p) = e then ‖moebiusCoeff F D‖ / (e : ℝ) else 0) ≤
        ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ) := by
    intro D _
    have h0 : 0 ≤ ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ) :=
      div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
    rw [Finset.sum_ite_eq]
    by_cases hm : (∏ p ∈ D, p) ∈ Finset.Icc 1 E
    · exact le_of_eq (if_pos hm)
    · exact le_of_eq_of_le (if_neg hm) h0
  have h3 : ∀ D ∈ 𝒬.powerset,
      ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Hb * ∏ p ∈ D, (2 / (p : ℝ)) := by
    intro D hD
    have hDsub : D ⊆ 𝒬 := Finset.mem_powerset.mp hD
    have hn : ‖moebiusCoeff F D‖ ≤ 2 ^ D.card * Hb :=
      norm_moebiusCoeff_le fun D' hD' => hF D' (hD'.trans hDsub)
    calc ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ)
        ≤ 2 ^ D.card * Hb / ((∏ p ∈ D, p : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
      _ = Hb * ∏ p ∈ D, (2 / (p : ℝ)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
          ring
  calc ∑ e ∈ Finset.Icc 1 E, ‖truncatedModel 𝒬 h F e‖ / (e : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1 E, ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
          (if (∏ p ∈ D, p) = e then ‖moebiusCoeff F D‖ / (e : ℝ) else 0) :=
        Finset.sum_le_sum h1
    _ = ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h), ∑ e ∈ Finset.Icc 1 E,
          (if (∏ p ∈ D, p) = e then ‖moebiusCoeff F D‖ / (e : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ D ∈ 𝒬.powerset.filter (fun D => D.card ≤ h),
          ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ) := Finset.sum_le_sum h2
    _ ≤ ∑ D ∈ 𝒬.powerset, ‖moebiusCoeff F D‖ / ((∏ p ∈ D, p : ℕ) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun D _ _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ ∑ D ∈ 𝒬.powerset, Hb * ∏ p ∈ D, (2 / (p : ℝ)) := Finset.sum_le_sum h3
    _ = Hb * ∏ p ∈ 𝒬, (1 + 2 / (p : ℝ)) := by rw [← Finset.mul_sum, Finset.prod_one_add]

/-! ### Reciprocal masses -/

/-- `∏_{p ∈ T} (1 + 2/p) ≤ exp(2 V_T)`. -/
theorem prod_one_add_two_div_le_exp (T : Finset ℕ) :
    ∏ p ∈ T, (1 + 2 / (p : ℝ)) ≤ Real.exp (2 * reciprocalMass T) := by
  unfold reciprocalMass
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
  · have h : 0 ≤ 2 / (p : ℝ) := div_nonneg zero_le_two (Nat.cast_nonneg p)
    linarith
  · calc 1 + 2 / (p : ℝ) = 2 * (1 / (p : ℝ)) + 1 := by ring
      _ ≤ Real.exp (2 * (1 / (p : ℝ))) := Real.add_one_le_exp _

/-- `V_{A ∪ B} ≤ V_A + V_B`. -/
theorem reciprocalMass_union_le (A B : Finset ℕ) :
    reciprocalMass (A ∪ B) ≤ reciprocalMass A + reciprocalMass B := by
  unfold reciprocalMass
  have h : ∑ p ∈ A ∪ B, 1 / (p : ℝ) + ∑ p ∈ A ∩ B, 1 / (p : ℝ) =
      ∑ p ∈ A, 1 / (p : ℝ) + ∑ p ∈ B, 1 / (p : ℝ) := Finset.sum_union_inter
  have h0 : 0 ≤ ∑ p ∈ A ∩ B, 1 / (p : ℝ) :=
    Finset.sum_nonneg fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p)
  linarith

/-- `V_{⋃_i T_i} ≤ ∑_i V_{T_i}`. -/
theorem reciprocalMass_biUnion_le {K : ℕ} (s : Finset (Fin K)) (T : Fin K → Finset ℕ) :
    reciprocalMass (s.biUnion T) ≤ ∑ i ∈ s, reciprocalMass (T i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.biUnion_empty, Finset.sum_empty]
    unfold reciprocalMass
    exact le_of_eq Finset.sum_empty
  · intro i s hi ih
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (reciprocalMass_union_le _ _).trans (add_le_add le_rfl ih)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

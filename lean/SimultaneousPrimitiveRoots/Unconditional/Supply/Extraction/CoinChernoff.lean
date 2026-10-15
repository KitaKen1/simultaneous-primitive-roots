module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Sanity

/-!
# The coin step: few successes are unlikely when the mean is large

`[P-07:0496–0502]`, the first-level (coin) part of (ext:success-chebyshev). For independent coins
with success probabilities `s_g ∈ [0, 1]` and a real threshold `t`, the outcomes with fewer than
`t` successes in the small family have total weight at most

`2^t ∏_{g small} (1 - s_g / 2) ≤ 2^t exp(-(∑_{g small} s_g) / 2)`

(the exponential moment `E 2^{-N}` instead of the manuscript's Chebyshev inequality; only the
product formula `∏ (f + g) = ∑_S ∏_S f ∏_{Sᶜ} g` is used), and the same for the big family.

* `sum_coinWeight_mul_prod`: `∑_S coinWeight(S) ∏_{g ∈ S} w_g = ∏_g (s_g w_g + 1 - s_g)`.
* `failedMass_le_exp`: the failed mass is at most
  `2^{c₂ log L} (exp(-m_small/2) + exp(-m_big/2))`, `m = ∑ s_g` over the family.
* `failedMass_le_indicator`: hence it is at most
  `1_{m_small < τ} + 1_{m_big < τ} + 2 · 2^{c₂ log L} exp(-τ/2)` for every `τ`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-- The coin measure of a multiplicative weight:
`∑_S coinWeight(S) ∏_{g ∈ S} w_g = ∏_g (s_g w_g + (1 - s_g))`. -/
theorem sum_coinWeight_mul_prod (𝔊 : ActiveGroups) (s w : 𝔊.Index → ℝ) :
    ∑ S : Finset 𝔊.Index, coinWeight 𝔊 s S * ∏ g ∈ S, w g =
      ∏ g, (s g * w g + (1 - s g)) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold coinWeight
  rw [Finset.prod_mul_distrib]
  ring

/-- The weight `c` on the small groups and `1` on the big groups has product `c^{|S ∩ small|}`. -/
theorem prod_elim_left (𝔊 : ActiveGroups) (c : ℝ) (S : Finset 𝔊.Index) :
    ∏ g ∈ S, Sum.elim (fun _ : Fin 𝔊.numSmall => c) (fun _ : Fin 𝔊.numBig => (1 : ℝ)) g =
      c ^ S.toLeft.card := by
  calc ∏ g ∈ S, Sum.elim (fun _ : Fin 𝔊.numSmall => c) (fun _ : Fin 𝔊.numBig => (1 : ℝ)) g
      = ∏ g ∈ S.toLeft.disjSum S.toRight,
          Sum.elim (fun _ : Fin 𝔊.numSmall => c) (fun _ : Fin 𝔊.numBig => (1 : ℝ)) g := by
        rw [Finset.toLeft_disjSum_toRight]
    _ = (∏ _a ∈ S.toLeft, c) * ∏ _b ∈ S.toRight, (1 : ℝ) := Finset.prod_disjSum _ _ _
    _ = c ^ S.toLeft.card := by rw [Finset.prod_const, Finset.prod_const_one, mul_one]

/-- The weight `1` on the small groups and `c` on the big groups has product `c^{|S ∩ big|}`. -/
theorem prod_elim_right (𝔊 : ActiveGroups) (c : ℝ) (S : Finset 𝔊.Index) :
    ∏ g ∈ S, Sum.elim (fun _ : Fin 𝔊.numSmall => (1 : ℝ)) (fun _ : Fin 𝔊.numBig => c) g =
      c ^ S.toRight.card := by
  calc ∏ g ∈ S, Sum.elim (fun _ : Fin 𝔊.numSmall => (1 : ℝ)) (fun _ : Fin 𝔊.numBig => c) g
      = ∏ g ∈ S.toLeft.disjSum S.toRight,
          Sum.elim (fun _ : Fin 𝔊.numSmall => (1 : ℝ)) (fun _ : Fin 𝔊.numBig => c) g := by
        rw [Finset.toLeft_disjSum_toRight]
    _ = (∏ _a ∈ S.toLeft, (1 : ℝ)) * ∏ _b ∈ S.toRight, c := Finset.prod_disjSum _ _ _
    _ = c ^ S.toRight.card := by rw [Finset.prod_const_one, Finset.prod_const, one_mul]

/-- `s/2 + (1 - s) ≤ exp(-s/2)`. -/
theorem half_factor_le (s : ℝ) : s * (1 / 2) + (1 - s) ≤ Real.exp (-s / 2) := by
  have h := Real.one_sub_le_exp_neg (s / 2)
  have e : -(s / 2) = -s / 2 := by ring
  rw [e] at h
  linarith

/-- `E (1/2)^{N_small} ≤ exp(-m_small/2)`. -/
theorem sum_coinWeight_half_left (𝔊 : ActiveGroups) (s : 𝔊.Index → ℝ) (h0 : ∀ g, 0 ≤ s g)
    (h1 : ∀ g, s g ≤ 1) :
    ∑ S : Finset 𝔊.Index, coinWeight 𝔊 s S * (1 / 2 : ℝ) ^ S.toLeft.card ≤
      Real.exp (-(∑ a, s (Sum.inl a)) / 2) := by
  have e : ∀ S : Finset 𝔊.Index, coinWeight 𝔊 s S * (1 / 2 : ℝ) ^ S.toLeft.card =
      coinWeight 𝔊 s S * ∏ g ∈ S,
        Sum.elim (fun _ : Fin 𝔊.numSmall => (1 / 2 : ℝ)) (fun _ : Fin 𝔊.numBig => (1 : ℝ)) g :=
    fun S => by rw [prod_elim_left]
  rw [Finset.sum_congr rfl fun S _ => e S, sum_coinWeight_mul_prod, Fintype.prod_sum_type]
  have hR : ∏ b : Fin 𝔊.numBig, (s (Sum.inr b) *
      Sum.elim (fun _ : Fin 𝔊.numSmall => (1 / 2 : ℝ)) (fun _ : Fin 𝔊.numBig => (1 : ℝ))
        (Sum.inr b) + (1 - s (Sum.inr b))) = 1 :=
    Finset.prod_eq_one fun b _ => by
      rw [Sum.elim_inr]
      ring
  rw [hR, mul_one]
  have hsum : -(∑ a, s (Sum.inl a)) / 2 = ∑ a : Fin 𝔊.numSmall, -s (Sum.inl a) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [hsum, Real.exp_sum]
  refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => ?_)
  · rw [Sum.elim_inl]
    have := h0 (Sum.inl a)
    have := h1 (Sum.inl a)
    linarith
  · rw [Sum.elim_inl]
    exact half_factor_le _

/-- `E (1/2)^{N_big} ≤ exp(-m_big/2)`. -/
theorem sum_coinWeight_half_right (𝔊 : ActiveGroups) (s : 𝔊.Index → ℝ) (h0 : ∀ g, 0 ≤ s g)
    (h1 : ∀ g, s g ≤ 1) :
    ∑ S : Finset 𝔊.Index, coinWeight 𝔊 s S * (1 / 2 : ℝ) ^ S.toRight.card ≤
      Real.exp (-(∑ b, s (Sum.inr b)) / 2) := by
  have e : ∀ S : Finset 𝔊.Index, coinWeight 𝔊 s S * (1 / 2 : ℝ) ^ S.toRight.card =
      coinWeight 𝔊 s S * ∏ g ∈ S,
        Sum.elim (fun _ : Fin 𝔊.numSmall => (1 : ℝ)) (fun _ : Fin 𝔊.numBig => (1 / 2 : ℝ)) g :=
    fun S => by rw [prod_elim_right]
  rw [Finset.sum_congr rfl fun S _ => e S, sum_coinWeight_mul_prod, Fintype.prod_sum_type]
  have hL : ∏ a : Fin 𝔊.numSmall, (s (Sum.inl a) *
      Sum.elim (fun _ : Fin 𝔊.numSmall => (1 : ℝ)) (fun _ : Fin 𝔊.numBig => (1 / 2 : ℝ))
        (Sum.inl a) + (1 - s (Sum.inl a))) = 1 :=
    Finset.prod_eq_one fun a _ => by
      rw [Sum.elim_inl]
      ring
  rw [hL, one_mul]
  have hsum : -(∑ b, s (Sum.inr b)) / 2 = ∑ b : Fin 𝔊.numBig, -s (Sum.inr b) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  rw [hsum, Real.exp_sum]
  refine Finset.prod_le_prod (fun b _ => ?_) (fun b _ => ?_)
  · rw [Sum.elim_inr]
    have := h0 (Sum.inr b)
    have := h1 (Sum.inr b)
    linarith
  · rw [Sum.elim_inr]
    exact half_factor_le _

/-- `1 ≤ 2^t (1/2)^n` for a natural number `n < t`. -/
theorem one_le_two_rpow_mul {t : ℝ} {n : ℕ} (h : (n : ℝ) < t) :
    1 ≤ (2 : ℝ) ^ t * (1 / 2 : ℝ) ^ n := by
  have h1 : (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ t :=
    Real.rpow_le_rpow_of_exponent_le one_le_two h.le
  rw [Real.rpow_natCast] at h1
  have h2 : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  calc (1 : ℝ) = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := h2.symm
    _ ≤ (2 : ℝ) ^ t * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_right h1 h3

/-- **Few successes are unlikely**: the failed mass is at most
`2^{c₂ log L} (exp(-m_small/2) + exp(-m_big/2))`, where `m` is the sum of the success
probabilities over the family. -/
theorem failedMass_le_exp (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (c₂ : ℝ) {j : ℕ} (x : ℝ) {u : ℕ}
    (h0 : ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j u g) (h1 : ∀ g, coinProb 𝔊 c₁ q₀ j u g ≤ 1) :
    failedMass 𝔊 c₁ c₂ q₀ j x u ≤
      (2 : ℝ) ^ (c₂ * Real.log (Real.log x)) *
        (Real.exp (-(∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a)) / 2) +
          Real.exp (-(∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b)) / 2)) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = c₂ * Real.log (Real.log x) := ⟨_, rfl⟩
  rw [← ht]
  have h2t : (0 : ℝ) ≤ (2 : ℝ) ^ t := Real.rpow_nonneg zero_le_two t
  have hcw : ∀ S : Finset 𝔊.Index, 0 ≤ coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S :=
    fun S => coinWeight_nonneg 𝔊 h0 h1 S
  have hterm0 : ∀ S : Finset 𝔊.Index,
      0 ≤ (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toLeft.card) +
        (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toRight.card) :=
    fun S => add_nonneg
      (mul_nonneg h2t (mul_nonneg (hcw S) (pow_nonneg (by norm_num) _)))
      (mul_nonneg h2t (mul_nonneg (hcw S) (pow_nonneg (by norm_num) _)))
  have key : ∀ S ∈ (goodSets 𝔊 c₂ x)ᶜ, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S ≤
      (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toLeft.card) +
        (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toRight.card) := by
    intro S hS
    have hS' : ¬ (t ≤ (S.toLeft.card : ℝ) ∧ t ≤ (S.toRight.card : ℝ)) := by
      intro hc
      rw [ht] at hc
      exact (Finset.mem_compl.mp hS)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hc⟩)
    have hl0 : 0 ≤ (2 : ℝ) ^ t *
        (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toLeft.card) :=
      mul_nonneg h2t (mul_nonneg (hcw S) (pow_nonneg (by norm_num) _))
    have hr0 : 0 ≤ (2 : ℝ) ^ t *
        (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S * (1 / 2 : ℝ) ^ S.toRight.card) :=
      mul_nonneg h2t (mul_nonneg (hcw S) (pow_nonneg (by norm_num) _))
    by_cases hL : t ≤ (S.toLeft.card : ℝ)
    · have hR : (S.toRight.card : ℝ) < t := not_le.mp fun h => hS' ⟨hL, h⟩
      have h3 := mul_le_mul_of_nonneg_left (one_le_two_rpow_mul hR) (hcw S)
      have e : coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
          ((2 : ℝ) ^ t * (1 / 2 : ℝ) ^ S.toRight.card) =
          (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
            (1 / 2 : ℝ) ^ S.toRight.card) := by ring
      rw [mul_one, e] at h3
      linarith
    · have hL' : (S.toLeft.card : ℝ) < t := not_le.mp hL
      have h3 := mul_le_mul_of_nonneg_left (one_le_two_rpow_mul hL') (hcw S)
      have e : coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
          ((2 : ℝ) ^ t * (1 / 2 : ℝ) ^ S.toLeft.card) =
          (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
            (1 / 2 : ℝ) ^ S.toLeft.card) := by ring
      rw [mul_one, e] at h3
      linarith
  unfold failedMass
  calc ∑ S ∈ (goodSets 𝔊 c₂ x)ᶜ, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S
      ≤ ∑ S ∈ (goodSets 𝔊 c₂ x)ᶜ,
          ((2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toLeft.card) +
            (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toRight.card)) := Finset.sum_le_sum key
    _ ≤ ∑ S : Finset 𝔊.Index,
          ((2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toLeft.card) +
            (2 : ℝ) ^ t * (coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toRight.card)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun S _ _ => hterm0 S
    _ = (2 : ℝ) ^ t *
          (∑ S : Finset 𝔊.Index, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toLeft.card +
            ∑ S : Finset 𝔊.Index, coinWeight 𝔊 (coinProb 𝔊 c₁ q₀ j u) S *
              (1 / 2 : ℝ) ^ S.toRight.card) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
    _ ≤ (2 : ℝ) ^ t *
          (Real.exp (-(∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a)) / 2) +
            Real.exp (-(∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b)) / 2)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (sum_coinWeight_half_left 𝔊 _ h0 h1)
            (sum_coinWeight_half_right 𝔊 _ h0 h1)) h2t

/-- **The failed mass and the two means**: for every `τ`, the failed mass is at most
`1_{m_small < τ} + 1_{m_big < τ} + 2 · 2^{c₂ log L} exp(-τ/2)`. -/
theorem failedMass_le_indicator (𝔊 : ActiveGroups) {c₁ q₀ : ℝ} (c₂ : ℝ) {j : ℕ} (x : ℝ) {u : ℕ}
    (h0 : ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j u g) (h1 : ∀ g, coinProb 𝔊 c₁ q₀ j u g ≤ 1) (τ : ℝ) :
    failedMass 𝔊 c₁ c₂ q₀ j x u ≤
      (if ∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a) < τ then (1 : ℝ) else 0) +
        (if ∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b) < τ then (1 : ℝ) else 0) +
          2 * ((2 : ℝ) ^ (c₂ * Real.log (Real.log x)) * Real.exp (-τ / 2)) := by
  have h2t : (0 : ℝ) ≤ (2 : ℝ) ^ (c₂ * Real.log (Real.log x)) := Real.rpow_nonneg zero_le_two _
  have hrest : 0 ≤ 2 * ((2 : ℝ) ^ (c₂ * Real.log (Real.log x)) * Real.exp (-τ / 2)) :=
    mul_nonneg zero_le_two (mul_nonneg h2t (Real.exp_pos _).le)
  have hle1 := failedMass_le_one 𝔊 c₂ x h0 h1
  by_cases hL : ∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a) < τ
  · rw [if_pos hL]
    have hi : (0 : ℝ) ≤ if ∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b) < τ then (1 : ℝ) else 0 := by
      split_ifs
      · exact zero_le_one
      · exact le_rfl
    linarith
  · rw [if_neg hL, zero_add]
    by_cases hR : ∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b) < τ
    · rw [if_pos hR]
      linarith
    · rw [if_neg hR, zero_add]
      have hL' : τ ≤ ∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a) := not_lt.mp hL
      have hR' : τ ≤ ∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b) := not_lt.mp hR
      have e1 : Real.exp (-(∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a)) / 2) ≤ Real.exp (-τ / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have e2 : Real.exp (-(∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b)) / 2) ≤ Real.exp (-τ / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      refine (failedMass_le_exp 𝔊 c₂ x h0 h1).trans ?_
      calc (2 : ℝ) ^ (c₂ * Real.log (Real.log x)) *
            (Real.exp (-(∑ a, coinProb 𝔊 c₁ q₀ j u (Sum.inl a)) / 2) +
              Real.exp (-(∑ b, coinProb 𝔊 c₁ q₀ j u (Sum.inr b)) / 2))
          ≤ (2 : ℝ) ^ (c₂ * Real.log (Real.log x)) *
              (Real.exp (-τ / 2) + Real.exp (-τ / 2)) :=
            mul_le_mul_of_nonneg_left (add_le_add e1 e2) h2t
        _ = 2 * ((2 : ℝ) ^ (c₂ * Real.log (Real.log x)) * Real.exp (-τ / 2)) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinBox
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinVariance
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinChernoff
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinMinorant
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinTools

/-!
# The coin step on one rough product box

`[P-07:0404–0407, 0489–0504]`: "for some fixed `c₂ > 0`, outcomes with fewer than `c₂ log L`
successes in either family have total positive weighted mass `o(x/L)`"; on one full rough product
dyad the failure probability is `o(1)`, uniformly.

The constants, for `0 < q₀ < 1` and `j ≥ 1`:

* `coinC1 q₀ = ((1 - q₀) (log 2)/2)²` (the largest `c₁` allowed by `eventually_coinProb_le_one`);
* `coinVhi = 3 (log 2)/2 ≥ V_g`, `coinBeta = ((log 2)/4)²`;
* `coinC4 q₀ j = c₁ (q₀/j)^{2j+2} / ((2j+2) v₊²)`: `s_g ≥ c₄ T_g` (`coinProb_ge_tee`);
* `coinC3 q₀ j = c₄ β / 100`, `coinC2 q₀ j = c₃ / 4`.

Results:

* `sum_failedMass_le`: on a sample with `BoxEq`, the failed mass summed over the sample is at most
  the two lower tails of `∑_g T_g` (small and big family, `BoxEq.card_lowerTail_le`) plus the
  Chernoff term (`failedMass_le_indicator`);
* `group_model_bounds`: a group of primes `≥ B` with `(log 2)/2 ≤ V_g ≤ 3 (log 2)/2` has
  `A_g + B_g ≤ 2j + 1` and `M(n n') ≥ β`;
* `candidateCount_ge`: each family has at least `(log L)/50` groups;
* `eventually_box_failedMass_le`: for every `η > 0` and large `x`, on every rough box with
  `x^δ ≤ 2^{k_i} ≤ x^C`, `∑_{m ∈ box} failedMass(∏ m_i - 1) ≤ η ∏_i V(W) 2^{k_i}`.

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

open Filter

noncomputable section

/-! ### The constants -/

/-- `c₁ = ((1 - q₀) (log 2)/2)²`. -/
def coinC1 (q₀ : ℝ) : ℝ := ((1 - q₀) * (Real.log 2 / 2)) ^ 2

/-- The upper bound `3 (log 2)/2` for the reciprocal masses of the candidate groups. -/
def coinVhi : ℝ := 3 * Real.log 2 / 2

/-- `β = ((log 2)/4)²`: the lower bound for the model mean of `T_g`. -/
def coinBeta : ℝ := (Real.log 2 / 4) ^ 2

/-- `c₄ = c₁ (q₀/j)^{2j+2} / ((2j+2) v₊²)`: `s_g ≥ c₄ T_g`. -/
def coinC4 (q₀ : ℝ) (j : ℕ) : ℝ :=
  coinC1 q₀ * ((q₀ / (j : ℝ)) ^ (2 * j + 2) / (((2 * j + 2 : ℕ) : ℝ) * coinVhi ^ 2))

/-- `c₃ = c₄ β / 100`. -/
def coinC3 (q₀ : ℝ) (j : ℕ) : ℝ := coinC4 q₀ j * coinBeta / 100

/-- `c₂ = c₃ / 4`: fewer than `c₂ log L` successes in either family is a failure. -/
def coinC2 (q₀ : ℝ) (j : ℕ) : ℝ := coinC3 q₀ j / 4

theorem coinC1_pos {q₀ : ℝ} (hq₀1 : q₀ < 1) : 0 < coinC1 q₀ :=
  pow_pos (mul_pos (by linarith) (half_pos (Real.log_pos (by norm_num)))) 2

theorem coinVhi_pos : 0 < coinVhi :=
  div_pos (mul_pos three_pos (Real.log_pos (by norm_num))) two_pos

theorem coinBeta_pos : 0 < coinBeta :=
  pow_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num)) 2

theorem coinC4_pos {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j) :
    0 < coinC4 q₀ j := by
  have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
  have hN : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  exact mul_pos (coinC1_pos hq₀1)
    (div_pos (pow_pos (div_pos hq₀ hjR) _) (mul_pos hN (pow_pos coinVhi_pos 2)))

theorem coinC3_pos {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j) :
    0 < coinC3 q₀ j :=
  div_pos (mul_pos (coinC4_pos hq₀ hq₀1 hj) coinBeta_pos) (by norm_num)

theorem coinC2_pos {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j) :
    0 < coinC2 q₀ j :=
  div_pos (coinC3_pos hq₀ hq₀1 hj) (by norm_num)

/-! ### The failed mass on an equidistributed sample -/

/-- **The failed mass on a sample**: the two lower tails of `∑_g T_g` and the Chernoff term. -/
theorem sum_failedMass_le {ι : Type*} {j : ℕ} (hj : 1 ≤ j) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 1 ≤ p) {Ω : Finset ι} {u : ι → ℕ} {M ε : ℝ} (hM : 0 ≤ M) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hbox : BoxEq j P Ω u M ε) (𝔊 : ActiveGroups) (hS : 1 ≤ 𝔊.numSmall)
    (hB : 1 ≤ 𝔊.numBig) (hsub : ∀ g, 𝔊.group g ⊆ P)
    (hdisjL : ∀ a a' : Fin 𝔊.numSmall, a ≠ a' →
      Disjoint (𝔊.group (Sum.inl a)) (𝔊.group (Sum.inl a')))
    (hdisjR : ∀ b b' : Fin 𝔊.numBig, b ≠ b' →
      Disjoint (𝔊.group (Sum.inr b)) (𝔊.group (Sum.inr b')))
    {N₀ β : ℝ} (hN₀ : 1 ≤ N₀) (hβ : 0 < β)
    (hsum : ∀ g, sumU j (𝔊.group g) + sumV j (𝔊.group g) ≤ N₀ - 1)
    (hlow : ∀ g, β ≤ mdl j 0 (𝔊.group g)) {c₁ q₀ c₄ τ : ℝ} (c₂ x : ℝ)
    (hprob0 : ∀ m ∈ Ω, ∀ g, 0 ≤ coinProb 𝔊 c₁ q₀ j (u m) g)
    (hprob1 : ∀ m ∈ Ω, ∀ g, coinProb 𝔊 c₁ q₀ j (u m) g ≤ 1) (hc₄ : 0 < c₄)
    (hmin : ∀ m ∈ Ω, ∀ g, c₄ * tee N₀ (𝔊.group g) (u m) ≤ coinProb 𝔊 c₁ q₀ j (u m) g)
    (hτL : τ ≤ c₄ * (β * (𝔊.numSmall : ℝ) / 2)) (hτR : τ ≤ c₄ * (β * (𝔊.numBig : ℝ) / 2)) :
    ∑ m ∈ Ω, failedMass 𝔊 c₁ c₂ q₀ j x (u m) ≤
      M * (8 * teeDiag N₀ / (β ^ 2 * (𝔊.numSmall : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) +
        M * (8 * teeDiag N₀ / (β ^ 2 * (𝔊.numBig : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) +
          (1 + ε) * M *
            (2 * ((2 : ℝ) ^ (c₂ * Real.log (Real.log x)) * Real.exp (-τ / 2))) := by
  obtain ⟨K, hK⟩ :
      ∃ K : ℝ, K = 2 * ((2 : ℝ) ^ (c₂ * Real.log (Real.log x)) * Real.exp (-τ / 2)) :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg zero_le_two
      (mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.exp_pos _).le)
  rw [← hK]
  have hpt : ∀ m ∈ Ω, failedMass 𝔊 c₁ c₂ q₀ j x (u m) ≤
      (if ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) < β * (𝔊.numSmall : ℝ) / 2
          then (1 : ℝ) else 0) +
        (if ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) < β * (𝔊.numBig : ℝ) / 2
          then (1 : ℝ) else 0) + K := by
    intro m hm
    have h := failedMass_le_indicator 𝔊 c₂ x (hprob0 m hm) (hprob1 m hm) τ
    rw [← hK] at h
    have hL : (if ∑ a, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inl a) < τ then (1 : ℝ) else 0) ≤
        (if ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) < β * (𝔊.numSmall : ℝ) / 2
          then (1 : ℝ) else 0) := by
      by_cases hc : ∑ a, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inl a) < τ
      · have h1 : c₄ * ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) ≤
            ∑ a, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inl a) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun a _ => hmin m hm (Sum.inl a)
        have h2 : c₄ * ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) <
            c₄ * (β * (𝔊.numSmall : ℝ) / 2) := by linarith
        have h3 : ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) < β * (𝔊.numSmall : ℝ) / 2 :=
          lt_of_mul_lt_mul_left h2 hc₄.le
        rw [if_pos hc, if_pos h3]
      · rw [if_neg hc]
        split_ifs
        · exact zero_le_one
        · exact le_rfl
    have hR : (if ∑ b, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inr b) < τ then (1 : ℝ) else 0) ≤
        (if ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) < β * (𝔊.numBig : ℝ) / 2
          then (1 : ℝ) else 0) := by
      by_cases hc : ∑ b, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inr b) < τ
      · have h1 : c₄ * ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) ≤
            ∑ b, coinProb 𝔊 c₁ q₀ j (u m) (Sum.inr b) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun b _ => hmin m hm (Sum.inr b)
        have h2 : c₄ * ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) <
            c₄ * (β * (𝔊.numBig : ℝ) / 2) := by linarith
        have h3 : ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) < β * (𝔊.numBig : ℝ) / 2 :=
          lt_of_mul_lt_mul_left h2 hc₄.le
        rw [if_pos hc, if_pos h3]
      · rw [if_neg hc]
        split_ifs
        · exact zero_le_one
        · exact le_rfl
    linarith
  have hLt := hbox.card_lowerTail_le hj hP hM hε0 hε1 hS (fun a => 𝔊.group (Sum.inl a))
    (fun a => hsub _) hdisjL hN₀ hβ (fun a => hsum _) (fun a => hlow _)
  have hRt := hbox.card_lowerTail_le hj hP hM hε0 hε1 hB (fun b => 𝔊.group (Sum.inr b))
    (fun b => hsub _) hdisjR hN₀ hβ (fun b => hsum _) (fun b => hlow _)
  have hc := mul_le_mul_of_nonneg_right hbox.card_le hK0
  calc ∑ m ∈ Ω, failedMass 𝔊 c₁ c₂ q₀ j x (u m)
      ≤ ∑ m ∈ Ω,
          ((if ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) < β * (𝔊.numSmall : ℝ) / 2
              then (1 : ℝ) else 0) +
            (if ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) < β * (𝔊.numBig : ℝ) / 2
              then (1 : ℝ) else 0) + K) := Finset.sum_le_sum hpt
    _ = ((Ω.filter fun m =>
            ∑ a, tee N₀ (𝔊.group (Sum.inl a)) (u m) < β * (𝔊.numSmall : ℝ) / 2).card : ℝ) +
          ((Ω.filter fun m =>
            ∑ b, tee N₀ (𝔊.group (Sum.inr b)) (u m) < β * (𝔊.numBig : ℝ) / 2).card : ℝ) +
            (Ω.card : ℝ) * K := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ M * (8 * teeDiag N₀ / (β ^ 2 * (𝔊.numSmall : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) +
          M * (8 * teeDiag N₀ / (β ^ 2 * (𝔊.numBig : ℝ)) + 16 * teeBar N₀ ^ 2 * ε / β ^ 2) +
            (1 + ε) * M * K := by linarith

/-! ### The candidate groups -/

/-- The model bounds for a group of large primes with reciprocal mass between `(log 2)/2` and
`3 (log 2)/2`: `A_g + B_g ≤ 2j + 1` and `M(n n') ≥ ((log 2)/4)²`. -/
theorem group_model_bounds {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} {B : ℝ}
    (hB1 : 2 * (j : ℝ) ≤ B) (hB2 : 4 * (j : ℝ) / Real.log 2 ≤ B) (hg : ∀ p ∈ g, B ≤ (p : ℝ))
    (hVlo : Real.log 2 / 2 ≤ reciprocalMass g) (hVhi : reciprocalMass g ≤ coinVhi) :
    sumU j g + sumV j g ≤ ((2 * j + 2 : ℕ) : ℝ) - 1 ∧ coinBeta ≤ mdl j 0 g := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt := Real.log_two_lt_d9
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hB0 : 0 < B := by linarith
  have hp2j : ∀ p ∈ g, 2 * j ≤ p := fun p hp => by
    have h : ((2 * j : ℕ) : ℝ) ≤ (p : ℝ) := by
      push_cast
      exact hB1.trans (hg p hp)
    exact_mod_cast h
  have hp1 : ∀ p ∈ g, 1 ≤ p := fun p hp => by
    have := hp2j p hp
    omega
  have hU1 : sumU j g ≤ reciprocalMass g := by
    unfold sumU reciprocalMass
    exact Finset.sum_le_sum fun p hp => alphaU_le hj (hp1 p hp)
  have hU2 : reciprocalMass g / 2 ≤ sumU j g := by
    unfold sumU reciprocalMass
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have h := alphaU_ge hj (hp2j p hp)
    have e : 1 / (p : ℝ) / 2 = 1 / (2 * (p : ℝ)) := by ring
    rw [e]
    exact h
  have hV1 : sumV j g ≤ (j : ℝ) * reciprocalMass g := by
    unfold sumV reciprocalMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h := alphaV_le (j := j) (hp1 p hp)
    have e : (j : ℝ) * (1 / (p : ℝ)) = (j : ℝ) / (p : ℝ) := by ring
    rw [e]
    exact h
  have hV2 : reciprocalMass g ≤ sumV j g := by
    unfold sumV reciprocalMass
    exact Finset.sum_le_sum fun p hp => alphaV_ge hj (hp1 p hp)
  have hδ : ∀ p ∈ g, alphaV j p ≤ Real.log 2 / 4 := by
    intro p hp
    have h1 := alphaV_le (j := j) (hp1 p hp)
    have h2 : (j : ℝ) / (p : ℝ) ≤ (j : ℝ) / B :=
      div_le_div_of_nonneg_left (by linarith) hB0 (hg p hp)
    have h3 : (j : ℝ) / B ≤ Real.log 2 / 4 := by
      rw [div_le_iff₀ hB0]
      have h4 := (div_le_iff₀ hlog2).mp hB2
      linarith
    linarith
  constructor
  · have hcast : ((2 * j + 2 : ℕ) : ℝ) - 1 = 2 * (j : ℝ) + 1 := by
      push_cast
      ring
    have hvhi : reciprocalMass g ≤ 3 * Real.log 2 / 2 := hVhi
    have h1 : (1 + (j : ℝ)) * reciprocalMass g ≤ (1 + (j : ℝ)) * (3 * 0.6931471808 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hcast]
    linarith
  · have h := mdl_zero_ge hj hp1 hδ
    have hV0 : Real.log 2 / 4 ≤ sumV j g - Real.log 2 / 4 := by linarith
    have hU0 : Real.log 2 / 4 ≤ sumU j g := by linarith
    have h4 : (0 : ℝ) ≤ Real.log 2 / 4 := by linarith
    have h5 : Real.log 2 / 4 * (Real.log 2 / 4) ≤
        sumU j g * (sumV j g - Real.log 2 / 4) := mul_le_mul hU0 hV0 h4 (by linarith)
    unfold coinBeta
    rw [sq]
    exact h5.trans h

/-- Each family of candidate groups has at least `(log L)/50` groups, once `log L ≥ 100`. -/
theorem candidateCount_ge {lo hi x : ℝ} (hlh : 0.05 ≤ hi - lo)
    (hLL : 100 ≤ Real.log (Real.log x)) :
    Real.log (Real.log x) / 50 ≤ (candidateCount lo hi x : ℝ) ∧ 1 ≤ candidateCount lo hi x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt := Real.log_two_lt_d9
  have hy : Real.log (Real.log x) / 14 ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    have h1 : Real.log (Real.log x) * Real.log 2 ≤ Real.log (Real.log x) * 0.7 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : Real.log (Real.log x) * 0.05 ≤ Real.log (Real.log x) * (hi - lo) :=
      mul_le_mul_of_nonneg_left hlh (by linarith)
    linarith
  have hfl : (hi - lo) * Real.log (Real.log x) / Real.log 2 - 1 <
      (candidateCount lo hi x : ℝ) := by
    unfold candidateCount
    exact Nat.sub_one_lt_floor _
  have hmain : Real.log (Real.log x) / 50 ≤ (candidateCount lo hi x : ℝ) := by linarith
  refine ⟨hmain, ?_⟩
  have hpos : (0 : ℝ) < (candidateCount lo hi x : ℝ) := by linarith
  exact Nat.succ_le_of_lt (Nat.cast_pos.mp hpos)

/-! ### The arithmetic of the three error terms -/

/-- The Chernoff term: `2 · 2^{(c₃/4) log L} exp(-c₃ (log L)/2) ≤ η/6` for large `log L`. -/
theorem chernoff_tail_le {c₃ LL η : ℝ} (hc₃ : 0 < c₃) (hLL : 0 ≤ LL) (hη : 0 < η)
    (hbig : 4 * (-Real.log (η / 12)) / c₃ ≤ LL) :
    2 * ((2 : ℝ) ^ (c₃ / 4 * LL) * Real.exp (-(c₃ * LL) / 2)) ≤ η / 6 := by
  have hlog2lt := Real.log_two_lt_d9
  have hnn : 0 ≤ c₃ / 4 * LL := mul_nonneg (by linarith) hLL
  have h2 : (2 : ℝ) ^ (c₃ / 4 * LL) ≤ Real.exp (c₃ / 4 * LL) := by
    rw [Real.rpow_def_of_pos two_pos]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right (by linarith : Real.log 2 ≤ 1) hnn
    linarith
  have h3 : Real.exp (c₃ / 4 * LL) * Real.exp (-(c₃ * LL) / 2) = Real.exp (-(c₃ * LL) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (-(c₃ * LL) / 4) ≤ η / 12 := by
    have h5 : 4 * (-Real.log (η / 12)) ≤ LL * c₃ := (div_le_iff₀ hc₃).mp hbig
    have h6 : -(c₃ * LL) / 4 ≤ Real.log (η / 12) := by linarith
    calc Real.exp (-(c₃ * LL) / 4) ≤ Real.exp (Real.log (η / 12)) := Real.exp_le_exp.mpr h6
      _ = η / 12 := Real.exp_log (by positivity)
  have h7 : (2 : ℝ) ^ (c₃ / 4 * LL) * Real.exp (-(c₃ * LL) / 2) ≤ η / 12 := by
    calc (2 : ℝ) ^ (c₃ / 4 * LL) * Real.exp (-(c₃ * LL) / 2)
        ≤ Real.exp (c₃ / 4 * LL) * Real.exp (-(c₃ * LL) / 2) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (-(c₃ * LL) / 4) := h3
      _ ≤ η / 12 := h4
  linarith

/-- The three error terms are `≤ η M`. -/
theorem perBox_arith {M D ν β ε η nL nR LL K : ℝ} (hM : 0 ≤ M) (hβ : 0 < β)
    (hη : 0 < η) (hν : 0 < ν) (hε1 : ε ≤ 1)
    (hε : ε ≤ η * β ^ 2 / (96 * ν ^ 2)) (hLL : 0 < LL) (hnL : LL / 50 ≤ nL)
    (hnR : LL / 50 ≤ nR) (hLL1 : 2400 * D / (β ^ 2 * η) ≤ LL) (hK0 : 0 ≤ K) (hK : K ≤ η / 6) :
    M * (8 * D / (β ^ 2 * nL) + 16 * ν ^ 2 * ε / β ^ 2) +
        M * (8 * D / (β ^ 2 * nR) + 16 * ν ^ 2 * ε / β ^ 2) + (1 + ε) * M * K ≤ η * M := by
  have hβ2 : 0 < β ^ 2 := pow_pos hβ 2
  have hν2 : 0 < ν ^ 2 := pow_pos hν 2
  have hD1 : 2400 * D ≤ LL * (β ^ 2 * η) := (div_le_iff₀ (mul_pos hβ2 hη)).mp hLL1
  have h1 : ∀ n : ℝ, LL / 50 ≤ n → 8 * D / (β ^ 2 * n) ≤ η / 6 := by
    intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
    rw [div_le_iff₀ (mul_pos hβ2 hn0)]
    have h2 : β ^ 2 * η * (LL / 50) ≤ β ^ 2 * η * n :=
      mul_le_mul_of_nonneg_left hn (mul_pos hβ2 hη).le
    linarith
  have h2 : 16 * ν ^ 2 * ε / β ^ 2 ≤ η / 6 := by
    rw [div_le_iff₀ hβ2]
    have h3 : ε * (96 * ν ^ 2) ≤ η * β ^ 2 := (le_div_iff₀ (mul_pos (by norm_num) hν2)).mp hε
    linarith
  have h3 : (1 + ε) * M * K ≤ M * (η / 3) := by
    have h4 : (1 + ε) * K ≤ 2 * (η / 6) := mul_le_mul (by linarith) hK hK0 (by norm_num)
    have h5 := mul_le_mul_of_nonneg_left h4 hM
    linarith
  have h4 := mul_le_mul_of_nonneg_left (add_le_add (h1 nL hnL) h2) hM
  have h5 := mul_le_mul_of_nonneg_left (add_le_add (h1 nR hnR) h2) hM
  linarith

/-! ### One rough product box -/

/-- **The failure probability on a rough product dyad is `o(1)`** (`[P-07:0489–0504]`): for every
`η > 0` and large `x`, uniformly in the boxes with `x^δ ≤ 2^{k_i} ≤ x^C`. -/
theorem eventually_box_failedMass_le (hR : RoughCounts) (hM1 : MertensReciprocal)
    (hM2 : MertensProduct) {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ k : Fin j → ℕ,
      (∀ i, x ^ δ ≤ (2 : ℝ) ^ k i ∧ (2 : ℝ) ^ k i ≤ x ^ C) →
        ∑ m ∈ roughBox x k,
            failedMass (candidateGroups x) (coinC1 q₀) (coinC2 q₀ j) q₀ j x (∏ i, m i - 1) ≤
          η * ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₀, hN₀def⟩ : ∃ N₀ : ℝ, N₀ = ((2 * j + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hN₀1 : 1 ≤ N₀ := by
    rw [hN₀def]
    exact_mod_cast (by omega : 1 ≤ 2 * j + 2)
  have hD : 0 < teeDiag N₀ := teeDiag_pos N₀ (by linarith)
  have hν : 0 < teeBar N₀ := mul_pos (by linarith) (pow_pos (by linarith) 2)
  have hβ := coinBeta_pos
  have hc₁ := coinC1_pos hq₀1
  have hc₄ := coinC4_pos hq₀ hq₀1 hj
  have hc₃ := coinC3_pos hq₀ hq₀1 hj
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min 1 (η * coinBeta ^ 2 / (96 * teeBar N₀ ^ 2)) :=
    ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min one_pos
      (div_pos (mul_pos hη (pow_pos hβ 2)) (mul_pos (by norm_num) (pow_pos hν 2)))
  have hε1 : ε ≤ 1 := by
    rw [hεdef]
    exact min_le_left _ _
  have hε2 : ε ≤ η * coinBeta ^ 2 / (96 * teeBar N₀ ^ 2) := by
    rw [hεdef]
    exact min_le_right _ _
  obtain ⟨Y₀, hY⟩ :=
    dyadicPrimeMass_of_mertensReciprocal hM1 (Real.log 2 / 2) (half_pos hlog2)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max (2 * (j : ℝ)) (4 * (j : ℝ) / Real.log 2) := ⟨_, rfl⟩
  have hLLtend : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hexpTend : Tendsto (fun x : ℝ => Real.exp (Real.log x ^ (0.28 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (show (0 : ℝ) < 0.28 by norm_num)).comp Real.tendsto_log_atTop)
  filter_upwards [eventually_boxEq hR hM2 hj hδ hC hεpos,
    eventually_coinProb_le_one hM1 hq₀.le hq₀1 hj (le_refl (coinC1 q₀)),
    ((tendsto_rpow_atTop (show (0 : ℝ) < 0.28 by norm_num)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop Y₀,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    hexpTend.eventually_ge_atTop B,
    hLLtend.eventually_ge_atTop 100,
    hLLtend.eventually_ge_atTop (2400 * teeDiag N₀ / (coinBeta ^ 2 * η)),
    hLLtend.eventually_ge_atTop (4 * (-Real.log (η / 12)) / coinC3 q₀ j)]
    with x hboxx hprob hY1 hL hBx hLL100 hLL1 hLL2 k hk
  have hL0 : 0 ≤ Real.log x := by linarith
  have hbox := hboxx k hk
  have hVpos := mertensProduct_pos (roughCutoff x)
  have hM0 : 0 ≤ ∏ i, mertensProduct (roughCutoff x) * (2 : ℝ) ^ k i :=
    Finset.prod_nonneg fun i _ => mul_nonneg hVpos.le (pow_nonneg zero_le_two _)
  have hprime : ∀ p ∈ candidatePrimes x, p.Prime := fun p hp =>
    (Strip.candidatePrimes_facts hL hp).1
  have hP1 : ∀ p ∈ candidatePrimes x, 1 ≤ p := fun p hp => (hprime p hp).one_le
  have hsub : ∀ g : (candidateGroups x).Index,
      (candidateGroups x).group g ⊆ candidatePrimes x := fun g =>
    Finset.subset_biUnion_of_mem (candidateGroups x).group (Finset.mem_univ g)
  have h28 : Real.log x ^ (0.28 : ℝ) ≤ Real.log x ^ (0.4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hmass : ∀ g : (candidateGroups x).Index,
      |reciprocalMass ((candidateGroups x).group g) - Real.log 2| ≤ Real.log 2 / 2 := by
    intro g
    rcases g with i | i
    · exact candidateBand_mass hY hL0 hY1 i.val
    · exact candidateBand_mass hY hL0 (hY1.trans h28) i.val
  have hVlo : ∀ g : (candidateGroups x).Index,
      Real.log 2 / 2 ≤ reciprocalMass ((candidateGroups x).group g) := fun g => by
    have := (abs_le.mp (hmass g)).1
    linarith
  have hVhi : ∀ g : (candidateGroups x).Index,
      reciprocalMass ((candidateGroups x).group g) ≤ coinVhi := fun g => by
    have := (abs_le.mp (hmass g)).2
    unfold coinVhi
    linarith
  have hpB : ∀ g : (candidateGroups x).Index, ∀ p ∈ (candidateGroups x).group g,
      B ≤ (p : ℝ) := fun g p hp =>
    hBx.trans (Strip.candidatePrimes_facts hL (hsub g hp)).2.1
  have hmodel : ∀ g : (candidateGroups x).Index,
      sumU j ((candidateGroups x).group g) + sumV j ((candidateGroups x).group g) ≤ N₀ - 1 ∧
        coinBeta ≤ mdl j 0 ((candidateGroups x).group g) := fun g => by
    rw [hN₀def]
    exact group_model_bounds hj (by rw [hBdef]; exact le_max_left _ _)
      (by rw [hBdef]; exact le_max_right _ _) (hpB g) (hVlo g) (hVhi g)
  obtain ⟨hnL, hnL1⟩ :=
    candidateCount_ge (lo := 0.28) (hi := 0.35) (x := x) (by norm_num) hLL100
  obtain ⟨hnR, hnR1⟩ :=
    candidateCount_ge (lo := 0.4) (hi := 0.45) (x := x) (by norm_num) hLL100
  have hdisjL : ∀ a a' : Fin (candidateGroups x).numSmall, a ≠ a' →
      Disjoint ((candidateGroups x).group (Sum.inl a))
        ((candidateGroups x).group (Sum.inl a')) := fun a a' h =>
    candidateBand_disjoint hL0 fun hv => h (Fin.ext hv)
  have hdisjR : ∀ b b' : Fin (candidateGroups x).numBig, b ≠ b' →
      Disjoint ((candidateGroups x).group (Sum.inr b))
        ((candidateGroups x).group (Sum.inr b')) := fun b b' h =>
    candidateBand_disjoint hL0 fun hv => h (Fin.ext hv)
  have hmin : ∀ m ∈ roughBox x k, ∀ g : (candidateGroups x).Index,
      coinC4 q₀ j * tee N₀ ((candidateGroups x).group g) (∏ i, m i - 1) ≤
        coinProb (candidateGroups x) (coinC1 q₀) q₀ j (∏ i, m i - 1) g := fun m _ g => by
    rw [hN₀def]
    exact coinProb_ge_tee (candidateGroups x) hc₁.le hq₀ hq₀1.le hj g
      (lt_of_lt_of_le (half_pos hlog2) (hVlo g)) (hVhi g) _
  have hLLpos : 0 < Real.log (Real.log x) := by linarith
  have hcβ : 0 ≤ coinC4 q₀ j * coinBeta := (mul_pos hc₄ hβ).le
  have hτL : coinC3 q₀ j * Real.log (Real.log x) ≤
      coinC4 q₀ j * (coinBeta * ((candidateGroups x).numSmall : ℝ) / 2) := by
    have h1 : coinC4 q₀ j * coinBeta * (Real.log (Real.log x) / 50) ≤
        coinC4 q₀ j * coinBeta * ((candidateGroups x).numSmall : ℝ) :=
      mul_le_mul_of_nonneg_left hnL hcβ
    unfold coinC3
    linarith
  have hτR : coinC3 q₀ j * Real.log (Real.log x) ≤
      coinC4 q₀ j * (coinBeta * ((candidateGroups x).numBig : ℝ) / 2) := by
    have h1 : coinC4 q₀ j * coinBeta * (Real.log (Real.log x) / 50) ≤
        coinC4 q₀ j * coinBeta * ((candidateGroups x).numBig : ℝ) :=
      mul_le_mul_of_nonneg_left hnR hcβ
    unfold coinC3
    linarith
  have hmainA := sum_failedMass_le hj hP1 hM0 hεpos.le hε1 hbox (candidateGroups x) hnL1 hnR1
    hsub hdisjL hdisjR hN₀1 hβ (fun g => (hmodel g).1) (fun g => (hmodel g).2) (coinC2 q₀ j) x
    (fun m _ g => coinProb_nonneg _ hc₁.le hq₀.le j _ g) (fun m _ g => hprob _ g) hc₄ hmin
    hτL hτR
  have hK : 2 * ((2 : ℝ) ^ (coinC2 q₀ j * Real.log (Real.log x)) *
      Real.exp (-(coinC3 q₀ j * Real.log (Real.log x)) / 2)) ≤ η / 6 :=
    chernoff_tail_le hc₃ hLLpos.le hη hLL2
  have hK0 : 0 ≤ 2 * ((2 : ℝ) ^ (coinC2 q₀ j * Real.log (Real.log x)) *
      Real.exp (-(coinC3 q₀ j * Real.log (Real.log x)) / 2)) :=
    mul_nonneg zero_le_two (mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.exp_pos _).le)
  exact hmainA.trans
    (perBox_arith hM0 hβ hη hν hε1 hε2 hLLpos hnL hnR hLL1 hK0 hK)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Square exceptions (ext:candidate-square-count)

`squareExceptions : SquareExceptions` (`[P-07:0542–0557]`): for a cutoff `Φ`, every `k` and every
`A > 0`, for all large `x`,

`∑_{u ≥ 1, ∃ candidate p, p² ∣ u + 1} Φ(u/x) τ(u+1)^k ≤ x L^{-A}`.

"Cauchy–Schwarz and a fixed divisor moment bound give an exponential saving in a power of `L` for
sums of any fixed divisor power over this exceptional set."

With `M = ⌊R x⌋ + 1` (`Φ` vanishes beyond `R`), `B ≥ Φ`, `W₁ = exp(L^{0.28})` and `ℓ = log(2M)`:

* Cauchy–Schwarz (`shiftSum_mul_sq_le`): `S² ≤ S₀ S₂` with `S₀ = ∑ Φ · 1` and
  `S₂ = ∑ Φ τ^{2k}` over the exceptional set.
* `S₂ ≤ B C₂ M ℓ^{A₂}` by the divisor moment of order `2k` (`divisorMoments`).
* Every candidate prime is at least `W₁` (`candidatePrimes_ge`), so the number of exceptional
  `u < M` is at most `∑_{p ≤ M} M/p² ≤ (M/W₁) ∑_{d ≤ M} 1/d` (`card_square_multiples_le`), and
  `∑_{d ≤ M} 1/d ≤ C₀ ℓ^{A₀}` is the weighted divisor moment of order `0`. Hence
  `S₀ ≤ B (M/W₁) C₀ ℓ^{A₀}`.
* `M ≤ (R+1) x` and `1 ≤ ℓ ≤ 2L`, so `S² ≤ K x² L^{b - 2A} exp(-L^{0.28})` with fixed `K, b`, and
  `K L^b exp(-L^{0.28}) ≤ 1` for large `x` (`square_exceptions_algebra`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- Every candidate prime is at least `exp(L^{0.28})` (`[P-07:0319–0323]`: the bands start at
`y = L^{0.28}` and at `y = L^{0.40}`), once `L ≥ 1`. -/
theorem candidatePrimes_ge {x : ℝ} (hL : 1 ≤ Real.log x) {p : ℕ} (hp : p ∈ candidatePrimes x) :
    Real.exp (Real.log x ^ (0.28 : ℝ)) ≤ (p : ℝ) := by
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  have hL0 : 0 ≤ Real.log x := by linarith
  have h28 : 0 ≤ Real.log x ^ (0.28 : ℝ) := Real.rpow_nonneg hL0 _
  have h40 : 0 ≤ Real.log x ^ (0.4 : ℝ) := Real.rpow_nonneg hL0 _
  have hpow : ∀ j : ℕ, (1 : ℝ) ≤ 2 ^ j := fun j => one_le_pow₀ (by norm_num)
  rcases g with i | i
  · have hmem : p ∈ candidateBand 0.28 x i.val := hg
    have h1 := (mem_candidateBand.mp hmem).2.1
    refine le_trans (Real.exp_le_exp.mpr ?_) h1
    exact le_mul_of_one_le_left h28 (hpow _)
  · have hmem : p ∈ candidateBand 0.4 x i.val := hg
    have h1 := (mem_candidateBand.mp hmem).2.1
    have hle : Real.log x ^ (0.28 : ℝ) ≤ Real.log x ^ (0.4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    refine le_trans (Real.exp_le_exp.mpr ?_) h1
    exact hle.trans (le_mul_of_one_le_left h40 (hpow _))

/-- **Counting square multiples**: if every element of `T` is at least `w > 0`, a set `U` of
integers `u < M` with `u + 1` divisible by the square of an element of `T` has at most
`(M/w) ∑_{d ≤ M} 1/d` elements. -/
theorem card_square_multiples_le {T : Finset ℕ} {w : ℝ} (hw : 0 < w)
    (hT : ∀ p ∈ T, w ≤ (p : ℝ)) (M : ℕ) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u < M ∧ ∃ p ∈ T, p ^ 2 ∣ u + 1) :
    (U.card : ℝ) ≤ (M : ℝ) / w * ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) := by
  obtain ⟨T', hT'⟩ : ∃ T' : Finset ℕ, T' = T.filter (fun p => p ≤ M) := ⟨_, rfl⟩
  have hpos : ∀ p ∈ T, 0 < p := fun p hp =>
    Nat.cast_pos.mp (lt_of_lt_of_le hw (hT p hp))
  have hsub : U ⊆ T'.biUnion fun p => (Finset.range M).filter fun u => p ^ 2 ∣ u + 1 := by
    intro u hu
    obtain ⟨huM, p, hpT, hdvd⟩ := hU u hu
    have hle : p ^ 2 ≤ u + 1 := Nat.le_of_dvd (Nat.succ_pos u) hdvd
    have hpM : p ≤ M :=
      (Nat.le_self_pow two_ne_zero p).trans (hle.trans (Nat.succ_le_of_lt huM))
    refine Finset.mem_biUnion.mpr
      ⟨p, ?_, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huM, hdvd⟩⟩
    rw [hT']
    exact Finset.mem_filter.mpr ⟨hpT, hpM⟩
  have hcard : U.card ≤ ∑ p ∈ T', M / p ^ 2 :=
    calc U.card
        ≤ (T'.biUnion fun p => (Finset.range M).filter fun u => p ^ 2 ∣ u + 1).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ T', ((Finset.range M).filter fun u => p ^ 2 ∣ u + 1).card :=
          Finset.card_biUnion_le
      _ = ∑ p ∈ T', M / p ^ 2 :=
          Finset.sum_congr rfl fun p _ => Nat.card_multiples M (p ^ 2)
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hterm : ∀ p ∈ T', ((M / p ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) / w * (1 / (p : ℝ)) := by
    intro p hp
    rw [hT'] at hp
    have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
    have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (hpos p hpT)
    have hwp : w * (p : ℝ) ≤ (p : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hT p hpT) hp0.le
    calc ((M / p ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (M : ℝ) / (p : ℝ) ^ 2 := by rw [Nat.cast_pow]
      _ ≤ (M : ℝ) / (w * (p : ℝ)) := div_le_div_of_nonneg_left hMnn (mul_pos hw hp0) hwp
      _ = (M : ℝ) / w * (1 / (p : ℝ)) := by rw [div_mul_div_comm, mul_one]
  have hsubT : T' ⊆ Finset.Icc 1 M := by
    intro p hp
    rw [hT'] at hp
    obtain ⟨hpT, hpM⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (hpos p hpT), hpM⟩
  calc (U.card : ℝ) ≤ ((∑ p ∈ T', M / p ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
    _ = ∑ p ∈ T', ((M / p ^ 2 : ℕ) : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ p ∈ T', (M : ℝ) / w * (1 / (p : ℝ)) := Finset.sum_le_sum hterm
    _ = (M : ℝ) / w * ∑ p ∈ T', 1 / (p : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (M : ℝ) / w * ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsubT fun d _ _ => by positivity)
          (div_nonneg hMnn hw.le)

/-- The real-variable inequality at the end of the proof of `squareExceptions`: the product of the
two bounds given by Cauchy–Schwarz is at most `(x L^{-A})²` once
`K L^{a₀ + a₂ + 2A} exp(-L^{0.28}) ≤ 1`. -/
theorem square_exceptions_algebra {B C₀ C₂ R x L Mr ℓ W₁ A₀ A₂ A K : ℝ}
    (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂) (hR : 0 ≤ R) (hx : 0 ≤ x) (hL : 1 ≤ L)
    (hMr0 : 0 ≤ Mr) (hMr : Mr ≤ (R + 1) * x) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 2 * L)
    (hW₁ : W₁ = Real.exp (L ^ (0.28 : ℝ)))
    (hK : K = B * B * (C₀ * C₂) * (R + 1) ^ 2 * ((2 : ℝ) ^ max A₀ 0 * (2 : ℝ) ^ max A₂ 0))
    (hlim : K * (L ^ (max A₀ 0 + max A₂ 0 + A + A) * Real.exp (-(L ^ (0.28 : ℝ)))) ≤ 1) :
    (B * (Mr / W₁ * (C₀ * ℓ ^ A₀))) * (B * (C₂ * Mr * ℓ ^ A₂)) ≤ (x * L ^ (-A)) ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hWinv : W₁⁻¹ = Real.exp (-(L ^ (0.28 : ℝ))) := by
    rw [hW₁, Real.exp_neg]
  have hWinv0 : 0 ≤ W₁⁻¹ := by
    rw [hWinv]
    exact (Real.exp_pos _).le
  -- the powers of `ℓ`
  have hpow : ∀ A' : ℝ, ℓ ^ A' ≤ (2 : ℝ) ^ max A' 0 * L ^ max A' 0 := by
    intro A'
    calc ℓ ^ A' ≤ ℓ ^ max A' 0 := Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)
      _ ≤ (2 * L) ^ max A' 0 := Real.rpow_le_rpow hℓ0 hℓ (le_max_right _ _)
      _ = (2 : ℝ) ^ max A' 0 * L ^ max A' 0 := Real.mul_rpow (by norm_num) hL0.le
  have hℓ₀nn : 0 ≤ ℓ ^ A₀ := Real.rpow_nonneg hℓ0 _
  have hℓ₂nn : 0 ≤ ℓ ^ A₂ := Real.rpow_nonneg hℓ0 _
  have hY₀nn : 0 ≤ (2 : ℝ) ^ max A₀ 0 * L ^ max A₀ 0 := hℓ₀nn.trans (hpow A₀)
  have hRx : 0 ≤ (R + 1) * x := mul_nonneg (by linarith) hx
  have hM2 : Mr * Mr ≤ (R + 1) * x * ((R + 1) * x) := mul_le_mul hMr hMr hMr0 hRx
  have hℓ2 : ℓ ^ A₀ * ℓ ^ A₂ ≤
      (2 : ℝ) ^ max A₀ 0 * L ^ max A₀ 0 * ((2 : ℝ) ^ max A₂ 0 * L ^ max A₂ 0) :=
    mul_le_mul (hpow A₀) (hpow A₂) hℓ₂nn hY₀nn
  have hc0 : 0 ≤ B * B * (C₀ * C₂) * W₁⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hB hB) (mul_nonneg hC₀ hC₂)) hWinv0
  have hXY : Mr * Mr * (ℓ ^ A₀ * ℓ ^ A₂) ≤
      (R + 1) * x * ((R + 1) * x) *
        ((2 : ℝ) ^ max A₀ 0 * L ^ max A₀ 0 * ((2 : ℝ) ^ max A₂ 0 * L ^ max A₂ 0)) :=
    mul_le_mul hM2 hℓ2 (mul_nonneg hℓ₀nn hℓ₂nn) (mul_nonneg hRx hRx)
  -- the powers of `L`
  have hexp : max A₀ 0 + max A₂ 0 = max A₀ 0 + max A₂ 0 + A + A + (-A + -A) := by ring
  have hr1 : L ^ max A₀ 0 * L ^ max A₂ 0 =
      L ^ (max A₀ 0 + max A₂ 0 + A + A) * L ^ (-A + -A) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← hexp]
  have hr2 : (L ^ (-A)) ^ 2 = L ^ (-A + -A) := by
    rw [sq, ← Real.rpow_add hL0]
  have hT0 : 0 ≤ x ^ 2 * L ^ (-A + -A) :=
    mul_nonneg (sq_nonneg x) (Real.rpow_nonneg hL0.le _)
  calc (B * (Mr / W₁ * (C₀ * ℓ ^ A₀))) * (B * (C₂ * Mr * ℓ ^ A₂))
      = B * B * (C₀ * C₂) * W₁⁻¹ * (Mr * Mr * (ℓ ^ A₀ * ℓ ^ A₂)) := by ring
    _ ≤ B * B * (C₀ * C₂) * W₁⁻¹ * ((R + 1) * x * ((R + 1) * x) *
          ((2 : ℝ) ^ max A₀ 0 * L ^ max A₀ 0 * ((2 : ℝ) ^ max A₂ 0 * L ^ max A₂ 0))) :=
        mul_le_mul_of_nonneg_left hXY hc0
    _ = B * B * (C₀ * C₂) * W₁⁻¹ *
          ((R + 1) ^ 2 * x ^ 2 * ((2 : ℝ) ^ max A₀ 0 * (2 : ℝ) ^ max A₂ 0)) *
            (L ^ max A₀ 0 * L ^ max A₂ 0) := by ring
    _ = B * B * (C₀ * C₂) * W₁⁻¹ *
          ((R + 1) ^ 2 * x ^ 2 * ((2 : ℝ) ^ max A₀ 0 * (2 : ℝ) ^ max A₂ 0)) *
            (L ^ (max A₀ 0 + max A₂ 0 + A + A) * L ^ (-A + -A)) := by rw [hr1]
    _ = x ^ 2 * L ^ (-A + -A) *
          (K * (L ^ (max A₀ 0 + max A₂ 0 + A + A) * Real.exp (-(L ^ (0.28 : ℝ))))) := by
        rw [hK, hWinv]
        ring
    _ ≤ x ^ 2 * L ^ (-A + -A) * 1 := mul_le_mul_of_nonneg_left hlim hT0
    _ = (x * L ^ (-A)) ^ 2 := by rw [mul_one, mul_pow, hr2]

/-- **Square exceptions** (`[P-07:0542–0557]`, (ext:candidate-square-count)): the contribution of
the `v = u + 1` divisible by the square of a candidate prime saves every power of `L`. -/
theorem squareExceptions : SquareExceptions := by
  intro Φ hΦ k A _
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨B, hB0, hB⟩ := hΦ.exists_bound
  obtain ⟨C₂, A₂, hC₂, hmom₂⟩ := (divisorMoments (2 * k)).1
  obtain ⟨C₀, A₀, hC₀, hmom₀⟩ := (divisorMoments 0).2
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B * B * (C₀ * C₂) * (R + 1) ^ 2 *
      ((2 : ℝ) ^ max A₀ 0 * (2 : ℝ) ^ max A₂ 0) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB0 hB0) (mul_pos hC₀ hC₂).le)
      (sq_nonneg _)) (mul_pos (Real.rpow_pos_of_pos two_pos _) (Real.rpow_pos_of_pos two_pos _)).le
  -- `K L^b exp(-L^{0.28}) ≤ 1` for large `x`
  have hlim : ∀ᶠ x : ℝ in atTop, K * (Real.log x ^ (max A₀ 0 + max A₂ 0 + A + A) *
      Real.exp (-(Real.log x ^ (0.28 : ℝ)))) ≤ 1 := by
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = max A₀ 0 + max A₂ 0 + A + A := ⟨_, rfl⟩
    rw [← hb]
    have h1 : Tendsto (fun t : ℝ => t ^ (b / 0.28) * Real.exp (-1 * t)) atTop (𝓝 0) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / 0.28) 1 one_pos
    have h2 : Tendsto (fun x : ℝ => Real.log x ^ (0.28 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.28)).comp Real.tendsto_log_atTop
    have h3 : Tendsto (fun x : ℝ => (Real.log x ^ (0.28 : ℝ)) ^ (b / 0.28) *
        Real.exp (-1 * Real.log x ^ (0.28 : ℝ))) atTop (𝓝 0) := h1.comp h2
    have hK1 : 0 < K + 1 := by linarith
    have hε : (0 : ℝ) < 1 / (K + 1) := one_div_pos.mpr hK1
    have h4 : ∀ᶠ x : ℝ in atTop, (Real.log x ^ (0.28 : ℝ)) ^ (b / 0.28) *
        Real.exp (-1 * Real.log x ^ (0.28 : ℝ)) < 1 / (K + 1) :=
      h3.eventually (eventually_lt_nhds hε)
    filter_upwards [h4, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hL0 : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hpow : (Real.log x ^ (0.28 : ℝ)) ^ (b / 0.28) = Real.log x ^ b := by
      rw [← Real.rpow_mul hL0, mul_div_cancel₀ b (by norm_num : (0.28 : ℝ) ≠ 0)]
    rw [hpow, neg_one_mul] at hx
    have hnn : 0 ≤ Real.log x ^ b * Real.exp (-(Real.log x ^ (0.28 : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg hL0 _) (Real.exp_pos _).le
    calc K * (Real.log x ^ b * Real.exp (-(Real.log x ^ (0.28 : ℝ))))
        ≤ (K + 1) * (Real.log x ^ b * Real.exp (-(Real.log x ^ (0.28 : ℝ)))) :=
          mul_le_mul_of_nonneg_right (by linarith) hnn
      _ ≤ (K + 1) * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hx.le hK1.le
      _ = 1 := mul_one_div_cancel hK1.ne'
  filter_upwards [hlim, eventually_ge_atTop (Real.exp 1 / R), eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (2 * (R + 1))] with x hlimx hx1 hx2 hx3
  -- sizes
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx2
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx2
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊R * x⌋₊ + 1 := ⟨_, rfl⟩
  have hRx : 0 ≤ R * x := (mul_pos hR0 hx0).le
  have hRxe : Real.exp 1 ≤ R * x := by
    have h := (div_le_iff₀ hR0).mp hx1
    rwa [mul_comm] at h
  have hMgt : R * x < (M : ℝ) := by
    rw [hM, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hMe : Real.exp 1 ≤ (M : ℝ) := hRxe.trans hMgt.le
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := he1.trans hMe
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMle : (M : ℝ) ≤ (R + 1) * x := by
    have h := Nat.floor_le hRx
    have e : (R + 1) * x = R * x + x := by ring
    rw [hM, Nat.cast_add, Nat.cast_one, e]
    linarith
  have hfloor : ⌊(M : ℝ)⌋₊ = M := Nat.floor_natCast M
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (2 * (M : ℝ)) := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2 * (M : ℝ) by linarith)
    rw [Real.log_exp] at h
    rw [hℓ]
    exact h
  have hℓle : ℓ ≤ 2 * Real.log x := by
    have hpos : 0 < 2 * (R + 1) := by linarith
    have h1 : 2 * (M : ℝ) ≤ 2 * (R + 1) * x :=
      calc 2 * (M : ℝ) ≤ 2 * ((R + 1) * x) := by linarith
        _ = 2 * (R + 1) * x := by ring
    have h2 : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (R + 1) * x) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul hpos.ne' hx0.ne'] at h2
    have h3 : Real.log (2 * (R + 1)) ≤ Real.log x := Real.log_le_log hpos hx3
    rw [hℓ]
    linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : ℝ, W₁ = Real.exp (Real.log x ^ (0.28 : ℝ)) := ⟨_, rfl⟩
  have hW₁pos : 0 < W₁ := by
    rw [hW₁]
    exact Real.exp_pos _
  -- reindexing `n = u + 1`
  have hreindex : ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) →
      ∑ u ∈ Finset.range M, f (u + 1) ≤ ∑ n ∈ Finset.Icc 1 M, f n := by
    intro f hf
    have himg : ∑ u ∈ Finset.range M, f (u + 1) =
        ∑ n ∈ (Finset.range M).image (fun u => u + 1), f n :=
      (Finset.sum_image (add_left_injective 1).injOn).symm
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hf n
    intro n hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr
      ⟨Nat.le_add_left 1 u, Nat.succ_le_of_lt (Finset.mem_range.mp hu)⟩
  -- the second moment: `S₂ ≤ B C₂ M ℓ^{A₂}`
  have hS2 : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
      (fun u => (((u + 1).divisors.card : ℝ) ^ k) ^ 2) ≤ B * (C₂ * (M : ℝ) * ℓ ^ A₂) := by
    have hmom := hmom₂ (M : ℝ) hM1
    rw [hfloor, ← hℓ] at hmom
    rw [shiftSum_eq_sum hR hx0, ← hM]
    calc _ ≤ ∑ u ∈ Finset.range M, B * ((u + 1).divisors.card : ℝ) ^ (2 * k) :=
          Finset.sum_le_sum fun u _ => by
            have hpw : (((u + 1).divisors.card : ℝ) ^ k) ^ 2 =
                ((u + 1).divisors.card : ℝ) ^ (2 * k) := by
              rw [← pow_mul, mul_comm k 2]
            have hnn : 0 ≤ ((u + 1).divisors.card : ℝ) ^ (2 * k) :=
              pow_nonneg (Nat.cast_nonneg _) _
            have key : Φ ((u : ℝ) / x) * (((u + 1).divisors.card : ℝ) ^ k) ^ 2 ≤
                B * ((u + 1).divisors.card : ℝ) ^ (2 * k) := by
              rw [hpw]
              exact mul_le_mul_of_nonneg_right (hB _) hnn
            by_cases h1 : ∃ p ∈ candidatePrimes x, p ^ 2 ∣ u + 1
            · rw [if_pos h1]
              exact key
            · rw [if_neg h1]
              exact mul_nonneg hB0 hnn
      _ = B * ∑ u ∈ Finset.range M, ((u + 1).divisors.card : ℝ) ^ (2 * k) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ B * ∑ n ∈ Finset.Icc 1 M, (n.divisors.card : ℝ) ^ (2 * k) :=
          mul_le_mul_of_nonneg_left
            (hreindex (fun n => (n.divisors.card : ℝ) ^ (2 * k))
              fun n => pow_nonneg (Nat.cast_nonneg _) _) hB0
      _ ≤ B * (C₂ * (M : ℝ) * ℓ ^ A₂) := mul_le_mul_of_nonneg_left hmom hB0
  -- the count: `S₀ ≤ B (M / W₁) C₀ ℓ^{A₀}`
  have hMW0 : 0 ≤ (M : ℝ) / W₁ := div_nonneg hMnn hW₁pos.le
  have hS0 : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
      (fun _ => (1 : ℝ) ^ 2) ≤ B * ((M : ℝ) / W₁ * (C₀ * ℓ ^ A₀)) := by
    classical
    obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = (Finset.range M).filter
        (fun u => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ u + 1) := ⟨_, rfl⟩
    have hUcard : (U.card : ℝ) ≤ (M : ℝ) / W₁ * ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) :=
      card_square_multiples_le (T := candidatePrimes x) hW₁pos
        (fun p hp => by
          rw [hW₁]
          exact candidatePrimes_ge hL1 hp) M U
        (fun u hu => by
          rw [hU] at hu
          exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩)
    have hharm : ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) ≤ C₀ * ℓ ^ A₀ := by
      have h := hmom₀ (M : ℝ) hM1
      rw [hfloor, ← hℓ] at h
      refine le_trans (le_of_eq ?_) h
      exact Finset.sum_congr rfl fun d _ => by rw [pow_zero]
    rw [shiftSum_eq_sum hR hx0, ← hM]
    calc _ ≤ ∑ u ∈ Finset.range M, (if u ∈ U then B else 0) :=
          Finset.sum_le_sum fun u hu => by
            by_cases h1 : ∃ p ∈ candidatePrimes x, p ^ 2 ∣ u + 1
            · have hmemU : u ∈ U := by
                rw [hU]
                exact Finset.mem_filter.mpr ⟨hu, h1⟩
              have key : Φ ((u : ℝ) / x) * (1 : ℝ) ^ 2 ≤ B := by
                rw [one_pow, mul_one]
                exact hB _
              rw [if_pos h1, if_pos hmemU]
              exact key
            · rw [if_neg h1]
              split_ifs
              · exact hB0
              · exact le_rfl
      _ = ∑ _u ∈ Finset.range M ∩ U, B := Finset.sum_ite_mem _ _ _
      _ = ((Finset.range M ∩ U).card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (U.card : ℝ) * B :=
          mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) hB0
      _ ≤ ((M : ℝ) / W₁ * (C₀ * ℓ ^ A₀)) * B :=
          mul_le_mul_of_nonneg_right
            (hUcard.trans (mul_le_mul_of_nonneg_left hharm hMW0)) hB0
      _ = B * ((M : ℝ) / W₁ * (C₀ * ℓ ^ A₀)) := mul_comm _ _
  -- Cauchy–Schwarz
  have hCS : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
        (fun u => (1 : ℝ) * ((u + 1).divisors.card : ℝ) ^ k) ^ 2 ≤
      shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v) (fun _ => (1 : ℝ) ^ 2) *
        shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
          (fun u => (((u + 1).divisors.card : ℝ) ^ k) ^ 2) :=
    shiftSum_mul_sq_le hR hx0 hΦ.nonneg _ (fun _ => (1 : ℝ))
      (fun u => ((u + 1).divisors.card : ℝ) ^ k)
  have hSeq : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
        (fun u => (1 : ℝ) * ((u + 1).divisors.card : ℝ) ^ k) =
      shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
        (fun u => ((u + 1).divisors.card : ℝ) ^ k) :=
    shiftSum_congr Φ x _ fun u => one_mul _
  have hS2nn : 0 ≤ shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
      (fun u => (((u + 1).divisors.card : ℝ) ^ k) ^ 2) :=
    shiftSum_nonneg hΦ.nonneg _ fun u => sq_nonneg _
  have hbound0 : 0 ≤ B * ((M : ℝ) / W₁ * (C₀ * ℓ ^ A₀)) :=
    mul_nonneg hB0 (mul_nonneg hMW0 (mul_nonneg hC₀.le (Real.rpow_nonneg hℓ0 _)))
  have hSnn : 0 ≤ shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
      (fun u => ((u + 1).divisors.card : ℝ) ^ k) :=
    shiftSum_nonneg hΦ.nonneg _ fun u => pow_nonneg (Nat.cast_nonneg _) _
  have hTnn : 0 ≤ x * Real.log x ^ (-A) := mul_nonneg hx0.le (Real.rpow_nonneg hL0.le _)
  have hsq : shiftSum Φ x (fun v => ∃ p ∈ candidatePrimes x, p ^ 2 ∣ v)
        (fun u => ((u + 1).divisors.card : ℝ) ^ k) ^ 2 ≤
      (B * ((M : ℝ) / W₁ * (C₀ * ℓ ^ A₀))) * (B * (C₂ * (M : ℝ) * ℓ ^ A₂)) := by
    rw [← hSeq]
    exact hCS.trans (mul_le_mul hS0 hS2 hS2nn hbound0)
  have halg := square_exceptions_algebra hB0 hC₀.le hC₂.le hR0.le hx0.le hL1 hMnn hMle hℓ1 hℓle
    hW₁ hK hlimx
  exact (sq_le_sq₀ hSnn hTnn).mp (hsq.trans halg)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

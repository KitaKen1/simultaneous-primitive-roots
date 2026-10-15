module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Objects

/-!
# The sizes of the error terms of Lemma 7.2

Real-variable inequalities for the last step of [P] Lemma 7.2 (`[P-07:0139–0146, 0170–0190]`), with
`L = log x`, the truncation degree `k = h + 1`, `h = ⌊L^{.01}⌋`, and the bound
`P_max = exp(2 L^{.2})` for the primes of the bands.

* `pow_le_exp_four`: `P_max^{h+1} ≤ exp(4 L^{.47})`: "every divisor in the truncation or the error
  envelope satisfies `d' ≤ exp(O_K((h_0+1) L^{.2})) ≤ exp(O_K(L^{.22})) = x^{o(1)}`"
  (ext:model-divisor-size).
* `tail_bounds`: `e^{-(h+1)} ≤ L^{-(A+2)}` and `exp(-L^{.1}) ≤ L^{-(A+2)}` once
  `L^{A+2} ≤ e^h`: the Bonferroni tail (ext:bonferroni-tail) and the reciprocal of a band prime
  ("`≪ L exp(-L^{.1})`") save every fixed power of `L`.
* `rounding_bound`: the rounding errors, `x^{c₀} · #I · x^{o(1)} ≤ x L^{-A}` when
  `#I ≤ B x^{1 - c₀ - δ}` (ext:rounding-sum).
* `main_error_bound`: the tail and the forced absences, summed over `r` with the weight `1/r`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

noncomputable section

/-- **(ext:model-divisor-size)**: `exp(2 L^{.2})^{h+1} ≤ exp(4 L^{.47})` for `h ≤ L^{.01}`,
`L ≥ 1`. -/
theorem pow_le_exp_four {L : ℝ} (hL1 : 1 ≤ L) {h : ℕ} (hh : (h : ℝ) ≤ L ^ (0.01 : ℝ)) :
    Real.exp (2 * L ^ (1 / 5 : ℝ)) ^ (h + 1) ≤ Real.exp (4 * L ^ (0.47 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have h01 : 1 ≤ L ^ (0.01 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have h15 : 0 ≤ L ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
  have hsplit : L ^ (0.01 : ℝ) * L ^ (1 / 5 : ℝ) ≤ L ^ (0.47 : ℝ) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hk : ((h + 1 : ℕ) : ℝ) ≤ 2 * L ^ (0.01 : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  calc ((h + 1 : ℕ) : ℝ) * (2 * L ^ (1 / 5 : ℝ))
      ≤ 2 * L ^ (0.01 : ℝ) * (2 * L ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hk (mul_nonneg zero_le_two h15)
    _ = 4 * (L ^ (0.01 : ℝ) * L ^ (1 / 5 : ℝ)) := by ring
    _ ≤ 4 * L ^ (0.47 : ℝ) := mul_le_mul_of_nonneg_left hsplit (by norm_num)

/-- **The tails save every power of `L`**: if `L^{A+2} ≤ e^h` with `h ≤ L^{.01}`, then
`e^{-(h+1)} ≤ L^{-(A+2)}` and `exp(-L^{.1}) ≤ L^{-(A+2)}`. -/
theorem tail_bounds {L A : ℝ} (hL1 : 1 ≤ L) {h : ℕ} (hh : (h : ℝ) ≤ L ^ (0.01 : ℝ))
    (htail : L ^ (A + 2) ≤ Real.exp 1 ^ h) :
    (Real.exp 1 ^ (h + 1))⁻¹ ≤ L ^ (-(A + 2)) ∧
      (Real.exp (L ^ (1 / 10 : ℝ)))⁻¹ ≤ L ^ (-(A + 2)) := by
  have hL0 : 0 < L := by linarith
  have hLA : 0 < L ^ (A + 2) := Real.rpow_pos_of_pos hL0 _
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hpos : 0 < Real.exp 1 ^ h := pow_pos (Real.exp_pos 1) h
  have hinv : (Real.exp 1 ^ h)⁻¹ ≤ L ^ (-(A + 2)) := by
    rw [Real.rpow_neg hL0.le]
    exact inv_anti₀ hLA htail
  constructor
  · exact (inv_anti₀ hpos (pow_le_pow_right₀ he1 (Nat.le_succ h))).trans hinv
  · have h1 : Real.exp 1 ^ h ≤ Real.exp (L ^ (1 / 10 : ℝ)) := by
      rw [← Real.exp_nat_mul, mul_one]
      refine Real.exp_le_exp.mpr (hh.trans ?_)
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    exact (inv_anti₀ hpos h1).trans hinv

/-- **The rounding errors** (ext:rounding-sum): if `N₀ ≤ x^{c₀}`, the family has at most
`B_I x^{1 - c₀ - δ}` members, the divisors are at most `exp(4 L^{.47})` and
`x^{-δ} exp(4 L^{.47}) L^A ≤ 1`, then
`N₀ · H_b · #I · C_Φ · 2 P_k E_V ≤ 2 H_b B_I C_Φ E_V · x L^{-A}`. -/
theorem rounding_bound {x c₀ δ A : ℝ} (hx : 1 < x) {N₀ : ℕ} (hN₀ : (N₀ : ℝ) ≤ x ^ c₀)
    {card BI Pk Hb CΦ EV : ℝ} (hcard0 : 0 ≤ card) (hcard : card ≤ BI * x ^ (1 - c₀ - δ))
    (hBI : 0 ≤ BI) (hPk0 : 0 ≤ Pk) (hPk : Pk ≤ Real.exp (4 * Real.log x ^ (0.47 : ℝ)))
    (hHb : 0 ≤ Hb) (hCΦ : 0 ≤ CΦ) (hEV : 0 ≤ EV)
    (hround : x ^ (-δ) * Real.exp (4 * Real.log x ^ (0.47 : ℝ)) * Real.log x ^ A ≤ 1) :
    (N₀ : ℝ) * (Hb * (card * CΦ * (2 * (Pk * EV)))) ≤
      2 * Hb * BI * CΦ * EV * (x * Real.log x ^ (-A)) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos hx
  obtain ⟨E4, hE4⟩ : ∃ E4 : ℝ, E4 = Real.exp (4 * Real.log x ^ (0.47 : ℝ)) := ⟨_, rfl⟩
  rw [← hE4] at hPk hround
  have hxc : 0 ≤ x ^ c₀ := Real.rpow_nonneg hx0.le _
  have hxd : 0 ≤ x ^ (1 - c₀ - δ) := Real.rpow_nonneg hx0.le _
  have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
  have h1 : (N₀ : ℝ) * card * Pk ≤ x ^ c₀ * (BI * x ^ (1 - c₀ - δ)) * E4 :=
    mul_le_mul (mul_le_mul hN₀ hcard hcard0 hxc) hPk hPk0
      (mul_nonneg hxc (mul_nonneg hBI hxd))
  have h2 : x ^ c₀ * x ^ (1 - c₀ - δ) = x * x ^ (-δ) := by
    rw [← Real.rpow_add hx0, show (c₀ + (1 - c₀ - δ) : ℝ) = 1 + -δ by ring,
      Real.rpow_add hx0, Real.rpow_one]
  have h3 : x ^ (-δ) * E4 ≤ Real.log x ^ (-A) := by
    rw [Real.rpow_neg hL0.le A, ← one_div, le_div_iff₀ hLA]
    exact hround
  have h4 : x ^ c₀ * (BI * x ^ (1 - c₀ - δ)) * E4 = BI * (x * (x ^ (-δ) * E4)) :=
    calc x ^ c₀ * (BI * x ^ (1 - c₀ - δ)) * E4
        = BI * (x ^ c₀ * x ^ (1 - c₀ - δ)) * E4 := by ring
      _ = BI * (x * x ^ (-δ)) * E4 := by rw [h2]
      _ = BI * (x * (x ^ (-δ) * E4)) := by ring
  have h5 : (N₀ : ℝ) * card * Pk ≤ BI * (x * Real.log x ^ (-A)) := by
    rw [h4] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hx0.le) hBI)
  have hc : 0 ≤ 2 * Hb * CΦ * EV :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hHb) hCΦ) hEV
  calc (N₀ : ℝ) * (Hb * (card * CΦ * (2 * (Pk * EV))))
      = 2 * Hb * CΦ * EV * ((N₀ : ℝ) * card * Pk) := by ring
    _ ≤ 2 * Hb * CΦ * EV * (BI * (x * Real.log x ^ (-A))) := mul_le_mul_of_nonneg_left h5 hc
    _ = 2 * Hb * BI * CΦ * EV * (x * Real.log x ^ (-A)) := by ring

/-- **The tail and the forced absences, summed over `r`**: with `T₂ ≤ L^{-(A+2)} E` and
`B ≤ L^{-(A+2)} c₀ L`,
`(x/H) I_Φ C (1 + log N₀) · 2 H_b (T₂ + B) ≤ 2 H_b B_I I_Φ (1 + c₀)(E + c₀) · x L^{-A}`. -/
theorem main_error_bound {x A c₀ : ℝ} (hx : 1 < x) (hL1 : 1 ≤ Real.log x) (hc₀ : 0 ≤ c₀)
    {H : ℕ} (hH : 0 < H) {IΦ CI BI Hb logN T₂ B EV2 : ℝ}
    (hIΦ : 0 ≤ IΦ) (hCI0 : 0 ≤ CI) (hCI : CI ≤ BI) (hHb : 0 ≤ Hb)
    (hlogN0 : 0 ≤ 1 + logN) (hlogN : logN ≤ c₀ * Real.log x)
    (hT₂0 : 0 ≤ T₂) (hB0 : 0 ≤ B) (hEV2 : 0 ≤ EV2)
    (hT₂ : T₂ ≤ Real.log x ^ (-(A + 2)) * EV2)
    (hB : B ≤ Real.log x ^ (-(A + 2)) * (c₀ * Real.log x)) :
    x / (H : ℝ) * IΦ * CI * (1 + logN) * (2 * Hb * (T₂ + B)) ≤
      2 * Hb * BI * IΦ * (1 + c₀) * (EV2 + c₀) * (x * Real.log x ^ (-A)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  rw [← hL] at hL1 hlogN hT₂ hB ⊢
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have h1 : x / (H : ℝ) ≤ x := div_le_self hx0.le hH1
  have h4 : 1 + logN ≤ (1 + c₀) * L := by linarith
  have hp : 0 ≤ L ^ (-(A + 2)) := Real.rpow_nonneg hL0.le _
  have h5a : T₂ + B ≤ L ^ (-(A + 2)) * ((EV2 + c₀) * L) := by
    have h6 : EV2 ≤ EV2 * L := le_mul_of_one_le_right hEV2 hL1
    have h7 : L ^ (-(A + 2)) * EV2 ≤ L ^ (-(A + 2)) * (EV2 * L) :=
      mul_le_mul_of_nonneg_left h6 hp
    calc T₂ + B ≤ L ^ (-(A + 2)) * EV2 + L ^ (-(A + 2)) * (c₀ * L) := add_le_add hT₂ hB
      _ ≤ L ^ (-(A + 2)) * (EV2 * L) + L ^ (-(A + 2)) * (c₀ * L) := add_le_add h7 le_rfl
      _ = L ^ (-(A + 2)) * ((EV2 + c₀) * L) := by ring
  have h5 : 2 * Hb * (T₂ + B) ≤ 2 * Hb * (L ^ (-(A + 2)) * ((EV2 + c₀) * L)) :=
    mul_le_mul_of_nonneg_left h5a (mul_nonneg zero_le_two hHb)
  have h50 : 0 ≤ 2 * Hb * (T₂ + B) :=
    mul_nonneg (mul_nonneg zero_le_two hHb) (add_nonneg hT₂0 hB0)
  have hBI : 0 ≤ BI := hCI0.trans hCI
  have h40 : 0 ≤ (1 + c₀) * L := mul_nonneg (by linarith) hL0.le
  have hxI : 0 ≤ x * IΦ := mul_nonneg hx0.le hIΦ
  have hpow : L * L * L ^ (-(A + 2)) = L ^ (-A) := by
    rw [show (-(A + 2) : ℝ) = -A + -1 + -1 by ring, Real.rpow_add hL0, Real.rpow_add hL0,
      Real.rpow_neg_one]
    calc L * L * (L ^ (-A) * L⁻¹ * L⁻¹) = L ^ (-A) * (L * L⁻¹) * (L * L⁻¹) := by ring
      _ = L ^ (-A) := by rw [mul_inv_cancel₀ hLne, mul_one, mul_one]
  calc x / (H : ℝ) * IΦ * CI * (1 + logN) * (2 * Hb * (T₂ + B))
      ≤ x * IΦ * BI * ((1 + c₀) * L) * (2 * Hb * (L ^ (-(A + 2)) * ((EV2 + c₀) * L))) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hIΦ) hCI hCI0 hxI) h4 hlogN0
            (mul_nonneg hxI hBI))
          h5 h50 (mul_nonneg (mul_nonneg hxI hBI) h40)
    _ = 2 * Hb * BI * IΦ * (1 + c₀) * (EV2 + c₀) * (x * (L * L * L ^ (-(A + 2)))) := by ring
    _ = 2 * Hb * BI * IΦ * (1 + c₀) * (EV2 + c₀) * (x * L ^ (-A)) := by rw [hpow]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripBad

/-!
# The coefficient comparison for the stripping step

`[P-07:0347–0372]`: the proxy coefficient `a(m) = 1_{m > x^γ} 1_{P⁻(m) > W} κ(m)` and the stripped
coefficient `ã(m) = 1_{P⁻(m) > W} 1_{m̄ > x^γ} κ(m̄)` are compared pointwise. With
`κ₀ = 1/(V(W) ℓ)`, `ℓ = log x^γ`, and for every `m ≥ 1`:

* `|a(m)| ≤ κ₀ ρ(m)` and `|ã(m)| ≤ κ₀ ρ(m)`, `ρ(m) = 1_{m > x^γ} 1_{P⁻(m) > W}` (`rhoW`);
* `|a(m) - ã(m)| ≤ κ₀ θ(m)`, `θ = ρ (β + σ + ε₀)` (`thetaW`), where `β` is the indicator of the
  integers that are not good (`badW`), `σ` is the indicator of the strip `x^γ < m ≤ x^γ e^Λ`
  (`stripW`) and `ε₀ = Λ/ℓ`.

This is `coeff_bounds`: "if `log(m/m̄) ≤ L^{.9}` and `m̄ > x^γ`, then
`κ(m̄) - κ(m) ≪ L^{-.1} κ(m)`; if `m̄ ≤ x^γ < m`, then `m` lies in the strip"
(`[P-07:0362–0372]`). The hypothesis `hgood` (`m ≤ m̄ e^Λ` for good `m`) is `Strip.good_le`.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

/-! ### The part of `m` away from `P` -/

/-- `m̄ ≥ 1`. -/
theorem freePart_pos (P : Finset ℕ) (n : ℕ) : 0 < freePart P n := by
  unfold freePart
  exact Finset.prod_pos fun p hp =>
    pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_filter.mp hp).1) _

/-- `m̄ ≤ m` for `m ≥ 1`. -/
theorem freePart_le (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0) : freePart P n ≤ n := by
  have h : freePart P n ∣ freePart ∅ n := by
    unfold freePart
    exact Finset.prod_dvd_prod_of_subset _ _ _ fun p hp =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, Finset.notMem_empty p⟩
  rw [freePart_empty hn] at h
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h

/-! ### The value of `κ` above `x^γ` -/

/-- For `m > x^γ ≥ 1` and `ℓ = log x^γ > 0`: `log m > ℓ`, `κ(m) = 1/(V(W) log m)` and
`0 ≤ κ(m) ≤ 1/(V(W) ℓ)`. -/
theorem proxyKappa_facts {x γ ℓ : ℝ} (hA : 1 ≤ x ^ γ) (hℓ : 0 < ℓ)
    (hlog : Real.log (x ^ γ) = ℓ) {m : ℕ} (hm : x ^ γ < (m : ℝ)) :
    ℓ < Real.log m ∧
      proxyKappa x m = 1 / (mertensProduct (roughCutoff x) * Real.log m) ∧
      0 ≤ proxyKappa x m ∧ proxyKappa x m ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) := by
  have hV := mertensProduct_pos (roughCutoff x)
  have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_le_of_lt hA hm
  have hm1' : 1 < m := by exact_mod_cast hm1
  have hlt : ℓ < Real.log m := by
    rw [← hlog]
    exact Real.log_lt_log (lt_of_lt_of_le one_pos hA) hm
  have heq : proxyKappa x m = 1 / (mertensProduct (roughCutoff x) * Real.log m) := by
    unfold proxyKappa
    exact if_pos (Nat.succ_le_of_lt hm1')
  have hpos : 0 < mertensProduct (roughCutoff x) * Real.log m := mul_pos hV (hℓ.trans hlt)
  refine ⟨hlt, heq, ?_, ?_⟩
  · rw [heq]
    exact (one_div_pos.mpr hpos).le
  · rw [heq]
    exact one_div_le_one_div_of_le (mul_pos hV hℓ) (mul_le_mul_of_nonneg_left hlt.le hV.le)

/-! ### The weights -/

open _root_.Classical in
/-- `ρ(m) = 1_{m > x^γ} 1_{P⁻(m) > W}`: the common support of the two coefficients. -/
def rhoW (x γ : ℝ) (m : ℕ) : ℝ :=
  if x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m then 1 else 0

open _root_.Classical in
/-- `β(m) = 1` if `m` is not good, `0` otherwise. -/
def badW (P : Finset ℕ) (Λ₀ : ℝ) (m : ℕ) : ℝ := if Good P Λ₀ m then 0 else 1

open _root_.Classical in
/-- `σ(m) = 1_{x^γ < m ≤ x^γ e^Λ} 1_{P⁻(m) > W}`: the strip. -/
def stripW (x γ Λ : ℝ) (m : ℕ) : ℝ :=
  if x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m then
    (if (m : ℝ) ≤ x ^ γ * Real.exp Λ then 1 else 0) else 0

/-- `θ = ρ (β + σ + ε₀)`: the weight of the difference `a - ã`. -/
def thetaW (x γ : ℝ) (P : Finset ℕ) (Λ₀ Λ ε₀ : ℝ) (m : ℕ) : ℝ :=
  rhoW x γ m * (badW P Λ₀ m + stripW x γ Λ m + ε₀)

theorem rhoW_of {x γ : ℝ} {m : ℕ} (h : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m) :
    rhoW x γ m = 1 := by
  unfold rhoW
  exact if_pos h

theorem rhoW_of_not {x γ : ℝ} {m : ℕ} (h : ¬ (x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m)) :
    rhoW x γ m = 0 := by
  unfold rhoW
  exact if_neg h

theorem rhoW_nonneg (x γ : ℝ) (m : ℕ) : 0 ≤ rhoW x γ m := by
  by_cases h : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m
  · rw [rhoW_of h]
    exact zero_le_one
  · rw [rhoW_of_not h]

theorem badW_of {P : Finset ℕ} {Λ₀ : ℝ} {m : ℕ} (h : Good P Λ₀ m) : badW P Λ₀ m = 0 := by
  unfold badW
  exact if_pos h

theorem badW_of_not {P : Finset ℕ} {Λ₀ : ℝ} {m : ℕ} (h : ¬ Good P Λ₀ m) : badW P Λ₀ m = 1 := by
  unfold badW
  exact if_neg h

theorem badW_nonneg (P : Finset ℕ) (Λ₀ : ℝ) (m : ℕ) : 0 ≤ badW P Λ₀ m := by
  by_cases h : Good P Λ₀ m
  · rw [badW_of h]
  · rw [badW_of_not h]
    exact zero_le_one

theorem stripW_nonneg (x γ Λ : ℝ) (m : ℕ) : 0 ≤ stripW x γ Λ m := by
  unfold stripW
  split_ifs <;> norm_num

theorem thetaW_nonneg {ε₀ : ℝ} (hε : 0 ≤ ε₀) (x γ : ℝ) (P : Finset ℕ) (Λ₀ Λ : ℝ) (m : ℕ) :
    0 ≤ thetaW x γ P Λ₀ Λ ε₀ m := by
  unfold thetaW
  exact mul_nonneg (rhoW_nonneg x γ m)
    (add_nonneg (add_nonneg (badW_nonneg P Λ₀ m) (stripW_nonneg x γ Λ m)) hε)

/-- `θ ≤ β + σ + ε₀ ρ`. -/
theorem thetaW_le (x γ : ℝ) (P : Finset ℕ) (Λ₀ Λ ε₀ : ℝ) (m : ℕ) :
    thetaW x γ P Λ₀ Λ ε₀ m ≤ badW P Λ₀ m + stripW x γ Λ m + ε₀ * rhoW x γ m := by
  unfold thetaW
  by_cases hρ : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m
  · rw [rhoW_of hρ, one_mul, mul_one]
  · rw [rhoW_of_not hρ, zero_mul, mul_zero, add_zero]
    exact add_nonneg (badW_nonneg P Λ₀ m) (stripW_nonneg x γ Λ m)

/-- The reciprocal sum of `θ` is at most those of `β`, `σ` and `ε₀ ρ`. -/
theorem sum_thetaW_div_le (x γ : ℝ) (P : Finset ℕ) (Λ₀ Λ ε₀ : ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, thetaW x γ P Λ₀ Λ ε₀ m / (m : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 N, badW P Λ₀ m / (m : ℝ) +
        ∑ m ∈ Finset.Icc 1 N, stripW x γ Λ m / (m : ℝ) +
          ε₀ * ∑ m ∈ Finset.Icc 1 N, rhoW x γ m / (m : ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  have h := div_le_div_of_nonneg_right (thetaW_le x γ P Λ₀ Λ ε₀ m) (Nat.cast_nonneg m)
  calc thetaW x γ P Λ₀ Λ ε₀ m / (m : ℝ)
      ≤ (badW P Λ₀ m + stripW x γ Λ m + ε₀ * rhoW x γ m) / (m : ℝ) := h
    _ = badW P Λ₀ m / (m : ℝ) + stripW x γ Λ m / (m : ℝ) + ε₀ * (rhoW x γ m / (m : ℝ)) := by
        rw [add_div, add_div, mul_div_assoc]

open _root_.Classical in
/-- `ρ` is below the rough indicator on `(x^γ, B]` at the integers `m ≤ B`. -/
theorem rhoW_le_block {x γ B : ℝ} {m : ℕ} (hm : (m : ℝ) ≤ B) :
    rhoW x γ m ≤ if x ^ γ < (m : ℝ) ∧ (m : ℝ) ≤ B then
      (if IsRough (roughCutoff x) m then (1 : ℝ) else 0) else 0 := by
  by_cases hρ : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m
  · rw [rhoW_of hρ, if_pos (⟨hρ.1, hm⟩ : x ^ γ < (m : ℝ) ∧ (m : ℝ) ≤ B),
      if_pos hρ.2]
  · rw [rhoW_of_not hρ]
    split_ifs <;> norm_num

open _root_.Classical in
/-- `σ` is below the rough indicator on `(x^γ, B]` when `x^γ e^Λ ≤ B`. -/
theorem stripW_le_block {x γ Λ B : ℝ} (hB : x ^ γ * Real.exp Λ ≤ B) (m : ℕ) :
    stripW x γ Λ m ≤ if x ^ γ < (m : ℝ) ∧ (m : ℝ) ≤ B then
      (if IsRough (roughCutoff x) m then (1 : ℝ) else 0) else 0 := by
  unfold stripW
  by_cases hρ : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m
  · rw [if_pos hρ]
    by_cases hs : (m : ℝ) ≤ x ^ γ * Real.exp Λ
    · rw [if_pos hs, if_pos (⟨hρ.1, hs.trans hB⟩ : x ^ γ < (m : ℝ) ∧ (m : ℝ) ≤ B),
        if_pos hρ.2]
    · rw [if_neg hs]
      split_ifs <;> norm_num
  · rw [if_neg hρ]
    split_ifs <;> norm_num

/-! ### The comparison -/

/-- **The coefficient comparison** (`[P-07:0362–0372]`). For `m ≥ 1`, with `κ₀ = 1/(V(W) ℓ)`:
`|a(m)|, |ã(m)| ≤ κ₀ ρ(m)` and `|a(m) - ã(m)| ≤ κ₀ θ(m)`. -/
theorem coeff_bounds {x γ ℓ Λ₀ Λ ε₀ : ℝ} {P : Finset ℕ} (hA : 1 ≤ x ^ γ) (hℓ : 0 < ℓ)
    (hlog : Real.log (x ^ γ) = ℓ) (hΛ : 0 ≤ Λ) (hε : ε₀ = Λ / ℓ)
    (hgood : ∀ m : ℕ, m ≠ 0 → Good P Λ₀ m → (m : ℝ) ≤ (freePart P m : ℝ) * Real.exp Λ)
    {m : ℕ} (hm : m ≠ 0) :
    |proxyCoeff x γ m| ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) * rhoW x γ m ∧
      |strippedCoeff x γ P m| ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) * rhoW x γ m ∧
      |proxyCoeff x γ m - strippedCoeff x γ P m| ≤
        1 / (mertensProduct (roughCutoff x) * ℓ) * thetaW x γ P Λ₀ Λ ε₀ m := by
  have hV := mertensProduct_pos (roughCutoff x)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : ℝ, κ₀ = 1 / (mertensProduct (roughCutoff x) * ℓ) := ⟨_, rfl⟩
  rw [← hκ₀]
  have hκpos : 0 < κ₀ := by
    rw [hκ₀]
    exact one_div_pos.mpr (mul_pos hV hℓ)
  have hbar_pos : (0 : ℝ) < (freePart P m : ℝ) := Nat.cast_pos.mpr (freePart_pos P m)
  have hbar_le : (freePart P m : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (freePart_le P hm)
  have hε0 : 0 ≤ ε₀ := by
    rw [hε]
    exact div_nonneg hΛ hℓ.le
  have hbad0 := badW_nonneg P Λ₀ m
  have hstrip0 := stripW_nonneg x γ Λ m
  by_cases hρ : x ^ γ < (m : ℝ) ∧ IsRough (roughCutoff x) m
  · obtain ⟨hlt, heq, h0, hle⟩ := proxyKappa_facts hA hℓ hlog hρ.1
    rw [← hκ₀] at hle
    have ha : proxyCoeff x γ m = proxyKappa x m := by
      unfold proxyCoeff
      exact if_pos hρ
    have hσ : stripW x γ Λ m = if (m : ℝ) ≤ x ^ γ * Real.exp Λ then 1 else 0 := by
      unfold stripW
      exact if_pos hρ
    have hθ : thetaW x γ P Λ₀ Λ ε₀ m = badW P Λ₀ m + stripW x γ Λ m + ε₀ := by
      unfold thetaW
      rw [rhoW_of hρ, one_mul]
    rw [ha, rhoW_of hρ, hθ, mul_one]
    by_cases hbar : x ^ γ < (freePart P m : ℝ)
    · obtain ⟨hlt', heq', h0', hle'⟩ := proxyKappa_facts hA hℓ hlog hbar
      rw [← hκ₀] at hle'
      have hb : strippedCoeff x γ P m = proxyKappa x (freePart P m) := by
        unfold strippedCoeff
        exact if_pos ⟨hρ.2, hbar⟩
      rw [hb]
      refine ⟨by rw [abs_of_nonneg h0]; exact hle, by rw [abs_of_nonneg h0']; exact hle', ?_⟩
      by_cases hg : Good P Λ₀ m
      · -- good: the two logarithms differ by at most `Λ`
        rw [badW_of hg, zero_add]
        have hlb : 0 < Real.log (freePart P m) := hℓ.trans hlt'
        have hlm : 0 < Real.log m := hℓ.trans hlt
        have hmono : Real.log (freePart P m) ≤ Real.log m := Real.log_le_log hbar_pos hbar_le
        have hdiff : Real.log m - Real.log (freePart P m) ≤ Λ := by
          have h1 := hgood m hm hg
          have h2 : Real.log m ≤ Real.log ((freePart P m : ℝ) * Real.exp Λ) :=
            Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) h1
          rw [Real.log_mul hbar_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
          linarith
        have hrat : (Real.log m - Real.log (freePart P m)) / Real.log m ≤ ε₀ := by
          rw [hε]
          calc (Real.log m - Real.log (freePart P m)) / Real.log m
              ≤ Λ / Real.log m := div_le_div_of_nonneg_right hdiff hlm.le
            _ = Λ * (1 / Real.log m) := div_eq_mul_one_div _ _
            _ ≤ Λ * (1 / ℓ) :=
                mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hℓ hlt.le) hΛ
            _ = Λ / ℓ := (div_eq_mul_one_div _ _).symm
        have hrat0 : 0 ≤ (Real.log m - Real.log (freePart P m)) / Real.log m :=
          div_nonneg (sub_nonneg.mpr hmono) hlm.le
        have hident : proxyKappa x m = proxyKappa x (freePart P m) *
            (Real.log (freePart P m) / Real.log m) := by
          rw [heq, heq', div_mul_div_comm, one_mul, div_eq_div_iff (mul_pos hV hlm).ne'
            (mul_pos (mul_pos hV hlb) hlm).ne']
          ring
        have hsub : proxyKappa x (freePart P m) - proxyKappa x m =
            proxyKappa x (freePart P m) *
              ((Real.log m - Real.log (freePart P m)) / Real.log m) := by
          rw [sub_div, div_self hlm.ne', mul_sub, mul_one, ← hident]
        have hnn : 0 ≤ proxyKappa x (freePart P m) - proxyKappa x m := by
          rw [hsub]
          exact mul_nonneg h0' hrat0
        rw [abs_sub_comm, abs_of_nonneg hnn, hsub]
        calc proxyKappa x (freePart P m) *
              ((Real.log m - Real.log (freePart P m)) / Real.log m)
            ≤ κ₀ * ε₀ := mul_le_mul hle' hrat hrat0 hκpos.le
          _ ≤ κ₀ * (stripW x γ Λ m + ε₀) :=
              mul_le_mul_of_nonneg_left (by linarith) hκpos.le
      · -- not good: the trivial bound
        rw [badW_of_not hg]
        have h1 : |proxyKappa x m - proxyKappa x (freePart P m)| ≤ κ₀ :=
          abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        have h2 : κ₀ ≤ κ₀ * (1 + stripW x γ Λ m + ε₀) :=
          le_mul_of_one_le_right hκpos.le (by linarith)
        exact h1.trans h2
    · -- `m̄ ≤ x^γ < m`: `ã(m) = 0`, and `m` is not good or lies in the strip
      have hb : strippedCoeff x γ P m = 0 := by
        unfold strippedCoeff
        exact if_neg fun h => hbar h.2
      rw [hb, abs_zero, sub_zero, abs_of_nonneg h0]
      refine ⟨hle, hκpos.le, ?_⟩
      have h1 : 1 ≤ badW P Λ₀ m + stripW x γ Λ m + ε₀ := by
        by_cases hg : Good P Λ₀ m
        · have hs : (m : ℝ) ≤ x ^ γ * Real.exp Λ :=
            (hgood m hm hg).trans
              (mul_le_mul_of_nonneg_right (not_lt.mp hbar) (Real.exp_pos _).le)
          have hs1 : stripW x γ Λ m = 1 := by
            rw [hσ]
            exact if_pos hs
          linarith
        · have hbad := badW_of_not hg
          linarith
      exact hle.trans (le_mul_of_one_le_right hκpos.le h1)
  · have ha : proxyCoeff x γ m = 0 := by
      unfold proxyCoeff
      exact if_neg hρ
    have hb : strippedCoeff x γ P m = 0 := by
      unfold strippedCoeff
      exact if_neg fun h => hρ ⟨lt_of_lt_of_le h.2 hbar_le, h.1⟩
    have hθ : thetaW x γ P Λ₀ Λ ε₀ m = 0 := by
      unfold thetaW
      rw [rhoW_of_not hρ, zero_mul]
    rw [ha, hb, rhoW_of_not hρ, hθ, sub_zero, abs_zero, mul_zero]
    exact ⟨le_rfl, le_rfl, le_rfl⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

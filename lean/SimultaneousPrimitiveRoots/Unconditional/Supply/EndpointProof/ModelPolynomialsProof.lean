module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelInterchange

/-!
# The Dirichlet polynomial of the truncated divisor model at medium and high times

* `modelMedium : ModeratePhase → ModelPolynomialMedium` (cor:constant-medium), `[P-06:0878–0893]`:
  `|N_0(t)| ≪ L^{C_8} (|t|^{-1} + x^{-c'})` for `1 ≤ |t| ≤ T_mod = exp(L / (log L)²)`.
* `modelHigh : LogPhase → ModelPolynomialHigh` (cor:constant-high), `[P-06:0903–0912]`:
  `|N_0(t)| ≪ L^{C_8} exp(-L / (log L)^{C_3})` for `T_mod ≤ |t| ≤ 4x³`.

Both use the interchange of the divisor sum (`EndpointProof/ModelInterchange.lean`): "a divisor
`d'` leaves a progression modulo `k` at scale `R' = R_0 / d'`. Its normalization in `N(t)` is
`A_{d'} / d'` times normalization at `R'`. Since `d' ≤ exp(O(L^{.47}))`, one has `R' = x^{1-o(1)}`.
The divisor is a unit modulo `k`, so the original residue restriction becomes a single residue
restriction at this scale."

* `exp_support_le_rpow`: `exp(Csupp L^{.47}) ≤ x^{δ/2}` for large `x`, so `R' = R_0 / d' ≥ x^{δ/2}`
  (`rpow_half_le_div`).
* The range `R' ≤ m ≤ ρ R'` is cut into the dyads `[2^j R', 2^{j+1} R']`, `j ≤ ⌈ρ⌉`
  (`norm_normPoly_model_le`); on a subinterval of a dyad the classical input gives the progression
  sum `≤ (2^j R' / k) γ ≤ 2^j R' γ`, with `γ = C₀ (|t|^{-1} + x^{-c_δ})` from (eq:moderate-phase)
  at `δ/2`, and `γ = C₀ exp(-L / (log L)^{C_3})` from Lemma `lem:log-phase`.
* For Lemma `lem:log-phase`: the scales `2^j R'` lie between `x^{δ/2} ≥ exp(L / (log L)²)` and
  `2^{⌈ρ⌉} x² ≤ 2x⁵`, and `|t| ≥ exp(L / (log L)²) ≥ exp(L / (2 (log L)²))`.

Constants: `c' = c_{δ/2}`, `C_{19} = C_3`, `M = 2^{⌈ρ⌉+1} C₀`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- `exp(Csupp L^{.47}) ≤ x^{δ/2}` once `2 Csupp / δ ≤ L^{.53}`: the divisors of the model are
`x^{o(1)}` (`[P-06:0880–0881]`). -/
theorem exp_support_le_rpow {x δ Csupp : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (h : 2 * Csupp / δ ≤ Real.log x ^ (0.53 : ℝ)) :
    Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) ≤ x ^ (δ / 2) := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have h47 : 0 ≤ Real.log x ^ (0.47 : ℝ) := Real.rpow_nonneg hL.le _
  have hC : Csupp ≤ δ / 2 * Real.log x ^ (0.53 : ℝ) := by
    have h1 : 2 * Csupp ≤ Real.log x ^ (0.53 : ℝ) * δ := (div_le_iff₀ hδ).mp h
    have e : δ / 2 * Real.log x ^ (0.53 : ℝ) = Real.log x ^ (0.53 : ℝ) * δ / 2 := by ring
    rw [e]
    linarith
  have hprod : Real.log x ^ (0.53 : ℝ) * Real.log x ^ (0.47 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL]
    have e : (0.53 : ℝ) + 0.47 = 1 := by norm_num
    rw [e, Real.rpow_one]
  rw [Real.rpow_def_of_pos hx0]
  refine Real.exp_le_exp.mpr ?_
  calc Csupp * Real.log x ^ (0.47 : ℝ)
      ≤ δ / 2 * Real.log x ^ (0.53 : ℝ) * Real.log x ^ (0.47 : ℝ) :=
        mul_le_mul_of_nonneg_right hC h47
    _ = δ / 2 * (Real.log x ^ (0.53 : ℝ) * Real.log x ^ (0.47 : ℝ)) := by ring
    _ = Real.log x * (δ / 2) := by
        rw [hprod]
        ring

/-- The scale of a divisor progression: `R_0 / e ≥ x^{δ/2}` for `R_0 ≥ x^δ` and
`e ≤ x^{δ/2}`. -/
theorem rpow_half_le_div {x δ R₀ : ℝ} (hx : 0 < x) (hR₀ : x ^ δ ≤ R₀) {e : ℝ} (he0 : 0 < e)
    (he : e ≤ x ^ (δ / 2)) : x ^ (δ / 2) ≤ R₀ / e := by
  rw [le_div_iff₀ he0]
  have hsplit : x ^ δ = x ^ (δ / 2) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc x ^ (δ / 2) * e ≤ x ^ (δ / 2) * x ^ (δ / 2) :=
        mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hx.le _)
    _ = x ^ δ := hsplit.symm
    _ ≤ R₀ := hR₀

/-- **(cor:constant-medium)** (`[P-06:0878–0893]`), from (eq:moderate-phase). -/
theorem modelMedium : ModeratePhase → ModelPolynomialMedium := by
  intro hMP δ ρ C₆ Csupp C₈ hδ _ hC₆
  obtain ⟨C₀, cδ, x₁, hC₀, hcδ, hx₁, hmain⟩ := hMP (δ / 2) C₆ (half_pos hδ) hC₆
  have hE : ∀ᶠ x : ℝ in atTop, 2 * Csupp / δ ≤ Real.log x ^ (0.53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.53)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.mp hE
  refine ⟨cδ, 2 ^ (⌈ρ⌉₊ + 1) * C₀, max x₁ x₂, hcδ, ?_⟩
  intro x hx R₀ hR₀ k hk hkL a A hA hmass t ht1 ht2
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxx₂ : x₂ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hsupp := exp_support_le_rpow hx1 hδ (hx₂ x hxx₂)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hR₀
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hγ : 0 ≤ C₀ * (|t|⁻¹ + x ^ (-cδ)) :=
    mul_nonneg hC₀.le (add_nonneg (inv_nonneg.mpr (abs_nonneg t)) (Real.rpow_nonneg hx0.le _))
  have hA' : ∀ e : ℕ, A e ≠ 0 →
      e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊ ∧ e.Coprime k :=
    fun e he => ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (hA e he).1, Nat.le_floor (hA e he).2.1⟩,
      (hA e he).2.2⟩
  -- the progressions at dyadic scales, by (eq:moderate-phase)
  have hdy : ∀ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊, A e ≠ 0 →
      ∀ a' : ZMod k, ∀ j : ℕ, j ≤ ⌈ρ⌉₊ → ∀ l r : ℝ,
        2 ^ j * (R₀ / (e : ℝ)) ≤ l → l ≤ r → r ≤ 2 * (2 ^ j * (R₀ / (e : ℝ))) →
          ‖∑ n ∈ natIcc l r,
              (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖ ≤
            2 ^ j * (R₀ / (e : ℝ) * (C₀ * (|t|⁻¹ + x ^ (-cδ)))) := by
    intro e _ hAe a' j _ l r hl hlr hr
    have he' : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr (hA e hAe).1
    have hele : (e : ℝ) ≤ x ^ (δ / 2) := (hA e hAe).2.1.trans hsupp
    have hscale : x ^ (δ / 2) ≤ R₀ / (e : ℝ) := rpow_half_le_div hx0 hR₀ he' hele
    have hNpos : 0 < R₀ / (e : ℝ) := div_pos hR₀pos he'
    have hpow1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
    have hN' : x ^ (δ / 2) ≤ 2 ^ j * (R₀ / (e : ℝ)) :=
      hscale.trans (le_mul_of_one_le_left hNpos.le hpow1)
    have hN'pos : 0 < 2 ^ j * (R₀ / (e : ℝ)) := mul_pos (pow_pos two_pos j) hNpos
    have hl0 : 0 < l := hN'pos.trans_le hl
    have h3 := (hmain x hxx₁ (2 ^ j * (R₀ / (e : ℝ))) hN' k hk1 hkL a' t ht1 ht2 l r hl hlr
      hr).2.2
    rw [sum_natIcc_ite_eq_residuePhaseSum k a' t hl0]
    have hS0 : 0 ≤ ‖residuePhaseSum k a' t l r‖ := norm_nonneg _
    have h4 : ‖residuePhaseSum k a' t l r‖ / (2 ^ j * (R₀ / (e : ℝ))) ≤
        C₀ * (|t|⁻¹ + x ^ (-cδ)) :=
      calc ‖residuePhaseSum k a' t l r‖ / (2 ^ j * (R₀ / (e : ℝ)))
          ≤ (k : ℝ) * ‖residuePhaseSum k a' t l r‖ / (2 ^ j * (R₀ / (e : ℝ))) :=
            div_le_div_of_nonneg_right (le_mul_of_one_le_left hS0 hk1') hN'pos.le
        _ = (k : ℝ) / (2 ^ j * (R₀ / (e : ℝ))) * ‖residuePhaseSum k a' t l r‖ := by ring
        _ ≤ C₀ * (|t|⁻¹ + x ^ (-cδ)) := h3
    calc ‖residuePhaseSum k a' t l r‖
        ≤ C₀ * (|t|⁻¹ + x ^ (-cδ)) * (2 ^ j * (R₀ / (e : ℝ))) := (div_le_iff₀ hN'pos).mp h4
      _ = 2 ^ j * (R₀ / (e : ℝ) * (C₀ * (|t|⁻¹ + x ^ (-cδ)))) := by ring
  have hfinal := norm_normPoly_model_le (ρ := ρ) hR₀pos a A hA' t hγ hdy
  calc ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
        (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖
      ≤ 2 ^ (⌈ρ⌉₊ + 1) * (C₀ * (|t|⁻¹ + x ^ (-cδ))) *
          ∑ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊,
            ‖A e‖ / (e : ℝ) := hfinal
    _ ≤ 2 ^ (⌈ρ⌉₊ + 1) * (C₀ * (|t|⁻¹ + x ^ (-cδ))) * Real.log x ^ C₈ :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg (pow_nonneg zero_le_two _) hγ)
    _ = 2 ^ (⌈ρ⌉₊ + 1) * C₀ * Real.log x ^ C₈ * (|t|⁻¹ + x ^ (-cδ)) := by ring

/-- **(cor:constant-high)** (`[P-06:0903–0912]`), from Lemma `lem:log-phase`. -/
theorem modelHigh : LogPhase → ModelPolynomialHigh := by
  intro hLP δ ρ C₆ Csupp C₈ hδ _ hC₆
  obtain ⟨C₃, hC₃, hLP'⟩ := hLP
  obtain ⟨C₀, x₁, hC₀, hx₁, hmain⟩ := hLP' C₆ hC₆
  have hE1 : ∀ᶠ x : ℝ in atTop, 2 * Csupp / δ ≤ Real.log x ^ (0.53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.53)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have hE2 : ∀ᶠ x : ℝ in atTop, max 1 (2 / δ) ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.mp (hE1.and hE2)
  refine ⟨C₃, 2 ^ (⌈ρ⌉₊ + 1) * C₀, max (max x₁ x₂) (2 ^ ⌈ρ⌉₊), hC₃, ?_⟩
  intro x hx R₀ hR₀ hR₀2 k hk hkL a A hA hmass t ht1 ht2
  have hxx₁ : x₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxx₂ : x₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxJ : (2 : ℝ) ^ ⌈ρ⌉₊ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hcs, hLL⟩ := hx₂ x hxx₂
  have hsupp := exp_support_le_rpow hx1 hδ hcs
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hLL1 : 1 ≤ Real.log (Real.log x) := (le_max_left _ _).trans hLL
  have hLLδ : 2 / δ ≤ Real.log (Real.log x) := (le_max_right _ _).trans hLL
  have hsq : 2 / δ ≤ Real.log (Real.log x) ^ 2 := by
    have h1 : Real.log (Real.log x) ≤ Real.log (Real.log x) ^ 2 := by
      rw [pow_two]
      exact le_mul_of_one_le_left (by linarith) hLL1
    linarith
  have hsqpos : 0 < Real.log (Real.log x) ^ 2 := by
    have h2 : 0 < 2 / δ := div_pos two_pos hδ
    linarith
  -- `x^{δ/2} ≥ T_mod`
  have hTmod : Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ x ^ (δ / 2) := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_iff₀ hsqpos]
    have h1 : 1 ≤ δ / 2 * Real.log (Real.log x) ^ 2 := by
      have h2 : 2 ≤ Real.log (Real.log x) ^ 2 * δ := (div_le_iff₀ hδ).mp hsq
      have e : δ / 2 * Real.log (Real.log x) ^ 2 = Real.log (Real.log x) ^ 2 * δ / 2 := by ring
      rw [e]
      linarith
    calc Real.log x = Real.log x * 1 := (mul_one _).symm
      _ ≤ Real.log x * (δ / 2 * Real.log (Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hL.le
      _ = Real.log x * (δ / 2) * Real.log (Real.log x) ^ 2 := by ring
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hR₀
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hγ : 0 ≤ C₀ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃) :=
    mul_nonneg hC₀.le (Real.exp_pos _).le
  -- the frequency is in the range of `lem:log-phase`
  have ht1' : Real.exp (Real.log x / (2 * Real.log (Real.log x) ^ 2)) ≤ |t| := by
    refine le_trans (Real.exp_le_exp.mpr ?_) ht1
    exact div_le_div_of_nonneg_left hL.le hsqpos (by linarith)
  -- `x · x² ≤ x⁵`
  have hx5 : x * x ^ (2 : ℝ) ≤ x ^ (5 : ℝ) := by
    have h1 : x ≤ x ^ (3 : ℝ) :=
      calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have h2 : x ^ (5 : ℝ) = x ^ (3 : ℝ) * x ^ (2 : ℝ) := by
      rw [← Real.rpow_add hx0]
      congr 1
      norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)
  have hA' : ∀ e : ℕ, A e ≠ 0 →
      e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊ ∧ e.Coprime k :=
    fun e he => ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (hA e he).1, Nat.le_floor (hA e he).2.1⟩,
      (hA e he).2.2⟩
  -- the progressions at dyadic scales, by `lem:log-phase`
  have hdy : ∀ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊, A e ≠ 0 →
      ∀ a' : ZMod k, ∀ j : ℕ, j ≤ ⌈ρ⌉₊ → ∀ l r : ℝ,
        2 ^ j * (R₀ / (e : ℝ)) ≤ l → l ≤ r → r ≤ 2 * (2 ^ j * (R₀ / (e : ℝ))) →
          ‖∑ n ∈ natIcc l r,
              (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖ ≤
            2 ^ j * (R₀ / (e : ℝ) *
              (C₀ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃))) := by
    intro e _ hAe a' j hj l r hl _ hr
    have he0 : 0 < e := (hA e hAe).1
    have he' : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he0
    have he1 : (1 : ℝ) ≤ (e : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt he0)
    have hele : (e : ℝ) ≤ x ^ (δ / 2) := (hA e hAe).2.1.trans hsupp
    have hscale : x ^ (δ / 2) ≤ R₀ / (e : ℝ) := rpow_half_le_div hx0 hR₀ he' hele
    have hNpos : 0 < R₀ / (e : ℝ) := div_pos hR₀pos he'
    have hpow1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
    have hN'pos : 0 < 2 ^ j * (R₀ / (e : ℝ)) := mul_pos (pow_pos two_pos j) hNpos
    have hlow : Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ 2 ^ j * (R₀ / (e : ℝ)) :=
      (hTmod.trans hscale).trans (le_mul_of_one_le_left hNpos.le hpow1)
    have hupp : 2 ^ j * (R₀ / (e : ℝ)) ≤ 2 * x ^ (5 : ℝ) := by
      have h1 : R₀ / (e : ℝ) ≤ x ^ (2 : ℝ) := (div_le_self hR₀pos.le he1).trans hR₀2
      have h2 : (2 : ℝ) ^ j ≤ x :=
        (pow_le_pow_right₀ (one_le_two : (1 : ℝ) ≤ 2) hj).trans hxJ
      have h4 : 0 ≤ x ^ (5 : ℝ) := Real.rpow_nonneg hx0.le _
      calc 2 ^ j * (R₀ / (e : ℝ)) ≤ x * x ^ (2 : ℝ) := mul_le_mul h2 h1 hNpos.le hx0.le
        _ ≤ x ^ (5 : ℝ) := hx5
        _ ≤ 2 * x ^ (5 : ℝ) := by linarith
    have hl0 : 0 < l := hN'pos.trans_le hl
    have h3 := hmain x hxx₁ (2 ^ j * (R₀ / (e : ℝ))) hlow hupp k hk1 hkL a' t ht1' ht2 l r hl hr
    -- the sum of `lem:log-phase` is the progression sum
    have heq : ‖∑ n ∈ natIcc l r,
          (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖ ≤
        C₀ * (2 ^ j * (R₀ / (e : ℝ)) / (k : ℝ)) *
          Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃) := by
      refine le_of_eq_of_le
        (congrArg norm (sum_natIcc_ite_eq_of_mem k a' t hl0 _ fun n => ?_)) h3
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨-, -, -, h4, h5⟩
        exact ⟨h4, h5⟩
      · rintro ⟨⟨h4, h5⟩, h6⟩
        exact ⟨Nat.lt_succ_of_le (Nat.le_floor (h5.trans hr)), hl.trans h4, h5.trans hr,
          ⟨h4, h5⟩, h6⟩
    have hdiv : 2 ^ j * (R₀ / (e : ℝ)) / (k : ℝ) ≤ 2 ^ j * (R₀ / (e : ℝ)) :=
      div_le_self hN'pos.le hk1'
    calc ‖∑ n ∈ natIcc l r,
          (if (n : ZMod k) = a' then (n : ℂ) ^ ((t : ℂ) * Complex.I) else 0)‖
        ≤ C₀ * (2 ^ j * (R₀ / (e : ℝ)) / (k : ℝ)) *
            Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃) := heq
      _ ≤ C₀ * (2 ^ j * (R₀ / (e : ℝ))) *
            Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hC₀.le) (Real.exp_pos _).le
      _ = 2 ^ j * (R₀ / (e : ℝ) *
            (C₀ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃))) := by ring
  have hfinal := norm_normPoly_model_le (ρ := ρ) hR₀pos a A hA' t hγ hdy
  calc ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
        (fun n => if n ≡ a [MOD k] then divisorSum A n else 0) t‖
      ≤ 2 ^ (⌈ρ⌉₊ + 1) * (C₀ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃)) *
          ∑ e ∈ Finset.Icc 1 ⌊Real.exp (Csupp * Real.log x ^ (0.47 : ℝ))⌋₊,
            ‖A e‖ / (e : ℝ) := hfinal
    _ ≤ 2 ^ (⌈ρ⌉₊ + 1) * (C₀ * Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃)) *
          Real.log x ^ C₈ :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg (pow_nonneg zero_le_two _) hγ)
    _ = 2 ^ (⌈ρ⌉₊ + 1) * C₀ * Real.log x ^ C₈ *
          Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

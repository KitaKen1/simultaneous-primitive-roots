module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements

/-!
# The scales of (cor:SM)

`scaleFacts : ScaleFacts` (`[P-06:0385–0389, 0549, 0703, 0765–0769]`). For large `x` and every
scale `x exp(2 L^{.39} - c₁) ≤ Y ≤ x exp(c₂ L^{.46} log L)`:

* `L > 1` and `Y > 0`;
* `T₀ = x L^{C₆ + 1} ≤ Y`: `(C₆ + 1) log L ≤ L^{.2} L^{.19} = L^{.39}` and `c₁ ≤ L^{.39}`, so
  `L^{C₆ + 1} ≤ exp(2 L^{.39} - c₁)` ("`T_0 / Y = L / H = o(1)`");
* `4 N (1 + log N) ≤ 16 a₂ · Y · L` for `N = ⌊a₂ Y⌋`: `c₂ L^{.46} log L ≤ L^{.35} L^{.46} L^{.19}
  = L`, so `log Y ≤ 2L`, `log N ≤ log a₂ + 2L ≤ 3L` and `1 + log N ≤ 4L`.

The thresholds are obtained from `log L = o(L^{.19})` and `L^{r} → ∞`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- **The scales of (cor:SM).** -/
theorem scaleFacts : ScaleFacts := by
  intro D
  have hA : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hB : ∀ᶠ L : ℝ in atTop, D.C₆ + 1 ≤ L ^ (0.2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.2)).eventually_ge_atTop _
  have hC : ∀ᶠ L : ℝ in atTop, D.c₁ ≤ L ^ (0.39 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.39)).eventually_ge_atTop _
  have hD : ∀ᶠ L : ℝ in atTop, |D.c₂| ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  have hE : ∀ᶠ L : ℝ in atTop, Real.log D.a₂ ≤ L := eventually_ge_atTop _
  have hF : ∀ᶠ L : ℝ in atTop, 1 < L := eventually_gt_atTop 1
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (hA.and (hB.and (hC.and (hD.and (hE.and hF))))))
  refine ⟨16 * D.a₂, max x₀ 1, ?_⟩
  intro x hx Y hY1 hY2
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  obtain ⟨hlogA, hCB, hCC, hCD, hCE, hCF⟩ := hx₀ x hxx₀
  have hL1 : 1 < Real.log x := hCF
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1.le
  have hp19 : 0 ≤ Real.log x ^ (0.19 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlog19 : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ) := by
    have h : ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ := hlogA
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg hp19] at h
    exact h
  have hB' : D.C₆ + 1 ≤ Real.log x ^ (0.2 : ℝ) := hCB
  have hC' : D.c₁ ≤ Real.log x ^ (0.39 : ℝ) := hCC
  have hD' : |D.c₂| ≤ Real.log x ^ (0.35 : ℝ) := hCD
  have hE' : Real.log D.a₂ ≤ Real.log x := hCE
  -- `T₀ ≤ Y`
  have h39 : Real.log x ^ (0.2 : ℝ) * Real.log x ^ (0.19 : ℝ) = Real.log x ^ (0.39 : ℝ) := by
    rw [← Real.rpow_add hL0]
    congr 1
    norm_num
  have hmul : (D.C₆ + 1) * Real.log (Real.log x) ≤ Real.log x ^ (0.39 : ℝ) := by
    have h1 : (D.C₆ + 1) * Real.log (Real.log x) ≤
        Real.log x ^ (0.2 : ℝ) * Real.log x ^ (0.19 : ℝ) :=
      mul_le_mul hB' hlog19 hLL0 (Real.rpow_nonneg hL0.le _)
    rw [h39] at h1
    exact h1
  have hexp : Real.log x ^ (D.C₆ + 1) ≤ Real.exp (2 * Real.log x ^ (0.39 : ℝ) - D.c₁) := by
    rw [Real.rpow_def_of_pos hL0 (D.C₆ + 1)]
    refine Real.exp_le_exp.mpr ?_
    have hcomm : Real.log (Real.log x) * (D.C₆ + 1) = (D.C₆ + 1) * Real.log (Real.log x) :=
      mul_comm _ _
    rw [hcomm]
    linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (mul_pos hx0 (Real.exp_pos _)) hY1
  have hT : timeBound D x ≤ Y := by
    unfold timeBound
    exact (mul_le_mul_of_nonneg_left hexp hx0.le).trans hY1
  -- `log Y ≤ 2 L`
  have hEle : D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤ Real.log x := by
    have h1 : D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        |D.c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp46) hLL0
    have h2 : |D.c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        Real.log x ^ (0.35 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hD' hp46) hlog19 hLL0
        (mul_nonneg (Real.rpow_nonneg hL0.le _) hp46)
    have h3 : Real.log x ^ (0.35 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) =
        Real.log x := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      have e : (0.35 : ℝ) + 0.46 + 0.19 = 1 := by norm_num
      rw [e, Real.rpow_one]
    linarith
  have hlogY : Real.log Y ≤ 2 * Real.log x := by
    have h1 : Real.log Y ≤ Real.log
        (x * Real.exp (D.c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))) :=
      Real.log_le_log hYpos hY2
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  -- the length term
  have ha₂ : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
  have haY : 0 ≤ D.a₂ * Y := (mul_pos ha₂ hYpos).le
  have hNle : ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) ≤ D.a₂ * Y := Nat.floor_le haY
  have hlogN0 : 0 ≤ Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogN : Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) ≤ 3 * Real.log x := by
    by_cases hN0 : ⌊D.a₂ * Y⌋₊ = 0
    · rw [hN0, Nat.cast_zero, Real.log_zero]
      linarith
    · have hNpos : (0 : ℝ) < ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
      have h1 : Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) ≤ Real.log (D.a₂ * Y) :=
        Real.log_le_log hNpos hNle
      rw [Real.log_mul ha₂.ne' hYpos.ne'] at h1
      linarith
  have hfin : 4 * ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ)) ≤
      16 * D.a₂ * Y * Real.log x := by
    have h1 : 4 * ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) ≤ 4 * (D.a₂ * Y) := by linarith
    have h2 : 1 + Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) ≤ 4 * Real.log x := by linarith
    have h3 : 4 * ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊D.a₂ * Y⌋₊ : ℕ) : ℝ)) ≤
        4 * (D.a₂ * Y) * (4 * Real.log x) :=
      mul_le_mul h1 h2 (by linarith) (by linarith)
    have e : 4 * (D.a₂ * Y) * (4 * Real.log x) = 16 * D.a₂ * Y * Real.log x := by ring
    rw [e] at h3
    exact h3
  exact ⟨hL1, hYpos, hT, hfin⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

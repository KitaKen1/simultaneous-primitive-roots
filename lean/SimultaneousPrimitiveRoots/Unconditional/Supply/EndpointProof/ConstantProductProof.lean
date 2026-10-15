module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ConstantProductTools

/-!
# The constant products at high times

`constantProduct d : CoefficientBound d → ExceptionalCount → DivisorModel →
ModelPolynomialMedium → ModelPolynomialHigh → ConstantProductBound d`
(`[P-06:0763–0772, 0860–0925]`): for every saving `A` there is `B'` such that every product
`P_s N` has energy `≤ M L^{-A}` on the intervals of `{L^{B'} ≤ |t| ≤ 2T_0}`.

With `R_0 = a₁ Y / (2P)`, `ρ = 2a₂/a₁` (so the range of `n` is `[R_0, ρ R_0]`),
`A_s = (A + 1)/2 + |C_c|` (`C_c` the exponent of `CoefficientBound`), the model of
`lem:divisor-model` with precision `N = A + 1` and `B' = A + 2|C₈|`:

* `N = N_0 + N_E` (`normPoly_add`), `N_0` the polynomial of the divisor model `H_0` restricted to
  the class `a mod k` and `N_E` that of the error `H_marks - H_0` ("Keep its residue-class
  restriction separately", `[P-06:0862]`).
* Ordinary times, `|P_s(t)| ≤ L^{-A_s}`: the mean-value theorem with `2T_0 ≤ R_0`
  ((cor:length-dominates-time)) and `|c(n)| ≤ L^{C_c}` gives
  `∫ |N|² ≤ ρ(1 + 12ρ) L^{1 + 2C_c}`.
* Exceptional times: `|P_s| ≤ 2` and `|N|² ≤ 2|N_0|² + 2|N_E|²`, so
  `|P_s N|² ≤ 8|N_E|² + 8|N_0|²`. The error is integrated over the whole interval: the dyadic
  mean squares of `H_marks - H_0` and the mean-value theorem give
  `∫ |N_E|² ≤ (1 + 12ρ) 2^{⌈ρ⌉ + 1} |M_E| L^{-A}`. For the model, (cor:constant-medium) gives
  `|N_0(t)|² ≤ 2 M_m² L^{2C₈} (t^{-2} + x^{-2c'})` for `|t| ≤ T_mod` and (cor:constant-high)
  gives `|N_0(t)|² ≤ M_h² L^{2C₈} exp(-2L/(log L)^{C_19})` for `T_mod ≤ |t| ≤ 2T_0 ≤ 4x³`; the
  divisors of the model are units modulo `k` because the marked primes exceed `L^{C_6} ≥ k`.
  The term `t^{-2}` is integrated ("square integration of `1/|t|`", `[P-06:0898–0900]`):
  `∫ t^{-2} ≤ L^{-B'}`; the two small errors are paid by the number `≤ exp(L^{.9})` of
  exceptional cells ((cor:exceptional-count)) through `integral_le_of_ordinary_exceptional`.

The constant is `M = ρ(1 + 12ρ) + 8(1 + 12ρ) 2^{⌈ρ⌉ + 1} |M_E| + 48 M_m² + 16 M_h²`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- **The constant products** (`[P-06:0763–0772, 0860–0925]`), for any number `d + 1` of slots:
from the coefficient bound, (cor:exceptional-count), the truncated divisor model and the two
bounds for the model polynomial. -/
theorem constantProduct (d : ℕ) :
    CoefficientBound d → ExceptionalCount → DivisorModel → ModelPolynomialMedium →
      ModelPolynomialHigh → ConstantProductBound d := by
  intro hCB hEC hDM hMed hHigh D A hA
  obtain ⟨Cc, xc, hCBx⟩ := hCB D
  obtain ⟨Csupp, C₈, hmodel⟩ :=
    hDM D.q D.q₀ D.q_pos D.q_lt_one D.q₀_pos D.q₀_lt_one D.K D.𝔞 D.P D.m'
  have ha₂ : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
  obtain ⟨ρc, hρc⟩ : ∃ ρc : ℝ, ρc = 2 * D.a₂ / D.a₁ := ⟨_, rfl⟩
  have hρc1 : 1 ≤ ρc := by
    have h := D.a₁_le_a₂
    rw [hρc, le_div_iff₀ D.a₁_pos]
    linarith
  obtain ⟨c', Mm, xm, hc', hMedx⟩ := hMed 1 ρc D.C₆ Csupp C₈ one_pos hρc1 D.C₆_pos
  obtain ⟨C₁₉, Mh, xh, hC₁₉, hHighx⟩ := hHigh 1 ρc D.C₆ Csupp C₈ one_pos hρc1 D.C₆_pos
  have hCc0 : 0 ≤ |Cc| := abs_nonneg Cc
  obtain ⟨As, hAsdef⟩ : ∃ As : ℝ, As = (A + 1) / 2 + |Cc| := ⟨_, rfl⟩
  have hAs : 0 < As := by
    rw [hAsdef]
    linarith
  obtain ⟨xE, hECx⟩ := hEC As hAs
  obtain ⟨ME, xM, hMx⟩ := hmodel (A + 1) (by linarith)
  have hC80 : 0 ≤ |C₈| := abs_nonneg C₈
  obtain ⟨Bp, hBpdef⟩ : ∃ Bp : ℝ, Bp = A + 2 * |C₈| := ⟨_, rfl⟩
  have hBp : 0 < Bp := by
    rw [hBpdef]
    linarith
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp
    (((((eventually_productScale D.a₁ D.a₂ D.c₁ D.c₂ D.C₆ D.a₁_pos).and
      (eventually_exp_mul_rpow_neg_le_one hc')).and
      (eventually_rpow_neg_mul_exp_mul_rpow_le_one hc' 0 (2 * C₈ + A))).and
      (eventually_exp_neg_div_log_pow hC₁₉ (2 * C₈ + A))).and
      (eventually_rpow_lt_exp_tenth D.C₆))
  refine ⟨Bp, hBp, ρc * (1 + 12 * ρc) + 8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) +
      48 * Mm ^ 2 + 16 * Mh ^ 2, max (max (max xc xm) (max xh xE)) (max xM x₃), ?_⟩
  intro x hx c hc i₀ P hP1 hP2 b hb k hk hkL a τ₁ τ₂ hτ hrange
  have hxc : xc ≤ x :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hx
  have hxm : xm ≤ x :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hx
  have hxh : xh ≤ x :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hxE : xE ≤ x :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hx
  have hxM : xM ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨⟨⟨⟨⟨hx1, hL1, hscale⟩, hEη₁⟩, hη₁L'⟩, hEη₂, hη₂L⟩, -, hC6⟩ := hx₃ x hxx₃
  obtain ⟨hYpos, hPhalf, h4aY, hTQ, hTx2⟩ := hscale c.Y hc.scale_ge hc.scale_le P hP1 hP2
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hP0 : 0 < P := by linarith
  have h2P : 0 < 2 * P := by linarith
  have h4P : 0 < 4 * P := by linarith
  have h2P1 : 1 ≤ 2 * P := by linarith
  have haY0 : 0 ≤ D.a₁ * c.Y := mul_nonneg D.a₁_pos.le hYpos.le
  -- the scale `R₀ = a₁ Y / (2P)` of `N`
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = D.a₁ * c.Y / (2 * P) := ⟨_, rfl⟩
  have hR₀Q : R₀ = 2 * (D.a₁ * c.Y / (4 * P)) := by
    rw [hR₀def, mul_div_assoc', div_eq_div_iff h2P.ne' h4P.ne']
    ring
  have hLC1 : 1 ≤ Real.log x ^ (D.C₆ + 1) :=
    Real.one_le_rpow hL1 (by linarith [D.C₆_pos])
  have hR₀x : x ≤ R₀ := by
    have h1 : x * 1 ≤ x * Real.log x ^ (D.C₆ + 1) := mul_le_mul_of_nonneg_left hLC1 hx0.le
    rw [hR₀Q]
    linarith
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le hx0 hR₀x
  have hR₀1 : 1 ≤ R₀ := by linarith
  have hR₀lo : x ^ (1 : ℝ) ≤ R₀ := by
    rw [Real.rpow_one]
    exact hR₀x
  have h4a : D.a₁ * c.Y ≤ 4 * D.a₂ * c.Y := by
    have h := D.a₁_le_a₂
    exact mul_le_mul_of_nonneg_right (by linarith) hYpos.le
  have hR₀up : R₀ ≤ x ^ (2 : ℝ) := by
    rw [hR₀def]
    exact ((div_le_self haY0 h2P1).trans h4a).trans h4aY
  have hupper : D.a₂ * c.Y / P = ρc * R₀ := by
    rw [hρc, hR₀def, div_mul_div_comm,
      div_eq_div_iff hP0.ne' (mul_pos D.a₁_pos h2P).ne']
    ring
  have hρR₀up : ρc * R₀ ≤ x ^ (2 : ℝ) := by
    have h1 : D.a₂ * c.Y / P ≤ 4 * D.a₂ * c.Y := by
      rw [div_le_iff₀ hP0]
      have h2 : 4 * D.a₂ * c.Y * (1 / 2) ≤ 4 * D.a₂ * c.Y * P :=
        mul_le_mul_of_nonneg_left hPhalf
          (mul_nonneg (mul_nonneg (by norm_num) ha₂.le) hYpos.le)
      have h3 : 0 ≤ D.a₂ * c.Y := mul_nonneg ha₂.le hYpos.le
      linarith
    rw [← hupper]
    exact h1.trans h4aY
  -- the times of `[τ₁, τ₂]`
  have hT0 : 2 * timeBound D x = 2 * (x * Real.log x ^ (D.C₆ + 1)) := rfl
  have hlo1 : 1 ≤ Real.log x ^ Bp := Real.one_le_rpow hL1 hBp.le
  have hlo0 : 0 ≤ Real.log x ^ Bp := by linarith
  have hlopos : 0 < Real.log x ^ Bp := by linarith
  have htime : ∀ t ∈ Set.Icc τ₁ τ₂, Real.log x ^ Bp ≤ |t| ∧ |t| ≤ x ^ (2 : ℝ) := fun t ht =>
    ⟨(abs_mem_of_highRange hlo0 hrange ht).1,
      ((abs_mem_of_highRange hlo0 hrange ht).2.trans (le_of_eq hT0)).trans hTx2⟩
  have hlen : τ₂ - τ₁ ≤ R₀ := by
    have h1 := sub_le_of_highRange hlo0 hrange
    rw [hT0] at h1
    have h2 : 0 ≤ D.a₁ * c.Y / (4 * P) := div_nonneg haY0 h4P.le
    rw [hR₀Q]
    linarith
  have hx23 : x ^ (2 : ℝ) ≤ 4 * x ^ (3 : ℝ) := by
    have h1 : x ^ (2 : ℝ) ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have h2 : 0 ≤ x ^ (3 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith
  have hne0 : ∀ t ∈ Set.Icc τ₁ τ₂, t ≠ 0 := by
    intro t ht h0
    have h1 := (htime t ht).1
    rw [h0, abs_zero] at h1
    linarith
  -- the polynomials `P_s` and `N`
  obtain ⟨Ps, hPs⟩ : ∃ Ps : ℝ → ℂ,
      Ps = normPoly P (c.smallGroup i₀ ∩ natIcc P (2 * P)) b := ⟨_, rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf : ℕ → ℂ,
      cf = fun n => if n ≡ a [MOD k] then c.constCoeff D x i₀ n else 0 := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℝ → ℂ, Nn = normPoly R₀ (natIcc R₀ (ρc * R₀)) cf := ⟨_, rfl⟩
  -- the divisor model `H_0` and the error
  obtain ⟨Am, hAmodel, hAerr⟩ := hMx x hxM c.𝔊 hc.groups c.t (fun g => (hc.marks g).2) c.test
    hc.test_le {Sum.inl i₀}
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ → ℂ,
      c₀ = fun n => if n ≡ a [MOD k] then divisorSum Am n else 0 := ⟨_, rfl⟩
  obtain ⟨cE, hcE⟩ : ∃ cE : ℕ → ℂ,
      cE = fun n => if n ≡ a [MOD k] then c.constCoeff D x i₀ n - divisorSum Am n else 0 :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ → ℂ, N₀ = normPoly R₀ (natIcc R₀ (ρc * R₀)) c₀ := ⟨_, rfl⟩
  obtain ⟨NE, hNE⟩ : ∃ NE : ℝ → ℂ, NE = normPoly R₀ (natIcc R₀ (ρc * R₀)) cE := ⟨_, rfl⟩
  have hcfn : ∀ n, cf n = if n ≡ a [MOD k] then c.constCoeff D x i₀ n else 0 := fun n => by
    rw [hcf]
  have hc₀n : ∀ n, c₀ n = if n ≡ a [MOD k] then divisorSum Am n else 0 := fun n => by
    rw [hc₀]
  have hcEn : ∀ n, cE n =
      if n ≡ a [MOD k] then c.constCoeff D x i₀ n - divisorSum Am n else 0 := fun n => by
    rw [hcE]
  have hpt : ∀ n, cf n = c₀ n + cE n := by
    intro n
    rw [hcfn n, hc₀n n, hcEn n]
    split_ifs with hn
    · ring
    · rw [add_zero]
  have hsplit : ∀ t : ℝ, Nn t = N₀ t + NE t := by
    intro t
    have h1 : cf = fun n => c₀ n + cE n := funext hpt
    rw [hNn, hN₀, hNE, h1]
    exact normPoly_add R₀ _ c₀ cE t
  have hGpos : ∀ p ∈ c.smallGroup i₀ ∩ natIcc P (2 * P), 0 < p := fun p hp =>
    Nat.pos_of_ne_zero (ne_zero_of_mem_natIcc hP0 (Finset.mem_inter.mp hp).2)
  have hUpos : ∀ u ∈ natIcc R₀ (ρc * R₀), 0 < u := fun u hu =>
    Nat.pos_of_ne_zero (ne_zero_of_mem_natIcc hR₀pos hu)
  have hPsc : Continuous Ps := by
    rw [hPs]
    exact continuous_normPoly P (fun n hn => (hGpos n hn).ne') b
  have hNnc : Continuous Nn := by
    rw [hNn]
    exact continuous_normPoly R₀ (fun n hn => (hUpos n hn).ne') cf
  have hNEc : Continuous NE := by
    rw [hNE]
    exact continuous_normPoly R₀ (fun n hn => (hUpos n hn).ne') cE
  have hPs2 : ∀ t : ℝ, ‖Ps t‖ ≤ 2 := by
    intro t
    have h1 : ‖normPoly P (c.smallGroup i₀ ∩ natIcc P (2 * P)) b t‖ ≤
        P⁻¹ * (((c.smallGroup i₀ ∩ natIcc P (2 * P)).card : ℝ) * 1) :=
      norm_normPoly_le hP0 hGpos (fun n _ => hb n) t
    have h2 : ((c.smallGroup i₀ ∩ natIcc P (2 * P)).card : ℝ) ≤ 2 * P :=
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans
        (card_natIcc_le hP0 (by linarith))
    have h3 : P⁻¹ * (((c.smallGroup i₀ ∩ natIcc P (2 * P)).card : ℝ) * 1) ≤
        P⁻¹ * (2 * P) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hP0.le)
    have e : P⁻¹ * (2 * P) = 2 := by
      rw [mul_comm 2 P, ← mul_assoc, inv_mul_cancel₀ hP0.ne', one_mul]
    rw [hPs]
    linarith
  -- the mean square of `N`
  have hLCc0 : 0 ≤ Real.log x ^ Cc := Real.rpow_nonneg hL0.le _
  have hUmem : ∀ n ∈ natIcc R₀ (ρc * R₀), 1 ≤ n ∧ (n : ℝ) ≤ x ^ (2 : ℝ) := fun n hn =>
    ⟨Nat.succ_le_of_lt (hUpos n hn), ((mem_natIcc_of_pos hR₀pos).mp hn).2.trans hρR₀up⟩
  have hcfle : ∀ n ∈ natIcc R₀ (ρc * R₀), ‖cf n‖ ≤ Real.log x ^ Cc := by
    intro n hn
    rw [hcfn n]
    split_ifs with h
    · exact (hCBx x hxc c hc i₀ n (hUmem n hn).1 (hUmem n hn).2).1
    · rw [norm_zero]
      exact hLCc0
  have hcfsum : ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cf n‖ ^ 2 ≤
      R₀ * (ρc * (Real.log x ^ Cc) ^ 2) :=
    calc ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cf n‖ ^ 2
        ≤ ∑ _n ∈ natIcc R₀ (ρc * R₀), (Real.log x ^ Cc) ^ 2 :=
          Finset.sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) (hcfle n hn) 2
      _ = ((natIcc R₀ (ρc * R₀)).card : ℝ) * (Real.log x ^ Cc) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ρc * R₀ * (Real.log x ^ Cc) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (card_natIcc_le hR₀pos (mul_nonneg (by linarith) hR₀pos.le)) (sq_nonneg _)
      _ = R₀ * (ρc * (Real.log x ^ Cc) ^ 2) := by ring
  have hmeanN : ∫ t in τ₁..τ₂, ‖Nn t‖ ^ 2 ≤
      (1 + 12 * ρc) * Real.log x * (ρc * (Real.log x ^ Cc) ^ 2) := by
    rw [hNn]
    exact integral_normSq_normPoly_natIcc_le hR₀pos hρc1 hx1 hL1 hρR₀up cf hτ hlen hcfsum
  -- the mean square of the error `N_E`
  have hEsum : ∑ n ∈ natIcc R₀ (ρc * R₀), ‖c.constCoeff D x i₀ n - divisorSum Am n‖ ^ 2 ≤
      R₀ * (2 ^ (⌈ρc⌉₊ + 1) * (|ME| * Real.log x ^ (-(A + 1)))) :=
    sum_normSq_natIcc_le_of_model (fun n => c.constCoeff D x i₀ n - divisorSum Am n) hR₀1
      (Real.rpow_nonneg hL0.le _) hAerr
  have hcEsum : ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cE n‖ ^ 2 ≤
      R₀ * (2 ^ (⌈ρc⌉₊ + 1) * (|ME| * Real.log x ^ (-(A + 1)))) := by
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) hEsum
    show ‖cE n‖ ^ 2 ≤ ‖c.constCoeff D x i₀ n - divisorSum Am n‖ ^ 2
    rw [hcEn n]
    split_ifs with h
    · exact le_rfl
    · rw [norm_zero, zero_pow two_ne_zero]
      exact sq_nonneg _
  have hmeanE : ∫ t in τ₁..τ₂, ‖NE t‖ ^ 2 ≤
      (1 + 12 * ρc) * Real.log x *
        (2 ^ (⌈ρc⌉₊ + 1) * (|ME| * Real.log x ^ (-(A + 1)))) := by
    rw [hNE]
    exact integral_normSq_normPoly_natIcc_le hR₀pos hρc1 hx1 hL1 hρR₀up cE hτ hlen hcEsum
  -- the model polynomial `N_0` at the times of `[τ₁, τ₂]`
  have hAsupp : ∀ e : ℕ, Am e ≠ 0 →
      0 < e ∧ (e : ℝ) ≤ Real.exp (Csupp * Real.log x ^ (0.47 : ℝ)) ∧ e.Coprime k := by
    intro e he
    refine ⟨(hAmodel.size e he).1, (hAmodel.size e he).2, ?_⟩
    refine Nat.coprime_of_dvd fun p hp hpe hpk => ?_
    have hple : (p : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr (Nat.le_of_dvd hk hpk)
    have hgt : Real.log x ^ D.C₆ < (p : ℝ) :=
      rpow_lt_of_mem_markPrimes D.𝔞 hc.groups hL1 hC6 (hAmodel.primes_mem e he p hp hpe)
    linarith
  obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = Real.log x ^ C₈ := ⟨_, rfl⟩
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = x ^ (-c') := ⟨_, rfl⟩
  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : ℝ,
      η₂ = Real.exp (-Real.log x / Real.log (Real.log x) ^ C₁₉) := ⟨_, rfl⟩
  obtain ⟨E₉, hE₉⟩ : ∃ E₉ : ℝ, E₉ = Real.exp (Real.log x ^ (0.9 : ℝ)) := ⟨_, rfl⟩
  have hη₁0 : 0 ≤ η₁ := by
    rw [hη₁]
    exact Real.rpow_nonneg hx0.le _
  have hη₂0 : 0 ≤ η₂ := by
    rw [hη₂]
    exact (Real.exp_pos _).le
  have hmed : ∀ t : ℝ, 1 ≤ |t| →
      |t| ≤ Real.exp (Real.log x / Real.log (Real.log x) ^ 2) →
      ‖N₀ t‖ ≤ Mm * Lc * (|t|⁻¹ + η₁) := by
    intro t ht1 ht2
    rw [hN₀, hc₀, hLc, hη₁]
    exact hMedx x hxm R₀ hR₀lo k hk hkL a Am hAsupp hAmodel.mass t ht1 ht2
  have hhigh : ∀ t : ℝ, Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ |t| →
      |t| ≤ 4 * x ^ (3 : ℝ) → ‖N₀ t‖ ≤ Mh * Lc * η₂ := by
    intro t ht1 ht2
    rw [hN₀, hc₀, hLc, hη₂]
    exact hHighx x hxh R₀ hR₀lo hR₀up k hk hkL a Am hAsupp hAmodel.mass t ht1 ht2
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : ℝ, G₀ = 2 * Mm ^ 2 * Lc ^ 2 := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = G₀ * η₁ ^ 2 + Mh ^ 2 * Lc ^ 2 * η₂ ^ 2 := ⟨_, rfl⟩
  have hG₀0 : 0 ≤ G₀ := by
    rw [hG₀]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hh0 : 0 ≤ Mh ^ 2 * Lc ^ 2 * η₂ ^ 2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hρ₁0 : 0 ≤ ρ₁ := by
    rw [hρ₁]
    exact add_nonneg (mul_nonneg hG₀0 (sq_nonneg _)) hh0
  have hN₀sq : ∀ t ∈ Set.Icc τ₁ τ₂, ‖N₀ t‖ ^ 2 ≤ G₀ * (t ^ 2)⁻¹ + ρ₁ := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := htime t ht
    have hg1 : 0 ≤ G₀ * (t ^ 2)⁻¹ := mul_nonneg hG₀0 (inv_nonneg.mpr (sq_nonneg t))
    have hg2 : 0 ≤ G₀ * η₁ ^ 2 := mul_nonneg hG₀0 (sq_nonneg _)
    rw [hρ₁]
    by_cases hT : |t| ≤ Real.exp (Real.log x / Real.log (Real.log x) ^ 2)
    · have h1 := hmed t (hlo1.trans ht1) hT
      have h2 : ‖N₀ t‖ ^ 2 ≤ (Mm * Lc * (|t|⁻¹ + η₁)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 := sq_mul_add_le_two_mul (Mm * Lc) (|t|⁻¹) η₁
      have e1 : |t|⁻¹ ^ 2 = (t ^ 2)⁻¹ := by rw [inv_pow, sq_abs]
      have e2 : 2 * (Mm * Lc) ^ 2 * |t|⁻¹ ^ 2 + 2 * (Mm * Lc) ^ 2 * η₁ ^ 2 =
          G₀ * (t ^ 2)⁻¹ + G₀ * η₁ ^ 2 := by
        rw [e1, hG₀]
        ring
      rw [e2] at h3
      exact (h2.trans h3).trans (by linarith)
    · have hT' : Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ |t| := (not_le.mp hT).le
      have h1 := hhigh t hT' (ht2.trans hx23)
      have h2 : ‖N₀ t‖ ^ 2 ≤ (Mh * Lc * η₂) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e : (Mh * Lc * η₂) ^ 2 = Mh ^ 2 * Lc ^ 2 * η₂ ^ 2 := by ring
      rw [e] at h2
      linarith
  -- the threshold and the three functions
  obtain ⟨Λs, hΛs⟩ : ∃ Λs : ℝ, Λs = Real.log x ^ (-As) := ⟨_, rfl⟩
  have hinvc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc τ₁ τ₂) :=
    continuousOn_inv_sq hne0
  have hFc : Continuous fun t : ℝ => ‖Ps t * Nn t‖ ^ 2 := (hPsc.mul hNnc).norm.pow 2
  have hN2c : Continuous fun t : ℝ => ‖Nn t‖ ^ 2 := hNnc.norm.pow 2
  have hE2c : Continuous fun t : ℝ => ‖NE t‖ ^ 2 := hNEc.norm.pow 2
  have hgc : ContinuousOn
      (fun t : ℝ => Λs ^ 2 * ‖Nn t‖ ^ 2 + 8 * ‖NE t‖ ^ 2 + 8 * G₀ * (t ^ 2)⁻¹)
      (Set.Icc τ₁ τ₂) :=
    ((continuous_const.mul hN2c).add (continuous_const.mul hE2c)).continuousOn.add
      (continuousOn_const.mul hinvc)
  have hρcont : ContinuousOn (fun _ : ℝ => 8 * ρ₁) (Set.Icc τ₁ τ₂) := continuousOn_const
  have hord : ∀ t ∈ Set.Icc τ₁ τ₂, ¬ Λs < ‖Ps t‖ →
      ‖Ps t * Nn t‖ ^ 2 ≤ Λs ^ 2 * ‖Nn t‖ ^ 2 + 8 * ‖NE t‖ ^ 2 + 8 * G₀ * (t ^ 2)⁻¹ := by
    intro t _ hnot
    have h1 : ‖Ps t‖ ≤ Λs := not_lt.mp hnot
    have h2 : ‖Ps t * Nn t‖ ^ 2 ≤ Λs ^ 2 * ‖Nn t‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
    have h3 : 0 ≤ 8 * ‖NE t‖ ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    have h4 : 0 ≤ 8 * G₀ * (t ^ 2)⁻¹ :=
      mul_nonneg (mul_nonneg (by norm_num) hG₀0) (inv_nonneg.mpr (sq_nonneg t))
    linarith
  have hexc : ∀ t ∈ Set.Icc τ₁ τ₂, Λs < ‖Ps t‖ →
      ‖Ps t * Nn t‖ ^ 2 ≤
        Λs ^ 2 * ‖Nn t‖ ^ 2 + 8 * ‖NE t‖ ^ 2 + 8 * G₀ * (t ^ 2)⁻¹ + 8 * ρ₁ := by
    intro t ht _
    have h1 : ‖Ps t * Nn t‖ ^ 2 ≤ 4 * ‖Nn t‖ ^ 2 := by
      have h2 : ‖Ps t * Nn t‖ ≤ 2 * ‖Nn t‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hPs2 t) (norm_nonneg _)
      have h3 : ‖Ps t * Nn t‖ ^ 2 ≤ (2 * ‖Nn t‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      have e : (2 * ‖Nn t‖) ^ 2 = 4 * ‖Nn t‖ ^ 2 := by ring
      rw [e] at h3
      exact h3
    have h4 : ‖Nn t‖ ^ 2 ≤ 2 * ‖N₀ t‖ ^ 2 + 2 * ‖NE t‖ ^ 2 := by
      rw [hsplit t]
      exact normSq_add_le_two_mul (N₀ t) (NE t)
    have h5 := hN₀sq t ht
    have h6 : 0 ≤ Λs ^ 2 * ‖Nn t‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  have hGprime : ∀ p ∈ c.smallGroup i₀, p.Prime := fun p hp =>
    hc.groups.prime (Sum.inl i₀) p hp
  have hcount : ∀ 𝒮 : Finset ℝ, (∀ s ∈ 𝒮, s ∈ Set.Icc τ₁ τ₂ ∧ Λs < ‖Ps s‖) →
      (∀ s ∈ 𝒮, ∀ s' ∈ 𝒮, s ≠ s' → 1 ≤ |s - s'|) → (𝒮.card : ℝ) ≤ E₉ := by
    intro 𝒮 h𝒮 hsep
    rw [hE₉]
    refine hECx x hxE (c.smallGroup i₀) hGprime P hP1 hP2 b hb 𝒮
      (fun s hs => (htime s (h𝒮 s hs).1).2) hsep ?_
    intro s hs
    have h1 := (h𝒮 s hs).2
    rw [hΛs, hPs] at h1
    exact h1
  have hsparse : ∀ 𝒯 : Finset ℝ, (∀ t ∈ 𝒯, t ∈ Set.Icc τ₁ τ₂) →
      (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) → (𝒯.card : ℝ) ≤ E₉ →
      ∑ _t ∈ 𝒯, 8 * ρ₁ ≤ E₉ * (8 * ρ₁) := by
    intro 𝒯 _ _ hcard
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (mul_nonneg (by norm_num) hρ₁0)
  have hcell : ∫ t in τ₁..τ₂, ‖Ps t * Nn t‖ ^ 2 ≤
      (∫ t in τ₁..τ₂, (Λs ^ 2 * ‖Nn t‖ ^ 2 + 8 * ‖NE t‖ ^ 2 + 8 * G₀ * (t ^ 2)⁻¹)) +
        2 * (E₉ * (8 * ρ₁)) :=
    integral_le_of_ordinary_exceptional hτ hFc.continuousOn hgc hρcont
      (fun _ _ => mul_nonneg (by norm_num) hρ₁0)
      (fun t : ℝ => Λs < ‖Ps t‖) hord hexc hcount hsparse
  have hint_g : ∫ t in τ₁..τ₂, (Λs ^ 2 * ‖Nn t‖ ^ 2 + 8 * ‖NE t‖ ^ 2 + 8 * G₀ * (t ^ 2)⁻¹) =
      Λs ^ 2 * (∫ t in τ₁..τ₂, ‖Nn t‖ ^ 2) + 8 * (∫ t in τ₁..τ₂, ‖NE t‖ ^ 2) +
        8 * G₀ * ∫ t in τ₁..τ₂, (t ^ 2)⁻¹ :=
    integral_three_terms (Λs ^ 2) 8 (8 * G₀) hτ hN2c.continuousOn hE2c.continuousOn hinvc
  -- the four contributions
  have hκ0 : 0 ≤ ρc * (1 + 12 * ρc) := mul_nonneg (by linarith) (by linarith)
  have hb1 : Λs ^ 2 * (∫ t in τ₁..τ₂, ‖Nn t‖ ^ 2) ≤
      ρc * (1 + 12 * ρc) * Real.log x ^ (-A) := by
    have h2 : (Real.log x ^ (-As)) ^ 2 * (Real.log x ^ 1 * (Real.log x ^ Cc) ^ 2) ≤
        Real.log x ^ (-A) := by
      refine rpow_neg_sq_mul_le hL1 1 ?_
      have h3 := le_abs_self Cc
      rw [hAsdef]
      push_cast
      linarith
    rw [hΛs]
    calc (Real.log x ^ (-As)) ^ 2 * ∫ t in τ₁..τ₂, ‖Nn t‖ ^ 2
        ≤ (Real.log x ^ (-As)) ^ 2 *
            ((1 + 12 * ρc) * Real.log x * (ρc * (Real.log x ^ Cc) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmeanN (sq_nonneg _)
      _ = ρc * (1 + 12 * ρc) *
            ((Real.log x ^ (-As)) ^ 2 * (Real.log x ^ 1 * (Real.log x ^ Cc) ^ 2)) := by ring
      _ ≤ ρc * (1 + 12 * ρc) * Real.log x ^ (-A) := mul_le_mul_of_nonneg_left h2 hκ0
  have hLA : Real.log x * Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) := by
    have e : -A = 1 + -(A + 1) := by ring
    rw [e, Real.rpow_add hL0 1 (-(A + 1)), Real.rpow_one]
  have hb2 : 8 * (∫ t in τ₁..τ₂, ‖NE t‖ ^ 2) ≤
      8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) * Real.log x ^ (-A) :=
    calc 8 * (∫ t in τ₁..τ₂, ‖NE t‖ ^ 2)
        ≤ 8 * ((1 + 12 * ρc) * Real.log x *
            (2 ^ (⌈ρc⌉₊ + 1) * (|ME| * Real.log x ^ (-(A + 1))))) :=
          mul_le_mul_of_nonneg_left hmeanE (by norm_num)
      _ = 8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) *
            (Real.log x * Real.log x ^ (-(A + 1))) := by ring
      _ = 8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) * Real.log x ^ (-A) := by rw [hLA]
  have hb3 : 8 * G₀ * (∫ t in τ₁..τ₂, (t ^ 2)⁻¹) ≤ 16 * Mm ^ 2 * Real.log x ^ (-A) := by
    have h1 : ∫ t in τ₁..τ₂, (t ^ 2)⁻¹ ≤ (Real.log x ^ Bp)⁻¹ :=
      integral_inv_sq_le hlopos hτ hrange
    have h2 : (Real.log x ^ Bp)⁻¹ = Real.log x ^ (-Bp) := (Real.rpow_neg hL0.le Bp).symm
    have h3 : (Real.log x ^ C₈) ^ 2 * Real.log x ^ (-Bp) ≤ Real.log x ^ (-A) := by
      refine sq_rpow_mul_rpow_neg_le hL1 ?_
      have h4 := le_abs_self C₈
      rw [hBpdef]
      linarith
    rw [h2] at h1
    calc 8 * G₀ * (∫ t in τ₁..τ₂, (t ^ 2)⁻¹) ≤ 8 * G₀ * Real.log x ^ (-Bp) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hG₀0)
      _ = 16 * Mm ^ 2 * ((Real.log x ^ C₈) ^ 2 * Real.log x ^ (-Bp)) := by
          rw [hG₀, hLc]
          ring
      _ ≤ 16 * Mm ^ 2 * Real.log x ^ (-A) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hη₁L : η₁ * Real.log x ^ (2 * C₈ + A) ≤ 1 := by
    have h := hη₁L'
    rw [zero_mul, Real.exp_zero, mul_one] at h
    rw [hη₁]
    exact h
  have hb4 : 2 * (E₉ * (8 * ρ₁)) ≤ (32 * Mm ^ 2 + 16 * Mh ^ 2) * Real.log x ^ (-A) := by
    have h1 : E₉ * ((Real.log x ^ C₈) ^ 2 * η₁ ^ 2) ≤ Real.log x ^ (-A) := by
      refine mul_sq_mul_sq_le_rpow_neg hL0 hη₁0 ?_ hη₁L
      rw [hE₉, hη₁]
      exact hEη₁
    have h2 : E₉ * ((Real.log x ^ C₈) ^ 2 * η₂ ^ 2) ≤ Real.log x ^ (-A) := by
      refine mul_sq_mul_sq_le_rpow_neg hL0 hη₂0 ?_ ?_
      · rw [hE₉, hη₂]
        exact hEη₂
      · rw [hη₂]
        exact hη₂L
    have e : 2 * (E₉ * (8 * ρ₁)) =
        32 * Mm ^ 2 * (E₉ * ((Real.log x ^ C₈) ^ 2 * η₁ ^ 2)) +
          16 * Mh ^ 2 * (E₉ * ((Real.log x ^ C₈) ^ 2 * η₂ ^ 2)) := by
      rw [hρ₁, hG₀, hLc]
      ring
    have h3 : 32 * Mm ^ 2 * (E₉ * ((Real.log x ^ C₈) ^ 2 * η₁ ^ 2)) ≤
        32 * Mm ^ 2 * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (sq_nonneg _))
    have h4 : 16 * Mh ^ 2 * (E₉ * ((Real.log x ^ C₈) ^ 2 * η₂ ^ 2)) ≤
        16 * Mh ^ 2 * Real.log x ^ (-A) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) (sq_nonneg _))
    have e' : (32 * Mm ^ 2 + 16 * Mh ^ 2) * Real.log x ^ (-A) =
        32 * Mm ^ 2 * Real.log x ^ (-A) + 16 * Mh ^ 2 * Real.log x ^ (-A) := by ring
    rw [e, e']
    linarith
  have hfinal : ∫ t in τ₁..τ₂, ‖Ps t * Nn t‖ ^ 2 ≤
      (ρc * (1 + 12 * ρc) + 8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) +
        48 * Mm ^ 2 + 16 * Mh ^ 2) * Real.log x ^ (-A) := by
    have e : (ρc * (1 + 12 * ρc) + 8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) +
          48 * Mm ^ 2 + 16 * Mh ^ 2) * Real.log x ^ (-A) =
        ρc * (1 + 12 * ρc) * Real.log x ^ (-A) +
          8 * (1 + 12 * ρc) * (2 ^ (⌈ρc⌉₊ + 1) * |ME|) * Real.log x ^ (-A) +
          16 * Mm ^ 2 * Real.log x ^ (-A) +
          (32 * Mm ^ 2 + 16 * Mh ^ 2) * Real.log x ^ (-A) := by ring
    rw [hint_g] at hcell
    rw [e]
    linarith
  refine le_of_eq_of_le ?_ hfinal
  rw [hPs, hNn, hcf, ← hupper, hR₀def]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

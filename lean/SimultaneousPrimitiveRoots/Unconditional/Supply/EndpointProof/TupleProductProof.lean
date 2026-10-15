module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ProductTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractionErrorBounds

/-!
# The tuple products at high times

`tupleProduct : ExceptionalCount → SparseBound → LongPrimeSaving → TupleProductBound`
(`[P-06:0763–0772, 0848–0858]`): for every saving `A` there is `B'` such that every product
`P_s P_l R` has energy `≤ M L^{-A}` on the intervals of `{L^{B'} ≤ |t| ≤ 2T_0}`.

With `R_0 = a₁ Y / (4 P N_l)`, `ρ = 4a₂/a₁` (so the range of `u` is `[R_0, ρ R_0]`),
`A_s = (A + 3)/2 + |C_R|`, `A_l = (A + 1)/2 + |C_R|` and `B' = B_0(ε, C_6, A_l)`:

* Ordinary times, `|P_s(t)| ≤ L^{-A_s}`: "collapse all remaining factors. Their scale is `Y/P`"
  (`normPoly_mul_normPoly`): `P_l R` is the normalized polynomial of length `W ≤ 2a₂ Y/P` at the
  scale `Q = N_l R_0 = a₁ Y/(4P)` with coefficients `|d_w| ≤ 4L · L^{C_R}` (at most `4L` primes of
  `J` divide `w ≤ x²`), and the mean-value theorem with `2T_0 ≤ Q`
  ((cor:length-dominates-time)) gives `∫ |P_l R|² ≤ 16κ(1 + 12κ) L^{3 + 2C_R}`, `κ = 8a₂/a₁`.
* Exceptional times: `|P_s| ≤ 2`, `|P_l| ≤ M_l L^{-A_l}` ((cor:long-prime-saving); the times are
  `≤ 2T_0 ≤ x²`), (cor:exceptional-count) and (cor:sparse-bound) with `x^{ε/2} ≤ R_0 ≤ x²`
  through `integral_le_of_ordinary_exceptional`: the contribution is
  `≤ 8 M_l² |M_S| ρ L^{1 + 2C_R - 2A_l}`.

The constant is `M = 16κ(1 + 12κ) + 8 M_l² |M_S| ρ`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- **The tuple products** (`[P-06:0763–0772, 0848–0858]`), from (cor:exceptional-count),
(cor:sparse-bound) and (cor:long-prime-saving). -/
theorem tupleProduct : ExceptionalCount → SparseBound → LongPrimeSaving → TupleProductBound := by
  intro hEC hSB hLP ε a₁ a₂ c₁ c₂ C₆ CR hε ha₁ ha hC₆ A hA
  have hCR0 : 0 ≤ |CR| := abs_nonneg CR
  obtain ⟨As, hAsdef⟩ : ∃ As : ℝ, As = (A + 3) / 2 + |CR| := ⟨_, rfl⟩
  obtain ⟨Al, hAldef⟩ : ∃ Al : ℝ, Al = (A + 1) / 2 + |CR| := ⟨_, rfl⟩
  have hAs : 0 < As := by
    rw [hAsdef]
    linarith
  have hAl : 0 < Al := by
    rw [hAldef]
    linarith
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha
  obtain ⟨ρc, hρc⟩ : ∃ ρc : ℝ, ρc = 4 * a₂ / a₁ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 8 * a₂ / a₁ := ⟨_, rfl⟩
  have hρc1 : 1 ≤ ρc := by
    rw [hρc, le_div_iff₀ ha₁]
    linarith
  have hκ0 : 0 < κ := by
    rw [hκ]
    exact div_pos (by linarith) ha₁
  obtain ⟨xE, hECx⟩ := hEC As hAs
  obtain ⟨MS, xS, hSBx⟩ := hSB (ε / 2) ρc (half_pos hε) hρc1
  obtain ⟨B₀, Ml, xLp, hB₀, hLPx⟩ := hLP ε C₆ Al hε hC₆ hAl
  have hae : 0 < a₁ * Real.exp (-c₁) := mul_pos ha₁ (Real.exp_pos _)
  have hxε : ∀ᶠ x : ℝ in atTop, 4 / (a₁ * Real.exp (-c₁)) ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (half_pos hε)).eventually_ge_atTop _
  obtain ⟨x₃, hx₃⟩ :=
    Filter.eventually_atTop.mp ((eventually_productScale a₁ a₂ c₁ c₂ C₆ ha₁).and hxε)
  refine ⟨B₀, hB₀, 16 * κ * (1 + 12 * κ) + 8 * Ml ^ 2 * |MS| * ρc,
    max (max xE xS) (max xLp x₃), ?_⟩
  intro x hx Y hY1 hY2 G hG P hP1 hP2 b hb Nl hN1 hN2 J hJ hJr k hk hkL χ cR hcR τ₁ τ₂ hτ hrange
  have hxE : xE ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxS : xS ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxLp : xLp ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨⟨hx1, hL1, hscale⟩, hxεx⟩ := hx₃ x hxx₃
  obtain ⟨hYpos, hPhalf, h4aY, hTQ, hTx2⟩ := hscale Y hY1 hY2 P hP1 hP2
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hP0 : 0 < P := by linarith
  have hNhalf : 1 / 2 ≤ Nl := by
    have h1 : (1 : ℝ) ≤ x ^ ε := Real.one_le_rpow hx1.le hε.le
    linarith
  have hN0 : 0 < Nl := by linarith
  have h4P : 0 < 4 * P := by linarith
  have h4PN : 0 < 4 * P * Nl := mul_pos h4P hN0
  have hLCR : 0 ≤ Real.log x ^ CR := Real.rpow_nonneg hL0.le _
  -- the residual scale `R₀` and the collapsed scale `Q`
  obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = a₁ * Y / (4 * P * Nl) := ⟨_, rfl⟩
  have hR₀pos : 0 < R₀ := by
    rw [hR₀def]
    exact div_pos (mul_pos ha₁ hYpos) h4PN
  have hupper : a₂ * Y / (P * Nl) = ρc * R₀ := by
    rw [hρc, hR₀def, div_mul_div_comm,
      div_eq_div_iff (mul_pos hP0 hN0).ne' (mul_pos ha₁ h4PN).ne']
    ring
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Nl * R₀ := ⟨_, rfl⟩
  have hQ : Q = a₁ * Y / (4 * P) := by
    rw [hQdef, hR₀def, mul_div_assoc', div_eq_div_iff h4PN.ne' h4P.ne']
    ring
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact mul_pos hN0 hR₀pos
  have hκQ : 2 * Nl * (ρc * R₀) = κ * Q := by
    rw [hκ, hρc, hQdef]
    ring
  have hκQle : κ * Q ≤ x ^ (2 : ℝ) := by
    have e : 8 * a₂ / a₁ * (a₁ * Y / (4 * P)) = 2 * a₂ * Y / P := by
      rw [div_mul_div_comm, div_eq_div_iff (mul_pos ha₁ h4P).ne' hP0.ne']
      ring
    have h1 : 2 * a₂ * Y / P ≤ 4 * a₂ * Y := by
      rw [div_le_iff₀ hP0]
      have h2 : 4 * a₂ * Y * (1 / 2) ≤ 4 * a₂ * Y * P :=
        mul_le_mul_of_nonneg_left hPhalf
          (mul_nonneg (mul_nonneg (by norm_num) ha₂.le) hYpos.le)
      linarith
    rw [hκ, hQ, e]
    exact h1.trans h4aY
  have hR₀up : R₀ ≤ x ^ (2 : ℝ) := by
    have h1 : (1 : ℝ) ≤ 4 * P * Nl :=
      calc (1 : ℝ) = 4 * (1 / 2) * (1 / 2) := by norm_num
        _ ≤ 4 * P * Nl :=
            mul_le_mul (mul_le_mul_of_nonneg_left hPhalf (by norm_num)) hNhalf (by norm_num)
              h4P.le
    have h2 : a₁ * Y ≤ 4 * a₂ * Y := mul_le_mul_of_nonneg_right (by linarith) hYpos.le
    rw [hR₀def]
    exact ((div_le_self (mul_nonneg ha₁.le hYpos.le) h1).trans h2).trans h4aY
  have hR₀lo : x ^ (ε / 2) ≤ R₀ := by
    have h4 : 4 ≤ a₁ * Real.exp (-c₁) * x ^ (ε / 2) := (div_le_iff₀' hae).mp hxεx
    have hx1ε : x ^ (ε / 2) * x ^ (1 - ε) = x ^ (1 - ε / 2) := by
      have e : ε / 2 + (1 - ε) = 1 - ε / 2 := by ring
      rw [← Real.rpow_add hx0, e]
    have hxx : x ^ (ε / 2) * x ^ (1 - ε / 2) = x := by
      have e : ε / 2 + (1 - ε / 2) = 1 := by ring
      rw [← Real.rpow_add hx0, e, Real.rpow_one]
    have hX0 : 0 ≤ x ^ (1 - ε / 2) := Real.rpow_nonneg hx0.le _
    have hXe0 : 0 ≤ x ^ (ε / 2) := Real.rpow_nonneg hx0.le _
    have hE0 : 0 < Real.exp (Real.log x ^ (0.36 : ℝ)) := Real.exp_pos _
    have h36 : Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Real.exp (2 * Real.log x ^ (0.39 : ℝ)) := by
      have h1 : Real.log x ^ (0.36 : ℝ) ≤ Real.log x ^ (0.39 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have h2 : 0 ≤ Real.log x ^ (0.39 : ℝ) := Real.rpow_nonneg hL0.le _
      exact Real.exp_le_exp.mpr (by linarith)
    have hYlow : a₁ * (x * (Real.exp (-c₁) * Real.exp (2 * Real.log x ^ (0.39 : ℝ)))) ≤
        a₁ * Y := by
      have e : -c₁ + 2 * Real.log x ^ (0.39 : ℝ) = 2 * Real.log x ^ (0.39 : ℝ) - c₁ := by ring
      refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hY1) ha₁.le
      rw [← Real.exp_add, e]
    rw [hR₀def, le_div_iff₀ h4PN]
    calc x ^ (ε / 2) * (4 * P * Nl)
        ≤ x ^ (ε / 2) * (4 * Real.exp (Real.log x ^ (0.36 : ℝ)) * x ^ (1 - ε)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (by linarith) hN2 hN0.le (mul_nonneg (by norm_num) hE0.le)) hXe0
      _ = 4 * (x ^ (ε / 2) * x ^ (1 - ε)) * Real.exp (Real.log x ^ (0.36 : ℝ)) := by ring
      _ = 4 * x ^ (1 - ε / 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) := by rw [hx1ε]
      _ ≤ a₁ * Real.exp (-c₁) * x ^ (ε / 2) * x ^ (1 - ε / 2) *
            Real.exp (Real.log x ^ (0.36 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hX0) hE0.le
      _ = a₁ * (x ^ (ε / 2) * x ^ (1 - ε / 2) *
            (Real.exp (-c₁) * Real.exp (Real.log x ^ (0.36 : ℝ)))) := by ring
      _ = a₁ * (x * (Real.exp (-c₁) * Real.exp (Real.log x ^ (0.36 : ℝ)))) := by rw [hxx]
      _ ≤ a₁ * (x * (Real.exp (-c₁) * Real.exp (2 * Real.log x ^ (0.39 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h36 (Real.exp_pos _).le) hx0.le) ha₁.le
      _ ≤ a₁ * Y := hYlow
  -- the three polynomials
  obtain ⟨Ps, hPs⟩ : ∃ Ps : ℝ → ℂ, Ps = normPoly P (G ∩ natIcc P (2 * P)) b := ⟨_, rfl⟩
  obtain ⟨Pl, hPl⟩ : ∃ Pl : ℝ → ℂ, Pl = normPoly Nl J (fun l => χ (l : ZMod k)) := ⟨_, rfl⟩
  obtain ⟨Rr, hRr⟩ : ∃ Rr : ℝ → ℂ, Rr = normPoly R₀ (natIcc R₀ (ρc * R₀)) cR := ⟨_, rfl⟩
  have hGpos : ∀ p ∈ G ∩ natIcc P (2 * P), 0 < p := fun p hp =>
    Nat.pos_of_ne_zero (ne_zero_of_mem_natIcc hP0 (Finset.mem_inter.mp hp).2)
  have hJpos : ∀ l ∈ J, 0 < l := fun l hl => (hJ.1 l hl).pos
  have hUpos : ∀ u ∈ natIcc R₀ (ρc * R₀), 0 < u := fun u hu =>
    Nat.pos_of_ne_zero (ne_zero_of_mem_natIcc hR₀pos hu)
  have hPsc : Continuous Ps := by
    rw [hPs]
    exact continuous_normPoly P (fun n hn => (hGpos n hn).ne') b
  have hPlc : Continuous Pl := by
    rw [hPl]
    exact continuous_normPoly Nl (fun n hn => (hJpos n hn).ne') _
  have hRrc : Continuous Rr := by
    rw [hRr]
    exact continuous_normPoly R₀ (fun n hn => (hUpos n hn).ne') cR
  have hPs2 : ∀ t : ℝ, ‖Ps t‖ ≤ 2 := by
    intro t
    have h1 : ‖normPoly P (G ∩ natIcc P (2 * P)) b t‖ ≤
        P⁻¹ * (((G ∩ natIcc P (2 * P)).card : ℝ) * 1) :=
      norm_normPoly_le hP0 hGpos (fun n _ => hb n) t
    have h2 : ((G ∩ natIcc P (2 * P)).card : ℝ) ≤ 2 * P :=
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans
        (card_natIcc_le hP0 (by linarith))
    have h3 : P⁻¹ * (((G ∩ natIcc P (2 * P)).card : ℝ) * 1) ≤ P⁻¹ * (2 * P) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hP0.le)
    have e : P⁻¹ * (2 * P) = 2 := by
      rw [mul_comm 2 P, ← mul_assoc, inv_mul_cancel₀ hP0.ne', one_mul]
    rw [hPs]
    linarith
  -- the times of `[τ₁, τ₂]`
  have hlo0 : 0 ≤ Real.log x ^ B₀ := Real.rpow_nonneg hL0.le _
  have htime : ∀ t ∈ Set.Icc τ₁ τ₂, Real.log x ^ B₀ ≤ |t| ∧ |t| ≤ x ^ (2 : ℝ) := fun t ht =>
    ⟨(abs_mem_of_highRange hlo0 hrange ht).1, (abs_mem_of_highRange hlo0 hrange ht).2.trans hTx2⟩
  have hlen : τ₂ - τ₁ ≤ Q := by
    rw [hQ]
    exact (sub_le_of_highRange hlo0 hrange).trans hTQ
  have hx23 : x ^ (2 : ℝ) ≤ 2 * x ^ (3 : ℝ) := by
    have h1 : x ^ (2 : ℝ) ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
    have h2 : 0 ≤ x ^ (3 : ℝ) := Real.rpow_nonneg hx0.le _
    linarith
  -- the collapsed polynomial `P_l R`
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ, W = ⌊2 * Nl * (ρc * R₀)⌋₊ := ⟨_, rfl⟩
  have hκQ0 : 0 ≤ κ * Q := mul_nonneg hκ0.le hQpos.le
  have hWle : (W : ℝ) ≤ κ * Q := by
    rw [hWdef, ← hκQ]
    refine Nat.floor_le ?_
    rw [hκQ]
    exact hκQ0
  have hWx2 : (W : ℝ) ≤ x ^ (2 : ℝ) := hWle.trans hκQle
  have hW : ∀ y ∈ J ×ˢ natIcc R₀ (ρc * R₀), y.1 * y.2 ∈ Finset.Icc 1 W := by
    intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hy
    have hl := hJpos y.1 h1
    have hu := hUpos y.2 h2
    have hl2 : (y.1 : ℝ) ≤ 2 * Nl := (hJr y.1 h1).2
    have hu2 : (y.2 : ℝ) ≤ ρc * R₀ := ((mem_natIcc_of_pos hR₀pos).mp h2).2
    refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hl hu), ?_⟩
    rw [hWdef]
    refine Nat.le_floor ?_
    rw [Nat.cast_mul]
    exact mul_le_mul hl2 hu2 (Nat.cast_nonneg _) (by linarith)
  obtain ⟨dc, hdc⟩ : ∃ dc : ℕ → ℂ,
      dc = collapseCoeff J (natIcc R₀ (ρc * R₀)) (fun l => χ (l : ZMod k)) cR := ⟨_, rfl⟩
  have hprod : ∀ t : ℝ, Pl t * Rr t = normPoly (Nl * R₀) (Finset.Icc 1 W) dc t := by
    intro t
    rw [hPl, hRr, hdc]
    exact normPoly_mul_normPoly Nl R₀ J _ _ cR hW t
  have hdcle : ∀ w ∈ Finset.Icc 1 W, ‖dc w‖ ≤ 4 * Real.log x * Real.log x ^ CR := by
    intro w hw
    have hw1 : 1 ≤ w := (Finset.mem_Icc.mp hw).1
    have hw2 : (w : ℝ) ≤ x ^ (2 : ℝ) := (Nat.cast_le.mpr (Finset.mem_Icc.mp hw).2).trans hWx2
    have h1 : ‖collapseCoeff J (natIcc R₀ (ρc * R₀)) (fun l => χ (l : ZMod k)) cR w‖ ≤
        ((J.filter fun l => l ∣ w).card : ℝ) * Real.log x ^ CR :=
      norm_collapseCoeff_le hJpos (fun l _ => DirichletCharacter.norm_le_one χ _)
        (fun u _ => hcR u) hLCR w
    have h2 : ((J.filter fun l => l ∣ w).card : ℝ) ≤ 4 * Real.log x :=
      card_filter_dvd_le hJ.1 hw1 hx1 hw2
    rw [hdc]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hLCR)
  have hlogW : Real.log (W : ℝ) ≤ 2 * Real.log x := by
    by_cases hW0 : W = 0
    · rw [hW0, Nat.cast_zero, Real.log_zero]
      linarith
    · have hWpos : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hW0)
      have h1 := Real.log_le_log hWpos hWx2
      rw [Real.log_rpow hx0] at h1
      exact h1
  have hlogW0 : 0 ≤ Real.log (W : ℝ) := Real.log_natCast_nonneg W
  have hW0 : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg W
  have hmean : ∫ t in τ₁..τ₂, ‖Pl t * Rr t‖ ^ 2 ≤
      16 * κ * (1 + 12 * κ) * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2) := by
    have h1 : ∫ t in τ₁..τ₂, ‖Pl t * Rr t‖ ^ 2 =
        ∫ t in τ₁..τ₂, ‖normPoly (Nl * R₀) (Finset.Icc 1 W) dc t‖ ^ 2 :=
      congrArg (fun g : ℝ → ℝ => ∫ t in τ₁..τ₂, g t) (funext fun t => by rw [hprod t])
    have h2 := integral_normSq_normPoly_le (R := Nl * R₀) (Finset.Subset.refl (Finset.Icc 1 W))
      dc hτ
    have h3 : ∑ w ∈ Finset.Icc 1 W, ‖dc w‖ ^ 2 ≤
        κ * Q * (4 * Real.log x * Real.log x ^ CR) ^ 2 :=
      calc ∑ w ∈ Finset.Icc 1 W, ‖dc w‖ ^ 2
          ≤ ∑ _w ∈ Finset.Icc 1 W, (4 * Real.log x * Real.log x ^ CR) ^ 2 :=
            Finset.sum_le_sum fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hdcle w hw) 2
        _ = (W : ℝ) * (4 * Real.log x * Real.log x ^ CR) ^ 2 := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ κ * Q * (4 * Real.log x * Real.log x ^ CR) ^ 2 :=
            mul_le_mul_of_nonneg_right hWle (sq_nonneg _)
    have h4 : (τ₂ - τ₁) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤
        Q * ((1 + 12 * κ) * Real.log x) := by
      have h5 : 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤ 4 * (κ * Q) * (3 * Real.log x) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hWle (by norm_num)) (by linarith) (by linarith)
          (mul_nonneg (by norm_num) hκQ0)
      have h6 : Q ≤ Q * Real.log x := le_mul_of_one_le_right hQpos.le hL1
      have e : Q * ((1 + 12 * κ) * Real.log x) =
          Q * Real.log x + 4 * (κ * Q) * (3 * Real.log x) := by ring
      rw [e]
      linarith
    have h7 : 0 ≤ Q * ((1 + 12 * κ) * Real.log x) :=
      mul_nonneg hQpos.le (mul_nonneg (by linarith) hL0.le)
    have hQQ : (Q ^ 2)⁻¹ * (Q * Q) = 1 := by
      rw [← pow_two]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hQpos.ne')
    rw [← hQdef] at h2
    rw [h1, ← hQdef]
    calc ∫ t in τ₁..τ₂, ‖normPoly Q (Finset.Icc 1 W) dc t‖ ^ 2
        ≤ (Q ^ 2)⁻¹ * (((τ₂ - τ₁) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
            ∑ w ∈ Finset.Icc 1 W, ‖dc w‖ ^ 2) := h2
      _ ≤ (Q ^ 2)⁻¹ * (Q * ((1 + 12 * κ) * Real.log x) *
            (κ * Q * (4 * Real.log x * Real.log x ^ CR) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul h4 h3 (Finset.sum_nonneg fun w _ => sq_nonneg _) h7)
            (inv_nonneg.mpr (sq_nonneg _))
      _ = 16 * κ * (1 + 12 * κ) * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2) *
            ((Q ^ 2)⁻¹ * (Q * Q)) := by ring
      _ = 16 * κ * (1 + 12 * κ) * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2) := by
          rw [hQQ, mul_one]
  -- the long-prime saving on the times of `[τ₁, τ₂]`
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = Ml * Real.log x ^ (-Al) := ⟨_, rfl⟩
  have hPlb : ∀ t ∈ Set.Icc τ₁ τ₂, ‖Pl t‖ ≤ Mb := by
    intro t ht
    rw [hPl, hMb]
    exact hLPx x hxLp Nl hN1 hN2 J hJ hJr k hk hkL χ t (htime t ht).1 (htime t ht).2
  -- the threshold and the three functions
  obtain ⟨Λs, hΛs⟩ : ∃ Λs : ℝ, Λs = Real.log x ^ (-As) := ⟨_, rfl⟩
  have hΛs0 : 0 ≤ Λs := by
    rw [hΛs]
    exact Real.rpow_nonneg hL0.le _
  have hFc : Continuous fun t : ℝ => ‖Ps t * Pl t * Rr t‖ ^ 2 :=
    ((hPsc.mul hPlc).mul hRrc).norm.pow 2
  have hgc : Continuous fun t : ℝ => Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 :=
    continuous_const.mul ((hPlc.mul hRrc).norm.pow 2)
  have hρcont : Continuous fun t : ℝ => 4 * Mb ^ 2 * ‖Rr t‖ ^ 2 :=
    continuous_const.mul (hRrc.norm.pow 2)
  have hord : ∀ t ∈ Set.Icc τ₁ τ₂, ¬ Λs < ‖Ps t‖ →
      ‖Ps t * Pl t * Rr t‖ ^ 2 ≤ Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 := by
    intro t _ hnot
    have h1 : ‖Ps t‖ ≤ Λs := not_lt.mp hnot
    rw [mul_assoc, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _)
  have hexc : ∀ t ∈ Set.Icc τ₁ τ₂, Λs < ‖Ps t‖ →
      ‖Ps t * Pl t * Rr t‖ ^ 2 ≤ Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 + 4 * Mb ^ 2 * ‖Rr t‖ ^ 2 := by
    intro t ht _
    have h1 := hPlb t ht
    have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans h1
    have h2 : ‖Ps t * Pl t * Rr t‖ ≤ 2 * Mb * ‖Rr t‖ := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (hPs2 t) h1 (norm_nonneg _) (by norm_num)) (norm_nonneg _)
    have h3 : ‖Ps t * Pl t * Rr t‖ ^ 2 ≤ (2 * Mb * ‖Rr t‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have e : (2 * Mb * ‖Rr t‖) ^ 2 = 4 * Mb ^ 2 * ‖Rr t‖ ^ 2 := by ring
    have h4 : 0 ≤ Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [e] at h3
    linarith
  have hcount : ∀ 𝒮 : Finset ℝ, (∀ s ∈ 𝒮, s ∈ Set.Icc τ₁ τ₂ ∧ Λs < ‖Ps s‖) →
      (∀ s ∈ 𝒮, ∀ s' ∈ 𝒮, s ≠ s' → 1 ≤ |s - s'|) →
      (𝒮.card : ℝ) ≤ Real.exp (Real.log x ^ (0.9 : ℝ)) := by
    intro 𝒮 h𝒮 hsep
    refine hECx x hxE G hG P hP1 hP2 b hb 𝒮 (fun s hs => (htime s (h𝒮 s hs).1).2) hsep ?_
    intro s hs
    have h1 := (h𝒮 s hs).2
    rw [hΛs, hPs] at h1
    exact h1
  have hcoefR : R₀⁻¹ * ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cR n‖ ^ 2 ≤ ρc * (Real.log x ^ CR) ^ 2 := by
    have h1 : ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cR n‖ ^ 2 ≤
        ρc * R₀ * (Real.log x ^ CR) ^ 2 :=
      calc ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cR n‖ ^ 2
          ≤ ∑ _n ∈ natIcc R₀ (ρc * R₀), (Real.log x ^ CR) ^ 2 :=
            Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hcR n) 2
        _ = ((natIcc R₀ (ρc * R₀)).card : ℝ) * (Real.log x ^ CR) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ρc * R₀ * (Real.log x ^ CR) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (card_natIcc_le hR₀pos (mul_nonneg (by linarith) hR₀pos.le)) (sq_nonneg _)
    calc R₀⁻¹ * ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cR n‖ ^ 2
        ≤ R₀⁻¹ * (ρc * R₀ * (Real.log x ^ CR) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hR₀pos.le)
      _ = ρc * (Real.log x ^ CR) ^ 2 * (R₀⁻¹ * R₀) := by ring
      _ = ρc * (Real.log x ^ CR) ^ 2 := by rw [inv_mul_cancel₀ hR₀pos.ne', mul_one]
  have hsparse : ∀ 𝒯 : Finset ℝ, (∀ t ∈ 𝒯, t ∈ Set.Icc τ₁ τ₂) →
      (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) →
      (𝒯.card : ℝ) ≤ Real.exp (Real.log x ^ (0.9 : ℝ)) →
      ∑ t ∈ 𝒯, 4 * Mb ^ 2 * ‖Rr t‖ ^ 2 ≤
        4 * Mb ^ 2 * (|MS| * Real.log x * (ρc * (Real.log x ^ CR) ^ 2)) := by
    intro 𝒯 h𝒯 hsep hcard
    have hE0 : 0 ≤ Real.exp (Real.log x ^ (0.9 : ℝ)) := (Real.exp_pos _).le
    have h1 := hSBx x hxS R₀ hR₀lo hR₀up cR 𝒯
      (fun t ht => (htime t (h𝒯 t ht)).2.trans hx23) hsep (by linarith)
    have h2 : MS * Real.log x * (R₀⁻¹ * ∑ n ∈ natIcc R₀ (ρc * R₀), ‖cR n‖ ^ 2) ≤
        |MS| * Real.log x * (ρc * (Real.log x ^ CR) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self MS) hL0.le) hcoefR
        (mul_nonneg (inv_nonneg.mpr hR₀pos.le) (Finset.sum_nonneg fun n _ => sq_nonneg _))
        (mul_nonneg (abs_nonneg _) hL0.le)
    rw [← Finset.mul_sum, hRr]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg (by norm_num) (sq_nonneg _))
  have hcell : ∫ t in τ₁..τ₂, ‖Ps t * Pl t * Rr t‖ ^ 2 ≤
      (∫ t in τ₁..τ₂, Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2) +
        2 * (4 * Mb ^ 2 * (|MS| * Real.log x * (ρc * (Real.log x ^ CR) ^ 2))) :=
    integral_le_of_ordinary_exceptional hτ hFc.continuousOn hgc.continuousOn
      hρcont.continuousOn
      (fun t _ => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _))
      (fun t : ℝ => Λs < ‖Ps t‖) hord hexc hcount hsparse
  -- the two contributions
  have hint_g : ∫ t in τ₁..τ₂, Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 ≤
      16 * κ * (1 + 12 * κ) * Real.log x ^ (-A) := by
    have h1 : ∫ t in τ₁..τ₂, Λs ^ 2 * ‖Pl t * Rr t‖ ^ 2 =
        Λs ^ 2 * ∫ t in τ₁..τ₂, ‖Pl t * Rr t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    have h2 : (Real.log x ^ (-As)) ^ 2 * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2) ≤
        Real.log x ^ (-A) := by
      refine rpow_neg_sq_mul_le hL1 3 ?_
      have h3 := le_abs_self CR
      rw [hAsdef]
      push_cast
      linarith
    rw [h1, hΛs]
    calc (Real.log x ^ (-As)) ^ 2 * ∫ t in τ₁..τ₂, ‖Pl t * Rr t‖ ^ 2
        ≤ (Real.log x ^ (-As)) ^ 2 *
            (16 * κ * (1 + 12 * κ) * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2)) :=
          mul_le_mul_of_nonneg_left hmean (sq_nonneg _)
      _ = 16 * κ * (1 + 12 * κ) *
            ((Real.log x ^ (-As)) ^ 2 * (Real.log x ^ 3 * (Real.log x ^ CR) ^ 2)) := by ring
      _ ≤ 16 * κ * (1 + 12 * κ) * Real.log x ^ (-A) :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg (mul_nonneg (by norm_num) hκ0.le) (by linarith))
  have hexcsum : 2 * (4 * Mb ^ 2 * (|MS| * Real.log x * (ρc * (Real.log x ^ CR) ^ 2))) ≤
      8 * Ml ^ 2 * |MS| * ρc * Real.log x ^ (-A) := by
    have h2 : (Real.log x ^ (-Al)) ^ 2 * (Real.log x ^ 1 * (Real.log x ^ CR) ^ 2) ≤
        Real.log x ^ (-A) := by
      refine rpow_neg_sq_mul_le hL1 1 ?_
      have h3 := le_abs_self CR
      rw [hAldef]
      push_cast
      linarith
    have e : 2 * (4 * Mb ^ 2 * (|MS| * Real.log x * (ρc * (Real.log x ^ CR) ^ 2))) =
        8 * Ml ^ 2 * |MS| * ρc *
          ((Real.log x ^ (-Al)) ^ 2 * (Real.log x ^ 1 * (Real.log x ^ CR) ^ 2)) := by
      rw [hMb]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h2
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (abs_nonneg _))
        (by linarith))
  have hfinal : ∫ t in τ₁..τ₂, ‖Ps t * Pl t * Rr t‖ ^ 2 ≤
      (16 * κ * (1 + 12 * κ) + 8 * Ml ^ 2 * |MS| * ρc) * Real.log x ^ (-A) := by
    have e : (16 * κ * (1 + 12 * κ) + 8 * Ml ^ 2 * |MS| * ρc) * Real.log x ^ (-A) =
        16 * κ * (1 + 12 * κ) * Real.log x ^ (-A) +
          8 * Ml ^ 2 * |MS| * ρc * Real.log x ^ (-A) := by ring
    rw [e]
    linarith
  refine le_of_eq_of_le ?_ hfinal
  rw [hPs, hPl, hRr, ← hupper, hR₀def]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound

/-!
# The extracted coefficients are bounded by a fixed log power

`coefficientBound d : MertensReciprocal → PartialMarkedBound → CoefficientBound d`
(`[P-06:0697–0698, 0712–0713]`): on `1 ≤ u ≤ x²`,
`|W_{𝐭 - 𝐞_{g_s}}^𝐛(u) 𝒲(u)| ≤ L^C` and
`|W_{𝐭 - 𝐞_{g_s}}^𝐛(u) 𝒲(u) ∑_{l_2, …, l_{d+1}} 1_{l_2 ⋯ l_{d+1} ∣ u}| ≤ L^C`.

* `𝒲` is bounded for fixed `K, q` (`Extraction.arrayWeightBounded_all`, from Mertens): `|𝒲| ≤ C_W`
  for `x ≥ x_W`.
* The remaining marked weight is `≤ L^{C₁}` (`PartialMarkedBound`, with `U = {g_s}`).
* "Slot multiplicities at each `w ≍ Y` remain bounded" (`slotCountRep_le`): the entries of a tuple
  whose product divides `u ≤ x²` are primes `≥ x^ε` dividing `u`, and there are at most `2/ε` such
  primes (`Extraction.card_le_two_div`), so there are at most `(2/ε)^d` tuples.
* The constant `B = max(1, 2/ε)^d · max(1, C_W)` is `≤ L^{log B}` once `log L ≥ 1`.

The exponent is `C = log B + C₁` and the threshold is `max(x_W, x₁, exp(e))`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- **Slot multiplicities remain bounded** (`[P-06:0697–0698]`): for slots of primes `≥ x^ε` and
`1 ≤ u ≤ x²`, the number of tuples `(l_1, …, l_d) ∈ ∏ S_i` (repetitions allowed) with
`l_1 ⋯ l_d ∣ u` is at most `(2/ε)^d`. -/
theorem slotCountRep_le {d : ℕ} {ε x : ℝ} (hε : 0 < ε) (hx : 1 < x) {S : Fin d → Finset ℕ}
    (hprime : ∀ i, ∀ ℓ ∈ S i, ℓ.Prime) (hlow : ∀ i, ∀ ℓ ∈ S i, x ^ ε ≤ (ℓ : ℝ)) {u : ℕ}
    (hu : 1 ≤ u) (hu2 : (u : ℝ) ≤ x * x) : (slotCountRep S u : ℝ) ≤ (2 / ε) ^ d := by
  have hx0 : 0 < x := by linarith
  have hsub : ((Fintype.piFinset S).filter fun 𝔩 => (∏ i, 𝔩 i) ∣ u) ⊆
      Fintype.piFinset fun i => (S i).filter fun ℓ => ℓ ∣ u := by
    intro 𝔩 h𝔩
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h𝔩
    refine Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp h1 i, ?_⟩
    exact (Finset.dvd_prod_of_mem 𝔩 (Finset.mem_univ i)).trans h2
  have hcard : ∀ i, (((S i).filter fun ℓ => ℓ ∣ u).card : ℝ) ≤ 2 / ε := fun i =>
    Extraction.card_le_two_div (R := x) hε hx0 hx le_rfl hu hu2
      (fun ℓ hℓ => hprime i ℓ (Finset.mem_filter.mp hℓ).1)
      (fun ℓ hℓ => (Finset.mem_filter.mp hℓ).2)
      (fun ℓ hℓ => hlow i ℓ (Finset.mem_filter.mp hℓ).1)
  have hle : ((Fintype.piFinset S).filter fun 𝔩 => (∏ i, 𝔩 i) ∣ u).card ≤
      (Fintype.piFinset fun i => (S i).filter fun ℓ => ℓ ∣ u).card := Finset.card_le_card hsub
  unfold slotCountRep
  calc ((((Fintype.piFinset S).filter fun 𝔩 => (∏ i, 𝔩 i) ∣ u).card : ℕ) : ℝ)
      ≤ (((Fintype.piFinset fun i => (S i).filter fun ℓ => ℓ ∣ u).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr hle
    _ = ∏ i : Fin d, (((S i).filter fun ℓ => ℓ ∣ u).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
    _ ≤ ∏ _i : Fin d, (2 / ε) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hcard i)
    _ = (2 / ε) ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The extracted coefficients are bounded by a fixed log power** on `1 ≤ u ≤ x²`
(`[P-06:0697–0698, 0712–0713]`), from Mertens' estimate (the bound for `𝒲`) and
(cor:marked-bound) with one mark removed. -/
theorem coefficientBound (d : ℕ) :
    MertensReciprocal → PartialMarkedBound → CoefficientBound d := by
  intro hM hPM D
  obtain ⟨CW, hCW⟩ := Extraction.arrayWeightBounded_all hM D.q D.q_pos D.q_lt_one D.K
  obtain ⟨xW, hxW⟩ := Filter.eventually_atTop.mp (hCW D.𝔞)
  obtain ⟨C₁, x₁, hC₁⟩ := hPM D.P D.q₀ D.q₀_pos D.q₀_lt_one D.m'
  have hB₀ : (1 : ℝ) ≤ max 1 CW := le_max_left _ _
  have hB₁ : (1 : ℝ) ≤ max 1 (2 / D.ε) := le_max_left _ _
  have hB₁d : (1 : ℝ) ≤ max 1 (2 / D.ε) ^ d := one_le_pow₀ hB₁
  have hB : (1 : ℝ) ≤ max 1 (2 / D.ε) ^ d * max 1 CW :=
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ max 1 (2 / D.ε) ^ d * max 1 CW :=
          mul_le_mul hB₁d hB₀ zero_le_one (zero_le_one.trans hB₁d)
  have hBpos : (0 : ℝ) < max 1 (2 / D.ε) ^ d * max 1 CW := lt_of_lt_of_le one_pos hB
  refine ⟨Real.log (max 1 (2 / D.ε) ^ d * max 1 CW) + C₁,
    max (max xW x₁) (Real.exp (Real.exp 1)), fun x hx c hc i₀ u hu1 hu2 => ?_⟩
  -- the thresholds
  have hxW' : xW ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx₁ : x₁ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxe : Real.exp (Real.exp 1) ≤ x := (le_max_right _ _).trans hx
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hee : (3 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h := Real.add_one_le_exp (Real.exp 1)
    linarith
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hLe : Real.exp 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL : 0 < Real.log x := by linarith
  have hLL : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL).mpr hLe
  -- the constant is at most a power of `L`
  have hBpow : max 1 (2 / D.ε) ^ d * max 1 CW ≤
      Real.log x ^ Real.log (max 1 (2 / D.ε) ^ d * max 1 CW) := by
    rw [Real.rpow_def_of_pos hL]
    calc max 1 (2 / D.ε) ^ d * max 1 CW
        = Real.exp (Real.log (max 1 (2 / D.ε) ^ d * max 1 CW)) := (Real.exp_log hBpos).symm
      _ ≤ Real.exp (Real.log (Real.log x) * Real.log (max 1 (2 / D.ε) ^ d * max 1 CW)) :=
          Real.exp_le_exp.mpr (le_mul_of_one_le_left (Real.log_nonneg hB) hLL)
  have hLC₁ : 0 ≤ Real.log x ^ C₁ := Real.rpow_nonneg hL.le _
  have hfin : max 1 (2 / D.ε) ^ d * (max 1 CW * Real.log x ^ C₁) ≤
      Real.log x ^ (Real.log (max 1 (2 / D.ε) ^ d * max 1 CW) + C₁) := by
    rw [Real.rpow_add hL, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hBpow hLC₁
  -- the three factors
  have hW : |markedWeight D.q D.𝔞 x u| ≤ CW := hxW x hxW' u
  have hP : ‖partialWeight c.𝔊 D.q₀ c.t c.test {Sum.inl i₀} u‖ ≤ Real.log x ^ C₁ :=
    hC₁ x hx₁ c.𝔊 hc.groups c.t (fun g => (hc.marks g).2) c.test hc.test_le {Sum.inl i₀} u
  have hu2' : (u : ℝ) ≤ x * x := by
    rw [Real.rpow_two, pow_two] at hu2
    exact hu2
  have hslot : (slotCountRep (tailSlots c.S) u : ℝ) ≤ (2 / D.ε) ^ d :=
    slotCountRep_le D.ε_pos hx1 (fun i => hc.slots.prime i.succ)
      (fun i => hc.slots.lower i.succ) hu1 hu2'
  -- the constant coefficient
  have hconst : ‖c.constCoeff D x i₀ u‖ ≤ max 1 CW * Real.log x ^ C₁ := by
    unfold EndpointConfig.constCoeff hMarks
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hW.trans (le_max_right _ _)) hP (norm_nonneg _) (zero_le_one.trans hB₀)
  -- the tuple coefficient
  have htuple : ‖c.tupleCoeff D x i₀ u‖ ≤
      max 1 (2 / D.ε) ^ d * (max 1 CW * Real.log x ^ C₁) := by
    unfold EndpointConfig.tupleCoeff
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul
      (hslot.trans (pow_le_pow_left₀ (div_pos two_pos D.ε_pos).le (le_max_right _ _) d))
      hconst (norm_nonneg _) (zero_le_one.trans hB₁d)
  have hconst' : ‖c.constCoeff D x i₀ u‖ ≤
      max 1 (2 / D.ε) ^ d * (max 1 CW * Real.log x ^ C₁) :=
    hconst.trans (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans hB₀) hLC₁) hB₁d)
  exact ⟨hconst'.trans hfin, htuple.trans hfin⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

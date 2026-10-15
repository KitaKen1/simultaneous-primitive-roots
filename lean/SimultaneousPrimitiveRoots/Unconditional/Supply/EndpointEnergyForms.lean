module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSided

/-!
# The two forms of (cor:SM) are equivalent

`EndpointEnergyPaper d` is [P]'s (cor:SM) for every fixed `C_6` (`k ≤ L^{C_6}`,
`T_0 = x L^{C_6 + 1}`, `[P-06:0544–0550]`); `EndpointEnergy d` is the public paper's
(eq:energy-input) (`k ≤ L^B`, `T ≤ x L^C` for all fixed `B, C`, `[PUB-tex:0199–0206]`). They are
equivalent (`endpointEnergy_iff_endpointEnergyPaper`): the energy integral increases with the time
range and `L^B ≤ L^{C_6}` for `B ≤ C_6` and `L ≥ 1`, so the case `(B, C)` follows from
`C_6 = max(B, C)`. This is the remark of `[PUB-tex:0318–0321, 0496–0500]` and
`[PUB-ja:0086–0092]` that the estimate at a larger fixed exponent covers the larger denominators
on their full time intervals.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter Asymptotics MeasureTheory
open scoped Topology ContDiff

noncomputable section

/-- The endpoint polynomial of a finitely supported sequence vanishing at `0` is continuous in the
time variable. -/
theorem continuous_endpointPolynomial {U : ℕ → ℂ} {s : Finset ℕ} (hs : ∀ w, U w ≠ 0 → w ∈ s)
    (h0 : U 0 = 0) (Y : ℝ) (h : ℤ) (k : ℕ) :
    Continuous fun τ : ℝ => endpointPolynomial U Y h k τ := by
  have heq : (fun τ : ℝ => endpointPolynomial U Y h k τ) = fun τ : ℝ =>
      (Y : ℂ)⁻¹ * ∑ w ∈ s.erase 0, U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
        (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
    funext τ
    have hsub : Function.support (fun w : ℕ => U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
        (w : ℂ) ^ ((τ : ℂ) * Complex.I)) ⊆ ↑(s.erase 0) := by
      intro w hw
      rw [Function.mem_support] at hw
      have hU : U w ≠ 0 := fun h' => hw (by rw [h', zero_mul, zero_mul])
      have hw0 : w ≠ 0 := fun h' => hU (by rw [h']; exact h0)
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hw0, hs w hU⟩)
    unfold endpointPolynomial
    rw [finsum_eq_sum_of_support_subset _ hsub]
  rw [heq]
  refine continuous_const.mul (continuous_finsetSum _ fun w hw => ?_)
  have hw0 : (w : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.ne_of_mem_erase hw)
  exact continuous_const.mul
    ((Complex.continuous_ofReal.mul continuous_const).const_cpow (Or.inl hw0))

/-- A comparison endpoint with cutoff supported in `[a₁, a₂] ⊂ (0, ∞)` at a positive scale `Y`
is supported on `1 ≤ w ≤ a₂ Y`. -/
theorem comparisonEndpoint_support (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ)
    (𝔊 : ActiveGroups) {d : ℕ} (S : Fin d → Finset ℕ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) {ψ₁ : ℝ → ℂ} {a₁ a₂ : ℝ} (ha₁ : 0 < a₁)
    (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (σ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    (∀ w : ℕ, comparisonEndpoint q q₀ 𝔞 x 𝔊 S t test ψ₁ σ Y w ≠ 0 →
        w ∈ Finset.range (⌊a₂ * Y⌋₊ + 1)) ∧
      comparisonEndpoint q q₀ 𝔞 x 𝔊 S t test ψ₁ σ Y 0 = 0 := by
  have hψ : ∀ u : ℝ, ψ₁ u ≠ 0 → a₁ ≤ u ∧ u ≤ a₂ := fun u hu => hsupp hu
  constructor
  · intro w hw
    have hψw : ψ₁ ((w : ℝ) / Y) ≠ 0 := by
      intro h'
      apply hw
      unfold comparisonEndpoint
      rw [h', zero_mul, zero_mul, zero_mul]
    have hle : (w : ℝ) ≤ a₂ * Y := (div_le_iff₀ hY).mp (hψ _ hψw).2
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hle))
  · have hψ0 : ψ₁ (((0 : ℕ) : ℝ) / Y) = 0 := by
      by_contra h'
      have := (hψ _ h').1
      rw [Nat.cast_zero, zero_div] at this
      linarith
    unfold comparisonEndpoint
    rw [hψ0, zero_mul, zero_mul, zero_mul]

/-- **[P]'s (cor:SM) for all `C_6` gives the form with independent exponents.** -/
theorem endpointEnergy_of_endpointEnergyPaper {d : ℕ} (h : EndpointEnergyPaper d) :
    EndpointEnergy d := by
  intro B C hB hC ε hε q q₀ hq hq1 hq₀ hq₀1 K 𝔞 P m' a₁ a₂ ha₁ ha₁₂ Dψ Cσ c₁ c₂ A hA
  obtain ⟨M, x₀, hM⟩ := h (max B C) (lt_max_of_lt_left hB) ε hε q q₀ hq hq1 hq₀ hq₀1 K 𝔞 P m'
    a₁ a₂ ha₁ ha₁₂ Dψ Cσ c₁ c₂ A hA
  refine ⟨M, max x₀ (Real.exp 1), ?_⟩
  intro x hx 𝔊 h𝔊 S hS Y hY1 hY2 t ht ht1 test htest hbig σ hσ ψ₁ hψ hsupp hder k hk hkL n
  have hx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hL1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hY : 0 < Y := lt_of_lt_of_le (mul_pos hx0 (Real.exp_pos _)) hY1
  have hk' : (k : ℝ) ≤ Real.log x ^ max B C :=
    hkL.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left B C))
  have hbound := hM x hx₀ 𝔊 h𝔊 S hS Y hY1 hY2 t ht ht1 test htest hbig σ hσ ψ₁ hψ hsupp hder k hk
    hk' n
  refine le_trans ?_ hbound
  have hT : x * Real.log x ^ C ≤ x * Real.log x ^ (max B C + 1) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by have := le_max_right B C; linarith)) hx0.le
  have hT0 : 0 ≤ x * Real.log x ^ C :=
    mul_nonneg hx0.le (Real.rpow_nonneg (zero_le_one.trans hL1) _)
  obtain ⟨hs, h0⟩ := comparisonEndpoint_support q q₀ 𝔞 x 𝔊 S t test ha₁ hsupp σ hY
  have hcont : Continuous fun τ : ℝ =>
      ‖endpointPolynomial (comparisonEndpoint q q₀ 𝔞 x 𝔊 S t test ψ₁ σ Y) Y n k τ‖ ^ 2 :=
    (continuous_endpointPolynomial hs h0 Y n k).norm.pow 2
  exact intervalIntegral.integral_mono_interval (neg_le_neg hT) (by linarith) hT
    (Filter.Eventually.of_forall fun τ => sq_nonneg _) (hcont.intervalIntegrable _ _)

/-- **The two forms of (cor:SM) are equivalent.** -/
theorem endpointEnergy_iff_endpointEnergyPaper (d : ℕ) :
    EndpointEnergy d ↔ EndpointEnergyPaper d :=
  ⟨endpointEnergyPaper_of_endpointEnergy, endpointEnergy_of_endpointEnergyPaper⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply

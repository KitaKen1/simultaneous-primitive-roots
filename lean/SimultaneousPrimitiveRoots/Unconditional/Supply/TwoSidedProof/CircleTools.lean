module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ArcEnergyTools

/-!
# Tools for the circle method

The analytic part of the proof of `CircleLink d H` (`[P-06:0476–0486]`,
`TwoSidedProof/CircleProof.lean`), for finite sequences on `ℕ`. With the convention
`â(θ) = ∑_w a_w e(θ w)` (`CircleMethod.trigSum`):

* orthogonality, `∫_a^{a+1} e(θ n) dθ = 1_{n = 0}` (`integral_addChar_mul_intCast`);
* Parseval on a period, `∫_a^{a+1} |â(θ)|² dθ = ∑_w |a_w|²` (`integral_normSq_trigSum`);
* the correlation `∑_w 𝒰(w) 𝒱(w + D) = ∫_0^1 𝒰̂(θ) 𝒱̂(-θ) e(θ D) dθ`
  (`integral_trigSum_mul_trigSum_neg`), and its average over the shifts
  (`sum_mul_finsum_eq_integral`): the bilinear sum is `∫_0^1 𝒰̂(θ) 𝒱̂(-θ) 𝔪(θ) dθ`;
* `integral_le_of_arcs`: an integral over `[0, 1]` of a function that is bounded by `G₀`
  outside finitely many arcs `|θ - c_i| ≤ δ` and by `G₁` on them;
* `norm_integral_circle_le`: "Parseval and (cor:endpoint-squares) handle the complement of
  `𝔐_H`. On its `O(L^{2C_6})` arcs, Cauchy and the global energy of `𝒱` reduce the problem to
  (cor:arc-energy-target)". Cauchy's inequality is used in the form
  `2|P||Q| ≤ λ|P|² + λ⁻¹|Q|²`;
* `circle_core`: the same for the first sequence twisted by `e(jw/H)`: the arcs at `h/k`,
  `k ≤ Q`, become arcs of the untwisted sequence at `(hH + jk)/(kH)` with denominators
  `kH ≤ QH` ("The shifted denominators are at most `Hk`", `[PUB-tex:0497–0498]`); the arcs that
  meet `[0, 1]` have `1 ≤ k ≤ Q`, `-1 ≤ h ≤ Q + 1`, at most `4Q²` of them;
* `circle_final`: the powers of `L`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace CircleMethod

/-! ### The additive character -/

/-- `e(0) = 1`. -/
theorem addChar_zero : addChar 0 = 1 := by
  unfold addChar
  rw [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]

/-- `e(-x)` is the conjugate of `e(x)`. -/
theorem addChar_neg (x : ℝ) : addChar (-x) = conj (addChar x) := by
  have h1 : addChar (-x) * addChar x = 1 := by
    rw [← addChar_add, neg_add_cancel, addChar_zero]
  have h2 : conj (addChar x) * addChar x = 1 := by
    rw [Complex.conj_mul', EndpointProof.norm_addChar, Complex.ofReal_one, one_pow]
  have h3 : addChar x ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

/-- `θ ↦ e(θ y)` is continuous. -/
theorem continuous_addChar_mul (y : ℝ) : Continuous fun θ : ℝ => addChar (θ * y) := by
  unfold addChar
  fun_prop

/-- **Orthogonality**: `∫_a^{a+1} e(θ n) dθ = 1_{n = 0}` for an integer `n`. -/
theorem integral_addChar_mul_intCast (a : ℝ) (n : ℤ) :
    ∫ θ in a..(a + 1), addChar (θ * (n : ℝ)) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    have h : (fun θ : ℝ => addChar (θ * ((0 : ℤ) : ℝ))) = fun _ : ℝ => (1 : ℂ) := by
      funext θ
      rw [Int.cast_zero, mul_zero, addChar_zero]
    rw [if_pos (rfl : (0 : ℤ) = 0), h, intervalIntegral.integral_const, add_sub_cancel_left,
      one_smul]
  · rw [if_neg hn]
    have hc : 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (Int.cast_ne_zero.mpr hn)) Complex.I_ne_zero
    have h : (fun θ : ℝ => addChar (θ * (n : ℝ))) =
        fun θ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I * (θ : ℂ)) := by
      funext θ
      unfold addChar
      congr 1
      push_cast
      ring
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I * (a : ℂ)) := by
      have e : 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I * ((a + 1 : ℝ) : ℂ) =
          2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I * (a : ℂ) +
            (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h, integral_exp_mul_complex hc, h1, sub_self, zero_div]

/-- Orthogonality on `[0, 1]`. -/
theorem integral_addChar_unit (n : ℤ) :
    ∫ θ in (0 : ℝ)..1, addChar (θ * (n : ℝ)) = if n = 0 then 1 else 0 := by
  have h := integral_addChar_mul_intCast 0 n
  rwa [zero_add] at h

/-! ### Trigonometric polynomials -/

/-- The trigonometric polynomial `â(θ) = ∑_{w ∈ s} a_w e(θ w)`. -/
def trigSum (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ := ∑ w ∈ s, c w * addChar (θ * (w : ℝ))

theorem continuous_trigSum (s : Finset ℕ) (c : ℕ → ℂ) : Continuous fun θ : ℝ => trigSum s c θ := by
  unfold trigSum
  exact continuous_finsetSum s fun w _ => continuous_const.mul (continuous_addChar_mul _)

theorem continuous_trigSum_neg (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous fun θ : ℝ => trigSum s c (-θ) :=
  (continuous_trigSum s c).comp continuous_neg

/-- Expansion of the square of a trigonometric polynomial. -/
theorem trigSum_mul_conj (s : Finset ℕ) (c : ℕ → ℂ) (θ : ℝ) :
    ((‖trigSum s c θ‖ ^ 2 : ℝ) : ℂ) =
      ∑ w ∈ s, ∑ v ∈ s, c w * conj (c v) * addChar (θ * (((w : ℤ) - (v : ℤ) : ℤ) : ℝ)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold trigSum
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
  have e : θ * (((w : ℤ) - (v : ℤ) : ℤ) : ℝ) = θ * (w : ℝ) + -(θ * (v : ℝ)) := by
    push_cast
    ring
  rw [map_mul, e, addChar_add, addChar_neg]
  ring

/-- **Parseval on a period**: `∫_a^{a+1} |∑_w c_w e(θ w)|² dθ = ∑_w |c_w|²`. -/
theorem integral_normSq_trigSum (s : Finset ℕ) (c : ℕ → ℂ) (a : ℝ) :
    ∫ θ in a..(a + 1), ‖trigSum s c θ‖ ^ 2 = ∑ w ∈ s, ‖c w‖ ^ 2 := by
  have hC : ((∫ θ in a..(a + 1), ‖trigSum s c θ‖ ^ 2 : ℝ) : ℂ) =
      ((∑ w ∈ s, ‖c w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [trigSum_mul_conj]
    rw [intervalIntegral.integral_finsetSum, Complex.ofReal_sum]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [intervalIntegral.integral_finsetSum]
      · have hterm : ∀ v ∈ s, ∫ θ in a..(a + 1),
              c w * conj (c v) * addChar (θ * (((w : ℤ) - (v : ℤ) : ℤ) : ℝ)) =
            if v = w then c v * conj (c v) else 0 := by
          intro v _
          rw [intervalIntegral.integral_const_mul, integral_addChar_mul_intCast]
          by_cases hvw : v = w
          · rw [if_pos hvw, hvw, sub_self, if_pos (rfl : (0 : ℤ) = 0), mul_one]
          · have h0 : ¬((w : ℤ) - (v : ℤ) = 0) := fun h => hvw (by omega)
            rw [if_neg hvw, if_neg h0, mul_zero]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s w fun v => c v * conj (c v),
          if_pos hw, Complex.mul_conj', Complex.ofReal_pow]
      · intro v _
        exact (continuous_const.mul (continuous_addChar_mul _)).intervalIntegrable _ _
    · intro w _
      exact (continuous_finsetSum s fun v _ =>
        continuous_const.mul (continuous_addChar_mul _)).intervalIntegrable _ _
  exact Complex.ofReal_injective hC

/-- Parseval on a period for the reflected polynomial `θ ↦ â(-θ)`. -/
theorem integral_normSq_trigSum_neg (s : Finset ℕ) (c : ℕ → ℂ) (a : ℝ) :
    ∫ θ in a..(a + 1), ‖trigSum s c (-θ)‖ ^ 2 = ∑ w ∈ s, ‖c w‖ ^ 2 := by
  have h : ∫ θ in a..(a + 1), ‖trigSum s c (-θ)‖ ^ 2 =
      ∫ θ in (-(a + 1))..(-a), ‖trigSum s c θ‖ ^ 2 :=
    intervalIntegral.integral_comp_neg (fun θ : ℝ => ‖trigSum s c θ‖ ^ 2)
  have h2 := integral_normSq_trigSum s c (-(a + 1))
  have e : -(a + 1) + 1 = -a := by ring
  rw [e] at h2
  rw [h, h2]

/-- The sum of the squares over a set that contains the support is the sum over `ℕ`. -/
theorem sum_normSq_eq_finsum {f : ℕ → ℂ} {s : Finset ℕ} (hf : ∀ w, f w ≠ 0 → w ∈ s) :
    ∑ w ∈ s, ‖f w‖ ^ 2 = ∑ᶠ w : ℕ, ‖f w‖ ^ 2 := by
  have hsub : Function.support (fun w : ℕ => ‖f w‖ ^ 2) ⊆ ↑s := by
    intro w hw
    rw [Function.mem_support] at hw
    refine Finset.mem_coe.mpr (hf w fun h' => hw ?_)
    rw [h', norm_zero]
    exact zero_pow two_ne_zero
  rw [finsum_eq_sum_of_support_subset _ hsub]

/-! ### The correlation of two sequences -/

/-- **The correlation on the circle**:
`∫_0^1 𝒰̂(θ) 𝒱̂(-θ) e(θ D) dθ = ∑_{w ∈ s, w + D ∈ t} 𝒰(w) 𝒱(w + D)`. -/
theorem integral_trigSum_mul_trigSum_neg (s t : Finset ℕ) (U V : ℕ → ℂ) (D : ℕ) :
    ∫ θ in (0 : ℝ)..1, trigSum s U θ * trigSum t V (-θ) * addChar (θ * (D : ℝ)) =
      ∑ w ∈ s, if w + D ∈ t then U w * V (w + D) else 0 := by
  have hexp : ∀ θ : ℝ, trigSum s U θ * trigSum t V (-θ) * addChar (θ * (D : ℝ)) =
      ∑ w ∈ s, ∑ v ∈ t,
        U w * V v * addChar (θ * (((w : ℤ) + (D : ℤ) - (v : ℤ) : ℤ) : ℝ)) := by
    intro θ
    unfold trigSum
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    have e : θ * (((w : ℤ) + (D : ℤ) - (v : ℤ) : ℤ) : ℝ) =
        θ * (w : ℝ) + (-θ * (v : ℝ) + θ * (D : ℝ)) := by
      push_cast
      ring
    rw [e, addChar_add, addChar_add]
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · have hterm : ∀ v ∈ t, ∫ θ in (0 : ℝ)..1,
            U w * V v * addChar (θ * (((w : ℤ) + (D : ℤ) - (v : ℤ) : ℤ) : ℝ)) =
          if w + D = v then U w * V v else 0 := by
        intro v _
        rw [intervalIntegral.integral_const_mul, integral_addChar_unit]
        by_cases hv : w + D = v
        · have h0 : (w : ℤ) + (D : ℤ) - (v : ℤ) = 0 := by omega
          rw [if_pos hv, if_pos h0, mul_one]
        · have h0 : ¬((w : ℤ) + (D : ℤ) - (v : ℤ) = 0) := fun h => hv (by omega)
          rw [if_neg hv, if_neg h0, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq t (w + D) fun v => U w * V v]
    · intro v _
      exact (continuous_const.mul (continuous_addChar_mul _)).intervalIntegrable _ _
  · intro w _
    exact (continuous_finsetSum t fun v _ =>
      continuous_const.mul (continuous_addChar_mul _)).intervalIntegrable _ _

/-- **The bilinear sum on the circle**: for sequences supported in `s` and `t`,
`∑_r c_r ∑_w 𝒰(w) 𝒱(w + D_r) = ∫_0^1 𝒰̂(θ) 𝒱̂(-θ) (∑_r c_r e(θ D_r)) dθ`. -/
theorem sum_mul_finsum_eq_integral {R : Type*} [Fintype R] (s t : Finset ℕ) {U V : ℕ → ℂ}
    (hU : ∀ w, U w ≠ 0 → w ∈ s) (hV : ∀ v, V v ≠ 0 → v ∈ t) (c : R → ℂ) (D : R → ℕ) :
    ∑ r, c r * ∑ᶠ w : ℕ, U w * V (w + D r) =
      ∫ θ in (0 : ℝ)..1, trigSum s U θ * trigSum t V (-θ) *
        ∑ r, c r * addChar (θ * (D r : ℝ)) := by
  have hfin : ∀ r, ∑ᶠ w : ℕ, U w * V (w + D r) =
      ∫ θ in (0 : ℝ)..1, trigSum s U θ * trigSum t V (-θ) * addChar (θ * (D r : ℝ)) := by
    intro r
    have hsub : Function.support (fun w : ℕ => U w * V (w + D r)) ⊆ ↑s := by
      intro w hw
      rw [Function.mem_support] at hw
      exact Finset.mem_coe.mpr (hU w fun h' => hw (by rw [h', zero_mul]))
    rw [finsum_eq_sum_of_support_subset _ hsub, integral_trigSum_mul_trigSum_neg]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hmem : w + D r ∈ t
    · rw [if_pos hmem]
    · have hV0 : V (w + D r) = 0 := by
        by_contra h'
        exact hmem (hV _ h')
      rw [if_neg hmem, hV0, mul_zero]
  have hfun : ∀ r, (fun θ : ℝ =>
        c r * (trigSum s U θ * trigSum t V (-θ) * addChar (θ * (D r : ℝ)))) =
      fun θ : ℝ => trigSum s U θ * trigSum t V (-θ) * (c r * addChar (θ * (D r : ℝ))) :=
    fun r => funext fun θ => by ring
  have hint : ∀ r, IntervalIntegrable (fun θ : ℝ =>
      trigSum s U θ * trigSum t V (-θ) * (c r * addChar (θ * (D r : ℝ)))) volume 0 1 := fun r =>
    (((continuous_trigSum s U).mul (continuous_trigSum_neg t V)).mul
      (continuous_const.mul (continuous_addChar_mul _))).intervalIntegrable _ _
  have hsum : (fun θ : ℝ =>
        ∑ r, trigSum s U θ * trigSum t V (-θ) * (c r * addChar (θ * (D r : ℝ)))) =
      fun θ : ℝ => trigSum s U θ * trigSum t V (-θ) * ∑ r, c r * addChar (θ * (D r : ℝ)) :=
    funext fun θ => by rw [Finset.mul_sum]
  calc ∑ r, c r * ∑ᶠ w : ℕ, U w * V (w + D r)
      = ∑ r, ∫ θ in (0 : ℝ)..1,
          trigSum s U θ * trigSum t V (-θ) * (c r * addChar (θ * (D r : ℝ))) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hfin r, ← intervalIntegral.integral_const_mul, hfun r]
    _ = ∫ θ in (0 : ℝ)..1,
          ∑ r, trigSum s U θ * trigSum t V (-θ) * (c r * addChar (θ * (D r : ℝ))) :=
        (intervalIntegral.integral_finsetSum fun r _ => hint r).symm
    _ = ∫ θ in (0 : ℝ)..1, trigSum s U θ * trigSum t V (-θ) *
          ∑ r, c r * addChar (θ * (D r : ℝ)) := by rw [hsum]

/-- The arc of a sequence twisted by `e(jw/H)` at the fraction `h/k` is the arc of the sequence at
`(hH + jk)/(kH)`. -/
theorem finsum_shifted_arc_eq {U : ℕ → ℂ} {s : Finset ℕ} (hUs : ∀ w, U w ≠ 0 → w ∈ s) {H k : ℕ}
    (hH : 0 < H) (hk : 0 < k) (j : ℕ) (h : ℤ) (β : ℝ) :
    ∑ᶠ w : ℕ, U w * addChar
        ((((h * (H : ℤ) + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) / ((k * H : ℕ) : ℝ) + β) * (w : ℝ)) =
      ∑ w ∈ s, U w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) *
        addChar (((h : ℝ) / (k : ℝ) + β) * (w : ℝ)) := by
  have hsub : Function.support (fun w : ℕ => U w * addChar
      ((((h * (H : ℤ) + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) / ((k * H : ℕ) : ℝ) + β) * (w : ℝ))) ⊆
      ↑s := by
    intro w hw
    rw [Function.mem_support] at hw
    exact Finset.mem_coe.mpr (hUs w fun h' => hw (by rw [h', zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hH0 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have e1 : ((h : ℝ) * (H : ℝ) + (j : ℝ) * (k : ℝ)) / ((k : ℝ) * (H : ℝ)) =
      (h : ℝ) / (k : ℝ) + (j : ℝ) / (H : ℝ) := by
    rw [div_add_div _ _ hk0 hH0]
    ring
  have e : (((h * (H : ℤ) + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) / ((k * H : ℕ) : ℝ) + β) * (w : ℝ) =
      (j : ℝ) * (w : ℝ) / (H : ℝ) + ((h : ℝ) / (k : ℝ) + β) * (w : ℝ) := by
    push_cast
    linear_combination (w : ℝ) * e1
  rw [e, addChar_add, mul_assoc]

/-! ### Integration over arcs -/

/-- **Integration over arcs**: if at every point of `[0, 1]` either `F ≤ G₀`, or the point lies in
one of the arcs `|θ - c_i| ≤ δ` and `F ≤ G₁` there, then
`∫_0^1 F ≤ ∫_0^1 G₀ + ∑_i ∫_{c_i - δ}^{c_i + δ} G₁`. -/
theorem integral_le_of_arcs {ι : Type*} (T : Finset ι) (c : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    {F G₀ G₁ : ℝ → ℝ} (hF : Continuous F) (hG₀ : Continuous G₀) (hG₁ : Continuous G₁)
    (hG₀0 : ∀ θ, 0 ≤ G₀ θ) (hG₁0 : ∀ θ, 0 ≤ G₁ θ)
    (h : ∀ θ ∈ Set.Icc (0 : ℝ) 1, F θ ≤ G₀ θ ∨ ∃ i ∈ T, |θ - c i| ≤ δ ∧ F θ ≤ G₁ θ) :
    ∫ θ in (0 : ℝ)..1, F θ ≤
      (∫ θ in (0 : ℝ)..1, G₀ θ) + ∑ i ∈ T, ∫ θ in (c i - δ)..(c i + δ), G₁ θ := by
  have hind0 : ∀ (i : ι) (θ : ℝ), 0 ≤ (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ :=
    fun i θ => Set.indicator_nonneg (fun θ' _ => hG₁0 θ') θ
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      F θ ≤ G₀ θ + ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ := by
    intro θ hθ
    have hsum0 : 0 ≤ ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ :=
      Finset.sum_nonneg fun i _ => hind0 i θ
    rcases h θ hθ with h0 | ⟨i, hi, hθi, hFi⟩
    · linarith
    · have hmem : θ ∈ Set.Icc (c i - δ) (c i + δ) := by
        obtain ⟨h1, h2⟩ := abs_le.mp hθi
        exact ⟨by linarith, by linarith⟩
      have h1 : (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ = G₁ θ :=
        Set.indicator_of_mem hmem G₁
      have h2 : (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ ≤
          ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ :=
        Finset.single_le_sum (f := fun i => (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ)
          (fun i _ => hind0 i θ) hi
      have h3 := hG₀0 θ
      linarith
  have hG₀I : IntegrableOn G₀ (Set.Ioc (0 : ℝ) 1) volume := hG₀.integrableOn_Ioc
  have hindI : ∀ i, IntegrableOn ((Set.Icc (c i - δ) (c i + δ)).indicator G₁)
      (Set.Ioc (0 : ℝ) 1) volume := fun i =>
    IntegrableOn.indicator hG₁.integrableOn_Ioc measurableSet_Icc
  have hsumI : IntegrableOn
      (fun θ => ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ) (Set.Ioc (0 : ℝ) 1)
      volume := integrable_finsetSum T fun i _ => hindI i
  have hrhsI : IntegrableOn
      (fun θ => G₀ θ + ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ)
      (Set.Ioc (0 : ℝ) 1) volume := Integrable.add hG₀I hsumI
  have harc : ∀ i, ∫ θ in Set.Ioc (0 : ℝ) 1, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ ≤
      ∫ θ in (c i - δ)..(c i + δ), G₁ θ := by
    intro i
    have hle : c i - δ ≤ c i + δ := by linarith
    rw [setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hle,
      ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_mono_set hG₁.integrableOn_Icc (ae_of_all _ fun θ => hG₁0 θ)
      (Filter.Eventually.of_forall Set.inter_subset_right)
  calc ∫ θ in (0 : ℝ)..1, F θ = ∫ θ in Set.Ioc (0 : ℝ) 1, F θ :=
        intervalIntegral.integral_of_le zero_le_one
    _ ≤ ∫ θ in Set.Ioc (0 : ℝ) 1,
          (G₀ θ + ∑ i ∈ T, (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ) :=
        setIntegral_mono_on hF.integrableOn_Ioc hrhsI measurableSet_Ioc
          fun θ hθ => hpt θ (Set.Ioc_subset_Icc_self hθ)
    _ = (∫ θ in Set.Ioc (0 : ℝ) 1, G₀ θ) +
          ∑ i ∈ T, ∫ θ in Set.Ioc (0 : ℝ) 1,
            (Set.Icc (c i - δ) (c i + δ)).indicator G₁ θ := by
        rw [integral_add hG₀I hsumI, integral_finsetSum T fun i _ => hindI i]
    _ ≤ (∫ θ in (0 : ℝ)..1, G₀ θ) + ∑ i ∈ T, ∫ θ in (c i - δ)..(c i + δ), G₁ θ := by
        rw [intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
        exact add_le_add le_rfl (Finset.sum_le_sum fun i _ => harc i)

/-- **The circle method**: if `|m| ≤ 1` everywhere and, on `[0, 1]`, `|m| ≤ ε` outside the arcs
`|θ - c_i| ≤ δ` (`2δ ≤ 1`), then for every `λ > 0`

`|∫_0^1 P Q m| ≤ ε (E_P + E_Q)/2 + #arcs · (λ E_A + λ⁻¹ E_Q)/2`,

where `E_P ≥ ∫_0^1 |P|²`, `E_Q` bounds the mean square of `Q` on every interval of length one and
`E_A` bounds the mean square of `P` on every arc. -/
theorem norm_integral_circle_le {ι : Type*} (T : Finset ι) (c : ι → ℝ)
    {δ ε lam EP EQ EA : ℝ} (hδ : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) (hε : 0 ≤ ε) (hlam : 0 < lam)
    {P Q m : ℝ → ℂ} (hP : Continuous P) (hQ : Continuous Q) (hm : Continuous m)
    (hm1 : ∀ θ, ‖m θ‖ ≤ 1)
    (harcs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖m θ‖ ≤ ε ∨ ∃ i ∈ T, |θ - c i| ≤ δ)
    (hEP : ∫ θ in (0 : ℝ)..1, ‖P θ‖ ^ 2 ≤ EP)
    (hEQ : ∀ a : ℝ, ∫ θ in a..(a + 1), ‖Q θ‖ ^ 2 ≤ EQ)
    (hEA : ∀ i ∈ T, ∫ θ in (c i - δ)..(c i + δ), ‖P θ‖ ^ 2 ≤ EA) :
    ‖∫ θ in (0 : ℝ)..1, P θ * Q θ * m θ‖ ≤
      ε * ((EP + EQ) / 2) + (T.card : ℝ) * ((lam * EA + lam⁻¹ * EQ) / 2) := by
  have hP2 : Continuous fun θ => ‖P θ‖ ^ 2 := hP.norm.pow 2
  have hQ2 : Continuous fun θ => ‖Q θ‖ ^ 2 := hQ.norm.pow 2
  have hF : Continuous fun θ => ‖P θ * Q θ * m θ‖ := ((hP.mul hQ).mul hm).norm
  have hG₀ : Continuous fun θ => ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2) :=
    continuous_const.mul ((hP2.add hQ2).div_const 2)
  have hG₁ : Continuous fun θ => (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 :=
    ((continuous_const.mul hP2).add (continuous_const.mul hQ2)).div_const 2
  have hlami : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hamgm : ∀ p q : ℝ, p * q ≤ (lam * p ^ 2 + lam⁻¹ * q ^ 2) / 2 := by
    intro p q
    have h1 : 0 ≤ lam⁻¹ * (lam * p - q) ^ 2 := mul_nonneg hlami.le (sq_nonneg _)
    have h3 : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
    have h2 : lam⁻¹ * (lam * p - q) ^ 2 = lam * p ^ 2 + lam⁻¹ * q ^ 2 - 2 * (p * q) := by
      linear_combination (lam * p ^ 2 - 2 * p * q) * h3
    linarith
  have hG₀0 : ∀ θ, 0 ≤ ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2) := fun θ =>
    mul_nonneg hε (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_two)
  have hG₁0 : ∀ θ, 0 ≤ (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 := fun θ =>
    div_nonneg (add_nonneg (mul_nonneg hlam.le (sq_nonneg _))
      (mul_nonneg hlami.le (sq_nonneg _))) zero_le_two
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖P θ * Q θ * m θ‖ ≤ ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2) ∨
        ∃ i ∈ T, |θ - c i| ≤ δ ∧
          ‖P θ * Q θ * m θ‖ ≤ (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 := by
    intro θ hθ
    have hnorm : ‖P θ * Q θ * m θ‖ = ‖P θ‖ * ‖Q θ‖ * ‖m θ‖ := by rw [norm_mul, norm_mul]
    have hpq : 0 ≤ ‖P θ‖ * ‖Q θ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rcases harcs θ hθ with h0 | ⟨i, hi, hθi⟩
    · left
      rw [hnorm]
      have h1 : ‖P θ‖ * ‖Q θ‖ ≤ (‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖P θ‖ - ‖Q θ‖)]
      calc ‖P θ‖ * ‖Q θ‖ * ‖m θ‖ ≤ ‖P θ‖ * ‖Q θ‖ * ε := mul_le_mul_of_nonneg_left h0 hpq
        _ = ε * (‖P θ‖ * ‖Q θ‖) := mul_comm _ _
        _ ≤ ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2) := mul_le_mul_of_nonneg_left h1 hε
    · right
      refine ⟨i, hi, hθi, ?_⟩
      rw [hnorm]
      calc ‖P θ‖ * ‖Q θ‖ * ‖m θ‖ ≤ ‖P θ‖ * ‖Q θ‖ * 1 :=
            mul_le_mul_of_nonneg_left (hm1 θ) hpq
        _ = ‖P θ‖ * ‖Q θ‖ := mul_one _
        _ ≤ (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 := hamgm _ _
  have hmain : ∫ θ in (0 : ℝ)..1, ‖P θ * Q θ * m θ‖ ≤
      (∫ θ in (0 : ℝ)..1, ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2)) +
        ∑ i ∈ T, ∫ θ in (c i - δ)..(c i + δ), (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 :=
    integral_le_of_arcs T c hδ hF hG₀ hG₁ hG₀0 hG₁0 hpt
  have hEQ0 : ∫ θ in (0 : ℝ)..1, ‖Q θ‖ ^ 2 ≤ EQ := by
    have h := hEQ 0
    rwa [zero_add] at h
  have hminor : ∫ θ in (0 : ℝ)..1, ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2) ≤
      ε * ((EP + EQ) / 2) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_add (hP2.intervalIntegrable _ _) (hQ2.intervalIntegrable _ _)]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (add_le_add hEP hEQ0) zero_le_two) hε
  have hmajor : ∀ i ∈ T,
      ∫ θ in (c i - δ)..(c i + δ), (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 ≤
        (lam * EA + lam⁻¹ * EQ) / 2 := by
    intro i hi
    have hQi1 : ∫ θ in (c i - δ)..(c i + δ), ‖Q θ‖ ^ 2 ≤
        ∫ θ in (c i - δ)..(c i - δ + 1), ‖Q θ‖ ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
        (ae_of_all _ fun θ => sq_nonneg ‖Q θ‖) (hQ2.intervalIntegrable _ _)
    have hQi : ∫ θ in (c i - δ)..(c i + δ), ‖Q θ‖ ^ 2 ≤ EQ := hQi1.trans (hEQ (c i - δ))
    have hI1 : IntervalIntegrable (fun θ => lam * ‖P θ‖ ^ 2) volume (c i - δ) (c i + δ) :=
      (continuous_const.mul hP2).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun θ => lam⁻¹ * ‖Q θ‖ ^ 2) volume (c i - δ) (c i + δ) :=
      (continuous_const.mul hQ2).intervalIntegrable _ _
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hI1 hI2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    exact div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (hEA i hi) hlam.le)
      (mul_le_mul_of_nonneg_left hQi hlami.le)) zero_le_two
  calc ‖∫ θ in (0 : ℝ)..1, P θ * Q θ * m θ‖
      ≤ ∫ θ in (0 : ℝ)..1, ‖P θ * Q θ * m θ‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ (∫ θ in (0 : ℝ)..1, ε * ((‖P θ‖ ^ 2 + ‖Q θ‖ ^ 2) / 2)) +
          ∑ i ∈ T, ∫ θ in (c i - δ)..(c i + δ),
            (lam * ‖P θ‖ ^ 2 + lam⁻¹ * ‖Q θ‖ ^ 2) / 2 := hmain
    _ ≤ ε * ((EP + EQ) / 2) + ∑ _i ∈ T, (lam * EA + lam⁻¹ * EQ) / 2 :=
        add_le_add hminor (Finset.sum_le_sum hmajor)
    _ = ε * ((EP + EQ) / 2) + (T.card : ℝ) * ((lam * EA + lam⁻¹ * EQ) / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The circle method for a twisted sequence -/

/-- **The circle method for the bilinear sum** with the first sequence twisted by `e(jw/H)`
(`[P-06:0476–0486]`, `[PUB-tex:0492–0500]`): if the multiplier `𝔪(θ) = ∑_r wt_r b_r e(θ D_r)` is
at most `ε` outside the arcs `|θ - h/k| ≤ δ`, `k ≤ Q`, and the untwisted first sequence has
energy at most `E_A` on every arc of radius `δ` with denominator at most `Q' ≥ QH`, then

`|∑_r wt_r b_r ∑_w 𝒰(w) e(jw/H) 𝒱(w + D_r)| ≤ ε (E_U + E_V)/2 + 4Q² (λ E_A + λ⁻¹ E_V)/2`. -/
theorem circle_core {R : Type*} [Fintype R] (wt : R → ℝ) (hwt0 : ∀ r, 0 ≤ wt r)
    (hwt1 : ∑ r, wt r ≤ 1) (b : R → ℂ) (hb : ∀ r, ‖b r‖ ≤ 1) (Dr : R → ℕ) (s : Finset ℕ)
    {Uc Vc : ℕ → ℂ} (hU : ∀ w, Uc w ≠ 0 → w ∈ s) (hV : ∀ v, Vc v ≠ 0 → v ∈ s) {H : ℕ}
    (hH : 0 < H) (j : ℕ) {EU EV EA Qr Qr' δ ε lam : ℝ}
    (hEU : ∑ᶠ w : ℕ, ‖Uc w‖ ^ 2 ≤ EU) (hEV : ∑ᶠ v : ℕ, ‖Vc v‖ ^ 2 ≤ EV) (hQ1 : 1 ≤ Qr)
    (hQH : Qr * (H : ℝ) ≤ Qr') (hδ : 0 ≤ δ) (hQδ : Qr * δ ≤ 1) (hδ1 : 2 * δ ≤ 1) (hε : 0 ≤ ε)
    (hlam : 0 < lam)
    (hdich : ∀ θ : ℝ,
      (∃ (k : ℕ) (h : ℤ), 0 < k ∧ (k : ℝ) ≤ Qr ∧ |θ - (h : ℝ) / (k : ℝ)| ≤ δ) ∨
        ‖∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ))‖ ≤ ε)
    (harc : ∀ (k : ℕ) (h : ℤ), 0 < k → (k : ℝ) ≤ Qr' →
      ∫ β in (-δ)..δ,
        ‖∑ᶠ w : ℕ, Uc w * addChar (((h : ℝ) / (k : ℝ) + β) * (w : ℝ))‖ ^ 2 ≤ EA) :
    ‖∑ r, ((wt r : ℝ) : ℂ) * b r *
        ∑ᶠ w : ℕ, Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) * Vc (w + Dr r)‖ ≤
      ε * ((EU + EV) / 2) + 4 * Qr ^ 2 * ((lam * EA + lam⁻¹ * EV) / 2) := by
  -- the twisted sequence and the bilinear sum on the circle
  have hU' : ∀ w, Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) ≠ 0 → w ∈ s := fun w hw =>
    hU w fun h' => hw (by rw [h', zero_mul])
  have key : ∑ r, ((wt r : ℝ) : ℂ) * b r *
        ∑ᶠ w : ℕ, Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) * Vc (w + Dr r) =
      ∫ θ in (0 : ℝ)..1,
        trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ *
          trigSum s Vc (-θ) * ∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ)) :=
    sum_mul_finsum_eq_integral s s hU' hV (fun r => ((wt r : ℝ) : ℂ) * b r) Dr
  rw [key]
  -- the energies
  have hEU' : ∑ w ∈ s, ‖Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))‖ ^ 2 ≤ EU := by
    have e : ∑ w ∈ s, ‖Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))‖ ^ 2 =
        ∑ w ∈ s, ‖Uc w‖ ^ 2 :=
      Finset.sum_congr rfl fun w _ => by rw [norm_mul, EndpointProof.norm_addChar, mul_one]
    rw [e, sum_normSq_eq_finsum hU]
    exact hEU
  have hEV' : ∑ v ∈ s, ‖Vc v‖ ^ 2 ≤ EV := by
    rw [sum_normSq_eq_finsum hV]
    exact hEV
  have hEV0 : 0 ≤ EV := (Finset.sum_nonneg fun v _ => sq_nonneg ‖Vc v‖).trans hEV'
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := Nat.one_le_cast.mpr hH
  have hEA0 : 0 ≤ EA := by
    have h1 := harc 1 0 one_pos (by
      rw [Nat.cast_one]
      exact (one_le_mul_of_one_le_of_one_le hQ1 hH1).trans hQH)
    have h0 : 0 ≤ ∫ β in (-δ)..δ, ‖∑ᶠ w : ℕ, Uc w * addChar
        ((((0 : ℤ) : ℝ) / ((1 : ℕ) : ℝ) + β) * (w : ℝ))‖ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun β _ => sq_nonneg _
    exact h0.trans h1
  have hEP : ∫ θ in (0 : ℝ)..1,
      ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ‖ ^ 2 ≤ EU := by
    have h := integral_normSq_trigSum s
      (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) 0
    rw [zero_add] at h
    rw [h]
    exact hEU'
  have hEQ : ∀ a : ℝ, ∫ θ in a..(a + 1), ‖trigSum s Vc (-θ)‖ ^ 2 ≤ EV := fun a => by
    rw [integral_normSq_trigSum_neg s Vc a]
    exact hEV'
  -- the arcs
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊Qr⌋₊ := ⟨_, rfl⟩
  have hQr0 : 0 ≤ Qr := by linarith
  have hnQ : (n : ℝ) ≤ Qr := by
    rw [hn]
    exact Nat.floor_le hQr0
  have hm1 : ∀ θ : ℝ, ‖∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ))‖ ≤ 1 := by
    intro θ
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun r _ => ?_) hwt1)
    rw [norm_mul, norm_mul, EndpointProof.norm_addChar, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hwt0 r)]
    exact mul_le_of_le_one_right (hwt0 r) (hb r)
  have hmc : Continuous fun θ : ℝ => ∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ)) :=
    continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_addChar_mul _)
  have harcs : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ))‖ ≤ ε ∨
        ∃ i ∈ Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1),
          |θ - (i.2 : ℝ) / (i.1 : ℝ)| ≤ δ := by
    intro θ hθ
    rcases hdich θ with ⟨k, h, hk, hkQ, hθk⟩ | hsmall
    · right
      have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      obtain ⟨h1, h2⟩ := abs_le.mp hθk
      have hkδ : (k : ℝ) * δ ≤ 1 := (mul_le_mul_of_nonneg_right hkQ hδ).trans hQδ
      have hq : (h : ℝ) / (k : ℝ) * (k : ℝ) = (h : ℝ) := div_mul_cancel₀ _ hk0.ne'
      have hup : (h : ℝ) ≤ (k : ℝ) + 1 := by
        have h3 : (h : ℝ) / (k : ℝ) ≤ θ + δ := by linarith
        have h4 := mul_le_mul_of_nonneg_right h3 hk0.le
        rw [hq] at h4
        have h5 : θ * (k : ℝ) ≤ (k : ℝ) := mul_le_of_le_one_left hk0.le hθ.2
        have h6 : (θ + δ) * (k : ℝ) = θ * (k : ℝ) + (k : ℝ) * δ := by ring
        linarith
      have hlow : (-1 : ℝ) ≤ (h : ℝ) := by
        have h3 : θ - δ ≤ (h : ℝ) / (k : ℝ) := by linarith
        have h4 := mul_le_mul_of_nonneg_right h3 hk0.le
        rw [hq] at h4
        have h5 : 0 ≤ θ * (k : ℝ) := mul_nonneg hθ.1 hk0.le
        have h6 : (θ - δ) * (k : ℝ) = θ * (k : ℝ) - (k : ℝ) * δ := by ring
        linarith
      have hkn : k ≤ n := by
        rw [hn]
        exact Nat.le_floor hkQ
      have hlowZ : (-1 : ℤ) ≤ h := by exact_mod_cast hlow
      have hupZ : h ≤ (k : ℤ) + 1 := by exact_mod_cast hup
      have hknZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
      exact ⟨(k, h), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hkn⟩,
        Finset.mem_Icc.mpr ⟨hlowZ, by linarith⟩⟩, hθk⟩
    · left
      exact hsmall
  have hEA' : ∀ i ∈ Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1),
      ∫ θ in ((i.2 : ℝ) / (i.1 : ℝ) - δ)..((i.2 : ℝ) / (i.1 : ℝ) + δ),
        ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ‖ ^ 2 ≤ EA := by
    intro i hi
    obtain ⟨hi1, -⟩ := Finset.mem_product.mp hi
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hi1
    have hk : 0 < i.1 := hk1
    have hkQ : (i.1 : ℝ) ≤ Qr := (Nat.cast_le.mpr hkn).trans hnQ
    have hkH : ((i.1 * H : ℕ) : ℝ) ≤ Qr' := by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_right hkQ (Nat.cast_nonneg H)).trans hQH
    have h1 := harc (i.1 * H) (i.2 * (H : ℤ) + (j : ℤ) * (i.1 : ℤ)) (Nat.mul_pos hk hH) hkH
    have hfun : (fun β : ℝ => ‖∑ᶠ w : ℕ, Uc w * addChar
          ((((i.2 * (H : ℤ) + (j : ℤ) * (i.1 : ℤ) : ℤ) : ℝ) / ((i.1 * H : ℕ) : ℝ) + β) *
            (w : ℝ))‖ ^ 2) =
        fun β : ℝ => ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
          ((i.2 : ℝ) / (i.1 : ℝ) + β)‖ ^ 2 :=
      funext fun β => by
        rw [finsum_shifted_arc_eq hU hH hk j i.2 β]
        rfl
    rw [hfun] at h1
    have h2 : ∫ β in (-δ)..δ,
          ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
            ((i.2 : ℝ) / (i.1 : ℝ) + β)‖ ^ 2 =
        ∫ θ in ((i.2 : ℝ) / (i.1 : ℝ) + -δ)..((i.2 : ℝ) / (i.1 : ℝ) + δ),
          ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ‖ ^ 2 :=
      intervalIntegral.integral_comp_add_left
        (fun θ : ℝ => ‖trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ‖ ^ 2)
        ((i.2 : ℝ) / (i.1 : ℝ))
    rw [h2, ← sub_eq_add_neg] at h1
    exact h1
  -- the number of arcs
  have hcard : (Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1)).card = n * (n + 3) := by
    have e2 : ((n : ℤ) + 1 + 1 - -1).toNat = n + 3 := by omega
    rw [Finset.card_product, Nat.card_Icc, Int.card_Icc, e2, Nat.add_sub_cancel]
  have hcardR : ((Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1)).card : ℝ) ≤
      4 * Qr ^ 2 := by
    rw [hcard]
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (n : ℝ) * ((n : ℝ) + 3) ≤ Qr * (Qr + 3) :=
      mul_le_mul hnQ (by linarith) (by linarith) hQr0
    nlinarith [mul_nonneg hQr0 (sub_nonneg.mpr hQ1)]
  have hX0 : 0 ≤ (lam * EA + lam⁻¹ * EV) / 2 :=
    div_nonneg (add_nonneg (mul_nonneg hlam.le hEA0)
      (mul_nonneg (inv_pos.mpr hlam).le hEV0)) zero_le_two
  have hcirc : ‖∫ θ in (0 : ℝ)..1,
        trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))) θ *
          trigSum s Vc (-θ) * ∑ r, ((wt r : ℝ) : ℂ) * b r * addChar (θ * (Dr r : ℝ))‖ ≤
      ε * ((EU + EV) / 2) +
        ((Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1)).card : ℝ) *
          ((lam * EA + lam⁻¹ * EV) / 2) :=
    norm_integral_circle_le (Finset.Icc 1 n ×ˢ Finset.Icc (-1 : ℤ) ((n : ℤ) + 1))
      (fun p : ℕ × ℤ => (p.2 : ℝ) / (p.1 : ℝ)) hδ hδ1 hε hlam
      (continuous_trigSum s (fun w => Uc w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ))))
      (continuous_trigSum_neg s Vc) hmc hm1 harcs hEP hEQ hEA'
  exact hcirc.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcardR hX0))

/-- The powers of `L` in the circle method: the minor arcs with the saving `A + C₅`, and the
`4 L^{2C₆}` major arcs with the arc energy at the precision `2A + 4C₆ + C₅` and
`λ = L^{A + 2C₆ + C₅}`. -/
theorem circle_final {L A C₅ C₆ MA Y : ℝ} (hL : 0 < L) :
    L ^ (-(A + C₅)) * ((Y * L ^ C₅ + Y * L ^ C₅) / 2) +
        4 * (L ^ C₆) ^ 2 *
          ((L ^ (A + 2 * C₆ + C₅) * (MA * Y * L ^ (-(2 * A + 4 * C₆ + C₅))) +
            (L ^ (A + 2 * C₆ + C₅))⁻¹ * (Y * L ^ C₅)) / 2) =
      (2 * MA + 3) * Y * L ^ (-A) := by
  have h1 : L ^ (-(A + C₅)) * L ^ C₅ = L ^ (-A) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have h2 : (L ^ C₆) ^ 2 * (L ^ (A + 2 * C₆ + C₅) * L ^ (-(2 * A + 4 * C₆ + C₅))) =
      L ^ (-A) := by
    rw [sq, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  have h3 : (L ^ C₆) ^ 2 * ((L ^ (A + 2 * C₆ + C₅))⁻¹ * L ^ C₅) = L ^ (-A) := by
    rw [sq, ← Real.rpow_neg hL.le, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  linear_combination Y * h1 + 2 * MA * Y * h2 + 2 * Y * h3

end CircleMethod

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

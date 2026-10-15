module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.LocalMellinCompare

/-!
# The lemma (local Mellin energy)

`localMellin : LocalMellin` (`[P-06:0488–0528]`): for `j ≥ 2`, `0 < a₁ ≤ a₂` there is `C` with

`∫_{|β| ≤ 1/H} |∑_w a_w e(βw)|² dβ ≤
  C (Y⁻¹ ∫ (1 + H|t|/Y)^{-j} |∑_w a_w w^{it}|² dt + (H/Y)² ∑_w |a_w|²)`

for all `1 ≤ H ≤ Y` and all coefficients supported on `[a₁Y, a₂Y]`.

The manuscript's proof with "a smooth bump `K` … supported close enough to zero that its additive
Fourier transform has modulus at least `1/2` on `[-1,1]`" is carried out with the Gaussian
`K(x) = e^{-x²}`, for which the two uses of Plancherel are identities between finite quadratic
forms (`LocalMellinAux.gauss_bridge`):

1. `arc_le_gauss` ("Plancherel gives …"): `1_{|β| ≤ 1/H} ≤ e^{2π²} e^{-2π²H²β²}`, hence
   `∫_{|β| ≤ 1/H} |â|² ≤ (e^{2π²}/(πH²)) ∫ |∑_w a_w e^{-(w-v)²/H²}|² dv`.
2. `additive_le` ("Only `v ≍ Y` contributes. … replace `K((w-v)/H)` by `K(v log(w/v)/H)` …
   normalized squared error `O((H/Y)² ∑|a_w|²)`"): the windows are replaced for
   `v ∈ [a₁Y/2, 2a₂Y]` (`LocalMellinAux.window_in`, `window_out`), the error being bounded by the
   Cauchy step and a Gaussian sum over the integers.
3. `LocalMellinAux.integral_cmpWin_le` ("Write `v = Y e^u` …"): the logarithmic windows of the
   varying width `(v/H)²` are Gaussian averages of windows of a fixed width `γ₀`.
4. `mellin_le` and `gauss_bridge` ("Fourier inversion for the new kernel"): the mean square of the
   windows of width `γ₀ = 1/(2c)` is `c ∫ e^{-ct²} |∑_w a_w w^{it}|² dt`, `c = (H/Y)²/(16a₂²)`,
   and `e^{-ct²} ≤ e^{4a₂²j²} (1 + H|t|/Y)^{-j}`. "The outside normalization is
   `H⁻² Y h₀² = Y⁻¹`."
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory

noncomputable section

namespace LocalMellinAux

/-! ### Scalar identities -/

theorem le_gauss_mul {E G q : ℝ} (hq : 0 ≤ q) (h : 1 ≤ E * G) : q ≤ E * (G * q) := by
  have h' := mul_le_mul_of_nonneg_right h hq
  rw [one_mul, mul_assoc] at h'
  exact h'

theorem add_mul_le_mul_add {A K x z : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    A * x + K * z ≤ (A + K) * (x + z) := by
  nlinarith [mul_nonneg hA hz, mul_nonneg hK hx]

theorem const_cancel {c κ hi W : ℝ} (hc : c ≠ 0) :
    2 * (1 / (2 * c)) / κ * hi * (c * W) = hi / κ * W := by
  have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination (hi * κ⁻¹ * W) * hci

theorem div_sq_mul_cancel {E H B : ℝ} (hH : H ≠ 0) :
    E / (Real.pi * H ^ 2) * (H ^ 2 * B) = E / Real.pi * B := by
  have hHi : H * H⁻¹ = 1 := mul_inv_cancel₀ hH
  linear_combination (E * Real.pi⁻¹ * B * (H * H⁻¹ + 1)) * hHi

/-! ### Step 1: the arc against additive Gaussian windows -/

/-- **Plancherel for the Gaussian majorant of the arc `|β| ≤ 1/H`.** -/
theorem arc_le_gauss (s : Finset ℕ) (a : ℕ → ℂ) {H : ℝ} (hH : 0 < H) :
    ∫ β in (-(1 / H))..(1 / H), ‖∑ w ∈ s, a w * addChar (β * (w : ℝ))‖ ^ 2 ≤
      Real.exp (2 * Real.pi ^ 2) / (Real.pi * H ^ 2) *
        ∫ v : ℝ, ‖∑ w ∈ s, a w *
          ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 := by
  have hc : 0 < 2 * Real.pi ^ 2 * H ^ 2 := by positivity
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hππ : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have hchar : ∀ (β : ℝ) (w : ℕ),
      addChar (β * (w : ℝ)) = Separation.phase β (2 * Real.pi * (w : ℝ)) := by
    intro β w
    unfold addChar Separation.phase
    congr 1
    push_cast
    ring
  have hfun : (fun β : ℝ => ‖∑ w ∈ s, a w * addChar (β * (w : ℝ))‖ ^ 2) =
      fun β : ℝ => ‖∑ w ∈ s, a w * Separation.phase β (2 * Real.pi * (w : ℝ))‖ ^ 2 := by
    funext β
    simp only [hchar]
  obtain ⟨hint, -⟩ := integral_gauss_expSum s a (fun w : ℕ => 2 * Real.pi * (w : ℝ)) hc
  have hbridge := gauss_bridge s a (fun w : ℕ => 2 * Real.pi * (w : ℝ)) hc
  have hcont : Continuous fun β : ℝ =>
      ‖∑ w ∈ s, a w * Separation.phase β (2 * Real.pi * (w : ℝ))‖ ^ 2 :=
    ((continuous_finsetSum _ fun w _ =>
      continuous_const.mul (Separation.continuous_phase _)).norm).pow 2
  have hle : -(1 / H) ≤ 1 / H := by
    have h := one_div_pos.mpr hH
    linarith
  -- the Gaussian majorant of the arc
  have hstep1 : ∫ β in (-(1 / H))..(1 / H),
        ‖∑ w ∈ s, a w * Separation.phase β (2 * Real.pi * (w : ℝ))‖ ^ 2 ≤
      ∫ β : ℝ, Real.exp (2 * Real.pi ^ 2) * (Real.exp (-(2 * Real.pi ^ 2 * H ^ 2) * β ^ 2) *
        ‖∑ w ∈ s, a w * Separation.phase β (2 * Real.pi * (w : ℝ))‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hle]
    refine (setIntegral_mono_on hcont.integrableOn_Ioc (hint.const_mul _).integrableOn
      measurableSet_Ioc fun β hβ => ?_).trans
      (setIntegral_le_integral (hint.const_mul _) (ae_of_all _ fun β =>
        mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))))
    have h1 : H * β ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hβ.2 hH.le
      rwa [mul_one_div_cancel hH.ne'] at h
    have h2 : -1 ≤ H * β := by
      have h := mul_le_mul_of_nonneg_left hβ.1.le hH.le
      rwa [mul_neg, mul_one_div_cancel hH.ne'] at h
    have h3 : (H * β) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 1 + H * β)]
    have h4 : 2 * Real.pi ^ 2 * H ^ 2 * β ^ 2 ≤ 2 * Real.pi ^ 2 := by
      have h := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2)
      nlinarith
    have h5 : 1 ≤ Real.exp (2 * Real.pi ^ 2) *
        Real.exp (-(2 * Real.pi ^ 2 * H ^ 2) * β ^ 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    exact le_gauss_mul (sq_nonneg _) h5
  -- the scaling `y = 2πv`
  have hexp : ∀ (x : ℝ) (w : ℕ), -(1 / (2 * (2 * Real.pi ^ 2 * H ^ 2))) *
        (2 * Real.pi * (w : ℝ) - 2 * Real.pi * x) ^ 2 = -(1 / H ^ 2) * ((w : ℝ) - x) ^ 2 := by
    intro x w
    linear_combination
      (-(H⁻¹ ^ 2) * ((w : ℝ) - x) ^ 2 * (Real.pi * Real.pi⁻¹ + 1)) * hππ
  have hscale : ∫ y : ℝ, ‖∑ w ∈ s, a w *
        ((Real.exp (-(1 / (2 * (2 * Real.pi ^ 2 * H ^ 2))) *
          (2 * Real.pi * (w : ℝ) - y) ^ 2) : ℝ) : ℂ)‖ ^ 2 =
      2 * Real.pi * ∫ v : ℝ, ‖∑ w ∈ s, a w *
        ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => ‖∑ w ∈ s, a w * ((Real.exp (-(1 / (2 * (2 * Real.pi ^ 2 * H ^ 2))) *
        (2 * Real.pi * (w : ℝ) - y) ^ 2) : ℝ) : ℂ)‖ ^ 2) (2 * Real.pi)
    rw [abs_of_pos (inv_pos.mpr h2π), smul_eq_mul] at h
    simp only [hexp] at h
    rw [h, mul_inv_cancel_left₀ h2π.ne']
  rw [hfun]
  refine hstep1.trans (le_of_eq ?_)
  rw [integral_const_mul, hbridge, hscale]
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∫ v : ℝ, ‖∑ w ∈ s, a w *
      ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hJ]
  linear_combination (Real.exp (2 * Real.pi ^ 2) * H⁻¹ ^ 2 * J * Real.pi⁻¹) * hππ

/-! ### Step 2: additive windows against logarithmic windows -/

/-- On the relevant centres the two window sums differ by `O(H/Y)` times a wider Gaussian sum. -/
theorem norm_sub_cmpWin_le (s : Finset ℕ) (a : ℕ → ℂ) {a₁ a₂ H Y v : ℝ} (ha₁ : 0 < a₁)
    (ha₁₂ : a₁ ≤ a₂) (hH : 0 < H) (hY : 0 < Y)
    (hs : ∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y)
    (hv : a₁ * Y / 2 ≤ v ∧ v ≤ 2 * a₂ * Y) :
    ‖(∑ w ∈ s, a w * ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)) -
        cmpWin s a H (Real.log v)‖ ≤
      winConst a₁ a₂ * (H / Y) * ∑ w ∈ s, ‖a w‖ *
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv.1
  have hcmp : cmpWin s a H (Real.log v) = ∑ w ∈ s, a w *
      ((Real.exp (-(v / H) ^ 2 * (Real.log (w : ℝ) - Real.log v) ^ 2) : ℝ) : ℂ) := by
    unfold cmpWin logWin
    rw [Real.exp_log hv0]
  rw [hcmp, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := window_in ha₁ ha₁₂ hH hY (hs w hw) hv
  calc ‖a w‖ * |Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) -
          Real.exp (-(v / H) ^ 2 * (Real.log (w : ℝ) - Real.log v) ^ 2)|
      ≤ ‖a w‖ * (winConst a₁ a₂ * (H / Y) *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = winConst a₁ a₂ * (H / Y) * (‖a w‖ *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) := by ring

/-- Away from the relevant centres the additive window sum is that small. -/
theorem norm_addWin_le_out (s : Finset ℕ) (a : ℕ → ℂ) {a₁ a₂ H Y v : ℝ} (ha₁ : 0 < a₁)
    (ha₁₂ : a₁ ≤ a₂) (hH : 0 < H) (hY : 0 < Y)
    (hs : ∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y)
    (hv : v < a₁ * Y / 2 ∨ 2 * a₂ * Y < v) :
    ‖∑ w ∈ s, a w * ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ≤
      winConst a₁ a₂ * (H / Y) * ∑ w ∈ s, ‖a w‖ *
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := window_out ha₁ ha₁₂ hH hY (hs w hw) hv
  calc ‖a w‖ * Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2)
      ≤ ‖a w‖ * (winConst a₁ a₂ * (H / Y) *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = winConst a₁ a₂ * (H / Y) * (‖a w‖ *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) := by ring

/-- The pointwise comparison for every centre `v`. -/
theorem normSq_addWin_le (s : Finset ℕ) (a : ℕ → ℂ) {a₁ a₂ H Y : ℝ} (ha₁ : 0 < a₁)
    (ha₁₂ : a₁ ≤ a₂) (hH : 0 < H) (hY : 0 < Y)
    (hs : ∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y) (v : ℝ) :
    ‖∑ w ∈ s, a w * ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 ≤
      2 * (Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)).indicator
          (fun v : ℝ => ‖cmpWin s a H (Real.log v)‖ ^ 2) v +
        2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (∑ w ∈ s, ‖a w‖ *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) ^ 2 := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = winConst a₁ a₂ * (H / Y) * ∑ w ∈ s, ‖a w‖ *
      Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) := ⟨_, rfl⟩
  have hm2 : 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (∑ w ∈ s, ‖a w‖ *
      Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) ^ 2 =
      2 * m ^ 2 := by
    rw [hm]
    ring
  rw [hm2]
  by_cases hv : v ∈ Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)
  · rw [Set.indicator_of_mem hv]
    have h1 := norm_sub_cmpWin_le s a ha₁ ha₁₂ hH hY hs ⟨hv.1, hv.2⟩
    rw [← hm] at h1
    have h2 := (norm_le_norm_add_norm_sub' _ _).trans (add_le_add le_rfl h1)
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    show _ ≤ 2 * ‖cmpWin s a H (Real.log v)‖ ^ 2 + 2 * m ^ 2
    nlinarith [sq_nonneg (‖cmpWin s a H (Real.log v)‖ - m)]
  · rw [Set.indicator_of_notMem hv, mul_zero, zero_add]
    have hv' : v < a₁ * Y / 2 ∨ 2 * a₂ * Y < v := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
      exact hv
    have h1 := norm_addWin_le_out s a ha₁ ha₁₂ hH hY hs hv'
    rw [← hm] at h1
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg m]

/-- **Replacement of the additive windows by the logarithmic ones**, with the normalized squared
error `O((H/Y)² ∑|a_w|²)`. -/
theorem additive_le {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H Y : ℝ, 1 ≤ H → H ≤ Y → ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      (∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y) →
      ∫ v : ℝ, ‖∑ w ∈ s, a w *
          ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 ≤
        2 * (∫ v in (a₁ * Y / 2)..(2 * a₂ * Y), ‖cmpWin s a H (Real.log v)‖ ^ 2) +
          K * ((H / Y) ^ 2 * H ^ 2) * ∑ w ∈ s, ‖a w‖ ^ 2 := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  have hρ : 1 ≤ 2 * a₂ / a₁ := one_le_ratio ha₁ ha₁₂
  refine ⟨24 * Real.exp 1 * (2 * a₂ / a₁) ^ 2 * winConst a₁ a₂ ^ 2, by positivity, ?_⟩
  intro H Y hH hHY s a hs
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH
  have hY : 0 < Y := lt_of_lt_of_le hH0 hHY
  have hlo : 0 < a₁ * Y / 2 := by positivity
  have hlohi : a₁ * Y / 2 ≤ 2 * a₂ * Y := by
    have h := mul_le_mul_of_nonneg_right ha₁₂ hY.le
    have h' := mul_pos ha₁ hY
    linarith
  have hg₁ : 0 < 1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2) := by positivity
  have hρH : 0 ≤ (2 * a₂ / a₁) ^ 2 * H ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hπ4 := mul_le_mul_of_nonneg_right Real.pi_le_four hρH
  -- the Gaussian sum over the `O(H)` available `w`
  have hsum : ∀ v : ℝ, ∑ w ∈ s,
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) ≤
      Real.exp 1 * (4 * (2 * a₂ / a₁) * H) := by
    intro v
    have h := gauss_sum_le s hg₁ (mul_le_mul_of_nonneg_right ha₁₂ hY.le) hs v
    refine h.trans (mul_le_mul (Real.exp_le_exp.mpr ?_) ?_ (Real.sqrt_nonneg _)
      (Real.exp_pos _).le)
    · have hZ : (1 : ℝ) ≤ 2 * (2 * a₂ / a₁) ^ 2 * H ^ 2 := by
        have h' := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hρ (n := 2))
          (one_le_pow₀ hH (n := 2))
        linarith
      have hg1 : 1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2) ≤ 1 :=
        (div_le_one (by positivity)).mpr hZ
      linarith
    · have e : Real.pi / (1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2) / 2) =
          Real.pi * 2 * (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2) := by
        rw [div_div_eq_mul_div, div_div_eq_mul_div, div_one]
      rw [e]
      calc Real.sqrt (Real.pi * 2 * (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2))
          ≤ Real.sqrt ((4 * (2 * a₂ / a₁) * H) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 4 * (2 * a₂ / a₁) * H := Real.sqrt_sq (by positivity)
  -- the integral over the `O(H)` centres for each `w`
  have hgint : Real.sqrt (Real.pi / (1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2))) ≤
      3 * (2 * a₂ / a₁) * H := by
    have e : Real.pi / (1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) =
        Real.pi * (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2) := by
      rw [div_div_eq_mul_div, div_one]
    rw [e]
    calc Real.sqrt (Real.pi * (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2))
        ≤ Real.sqrt ((3 * (2 * a₂ / a₁) * H) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 3 * (2 * a₂ / a₁) * H := Real.sqrt_sq (by positivity)
  -- the pointwise bound: Cauchy over the available `w`
  have hpt : ∀ v : ℝ, ‖∑ w ∈ s, a w *
        ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 ≤
      2 * (Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)).indicator
          (fun v : ℝ => ‖cmpWin s a H (Real.log v)‖ ^ 2) v +
        2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
          ∑ w ∈ s, ‖a w‖ ^ 2 *
            Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) := by
    intro v
    have h1 := normSq_addWin_le s a ha₁ ha₁₂ hH0 hY hs v
    have h2 := sq_sum_mul_le s (fun w => ‖a w‖)
      (fun w => Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2))
      (fun w _ => (Real.exp_pos _).le)
    have h3 : 0 ≤ ∑ w ∈ s, ‖a w‖ ^ 2 *
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) :=
      Finset.sum_nonneg fun w _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have h4 := h2.trans (mul_le_mul_of_nonneg_left (hsum v) h3)
    have h5 : 0 ≤ 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_left h4 h5
    have e : 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * ((∑ w ∈ s, ‖a w‖ ^ 2 *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) *
          (Real.exp 1 * (4 * (2 * a₂ / a₁) * H))) =
        2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
          ∑ w ∈ s, ‖a w‖ ^ 2 *
            Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) := by ring
    rw [e] at h6
    exact h1.trans (add_le_add le_rfl h6)
  -- integrability
  have hg0 : 0 < 1 / H ^ 2 := by positivity
  have hSint := (integral_gauss_windowSum s a (fun w : ℕ => (w : ℝ)) hg0).1
  have hgc : Continuous fun y : ℝ => ‖cmpWin s a H y‖ ^ 2 :=
    (continuous_cmpWin s a H).norm.pow 2
  have hFon : IntegrableOn (fun v : ℝ => ‖cmpWin s a H (Real.log v)‖ ^ 2)
      (Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)) :=
    (hgc.comp_continuousOn (Real.continuousOn_log.mono fun v hv =>
      Set.mem_compl_singleton_iff.mpr (lt_of_lt_of_le hlo hv.1).ne')).integrableOn_Icc
  have h₁ : Integrable (fun v : ℝ => 2 * (Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)).indicator
      (fun v : ℝ => ‖cmpWin s a H (Real.log v)‖ ^ 2) v) :=
    (hFon.integrable_indicator measurableSet_Icc).const_mul 2
  have h₂ : Integrable (fun v : ℝ =>
      2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
        ∑ w ∈ s, ‖a w‖ ^ 2 *
          Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2)) :=
    (integrable_finsetSum s fun w _ =>
      (integrable_gauss hg₁ (w : ℝ)).const_mul (‖a w‖ ^ 2)).const_mul _
  -- the two integrals
  have hI₁ : ∫ v : ℝ, 2 * (Set.Icc (a₁ * Y / 2) (2 * a₂ * Y)).indicator
        (fun v : ℝ => ‖cmpWin s a H (Real.log v)‖ ^ 2) v =
      2 * ∫ v in (a₁ * Y / 2)..(2 * a₂ * Y), ‖cmpWin s a H (Real.log v)‖ ^ 2 := by
    rw [integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hlohi]
  have hI₂ : ∫ v : ℝ,
        2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
          ∑ w ∈ s, ‖a w‖ ^ 2 *
            Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * ((w : ℝ) - v) ^ 2) =
      2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
        ∑ w ∈ s, ‖a w‖ ^ 2 *
          Real.sqrt (Real.pi / (1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2))) := by
    rw [integral_const_mul, integral_finsetSum s fun w _ =>
      (integrable_gauss hg₁ (w : ℝ)).const_mul (‖a w‖ ^ 2)]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_const_mul, integral_gauss]
  have hsplit := (integral_add' h₁ h₂).trans (congrArg₂ (· + ·) hI₁ hI₂)
  refine ((integral_mono hSint (h₁.add h₂) hpt).trans (le_of_eq hsplit)).trans
    (add_le_add le_rfl ?_)
  -- the constant
  rw [← Finset.sum_mul]
  have hSg0 : 0 ≤ ∑ w ∈ s, ‖a w‖ ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hKc : 0 ≤ 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 *
      (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) := by positivity
  calc 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
        ((∑ w ∈ s, ‖a w‖ ^ 2) *
          Real.sqrt (Real.pi / (1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2))))
      ≤ 2 * (winConst a₁ a₂ * (H / Y)) ^ 2 * (Real.exp 1 * (4 * (2 * a₂ / a₁) * H)) *
          ((∑ w ∈ s, ‖a w‖ ^ 2) * (3 * (2 * a₂ / a₁) * H)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgint hSg0) hKc
    _ = 24 * Real.exp 1 * (2 * a₂ / a₁) ^ 2 * winConst a₁ a₂ ^ 2 * ((H / Y) ^ 2 * H ^ 2) *
          ∑ w ∈ s, ‖a w‖ ^ 2 := by ring

/-! ### Step 4: the Mellin side -/

/-- The Gaussian weight against the weight `(1 + H|t|/Y)^{-j}`, `j ≥ 2`; the weighted mean square
of the Dirichlet polynomial is finite. -/
theorem mellin_le (s : Finset ℕ) (a : ℕ → ℂ) {a₂ H Y : ℝ} (ha₂ : 0 < a₂) (hH : 0 < H)
    (hY : 0 < Y) {j : ℕ} (hj : 2 ≤ j) :
    Integrable (fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) *
        ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2) ∧
      ∫ t : ℝ, Real.exp (-((H / Y) ^ 2 / (16 * a₂ ^ 2)) * t ^ 2) *
          ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 ≤
        Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) *
          ∫ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) *
            ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 := by
  have hlam : 0 < H / Y := div_pos hH hY
  have hc : 0 < (H / Y) ^ 2 / (16 * a₂ ^ 2) := by positivity
  have hPc : Continuous fun t : ℝ =>
      ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 :=
    ((continuous_finsetSum _ fun w _ =>
      continuous_const.mul (Separation.continuous_phase _)).norm).pow 2
  have hPB : ∀ t : ℝ, ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 ≤
      (∑ w ∈ s, ‖a w‖) ^ 2 := by
    intro t
    refine pow_le_pow_left₀ (norm_nonneg _)
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)) 2
    rw [norm_mul, Separation.norm_phase, mul_one]
  have hu : ∀ t : ℝ, 0 ≤ H * |t| / Y := fun t => by positivity
  have hbase : Continuous fun t : ℝ => 1 + H * |t| / Y :=
    continuous_const.add ((continuous_const.mul continuous_abs).div_const Y)
  have hwc : Continuous fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) :=
    hbase.rpow_const fun t =>
      Or.inl (lt_of_lt_of_le one_pos (le_add_of_nonneg_right (hu t))).ne'
  have hsq : ∀ t : ℝ, (H * |t| / Y) ^ 2 = (H / Y) ^ 2 * t ^ 2 := by
    intro t
    have e1 : H * |t| / Y = H / Y * |t| := by ring
    rw [e1, mul_pow, sq_abs]
  -- the weight is dominated by `(1 + (Ht/Y)²)⁻¹`
  have hwle : ∀ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) ≤ (1 + (H / Y * t) ^ 2)⁻¹ := by
    intro t
    have h0 := hu t
    have h1 : 0 < 1 + H * |t| / Y := by linarith
    rw [Real.rpow_neg h1.le, Real.rpow_natCast]
    refine inv_anti₀ (by positivity) ?_
    calc 1 + (H / Y * t) ^ 2 ≤ (1 + H * |t| / Y) ^ 2 := by
          rw [mul_pow, ← hsq t]
          nlinarith
      _ ≤ (1 + H * |t| / Y) ^ j := pow_le_pow_right₀ (by linarith) hj
  have hinv : Integrable (fun t : ℝ => (1 + (H / Y * t) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hlam.ne'
  have hwint : Integrable (fun t : ℝ => (1 + H * |t| / Y) ^ (-(j : ℝ)) *
      ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2) := by
    refine Integrable.mono' (hinv.mul_const ((∑ w ∈ s, ‖a w‖) ^ 2))
      (hwc.mul hPc).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    have h0 : 0 ≤ (1 + H * |t| / Y) ^ (-(j : ℝ)) :=
      Real.rpow_nonneg (by linarith [hu t]) _
    show ‖(1 + H * |t| / Y) ^ (-(j : ℝ)) *
        ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2‖ ≤
      (1 + (H / Y * t) ^ 2)⁻¹ * (∑ w ∈ s, ‖a w‖) ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
    exact mul_le_mul (hwle t) (hPB t) (sq_nonneg _) (by positivity)
  refine ⟨hwint, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono (integral_gauss_expSum s a (fun w : ℕ => Real.log (w : ℝ)) hc).1
    (hwint.const_mul _) fun t => ?_
  show Real.exp (-((H / Y) ^ 2 / (16 * a₂ ^ 2)) * t ^ 2) *
      ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 ≤
    Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * ((1 + H * |t| / Y) ^ (-(j : ℝ)) *
      ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2)
  have hexp : -((H / Y) ^ 2 / (16 * a₂ ^ 2)) * t ^ 2 =
      -((H * |t| / Y) ^ 2 / (16 * a₂ ^ 2)) := by
    rw [hsq t]
    ring
  have hw := mul_le_mul_of_nonneg_right (exp_weight_le ha₂ (hu t) j)
    (sq_nonneg ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖)
  rw [hexp, ← mul_assoc]
  exact hw

end LocalMellinAux

open LocalMellinAux in
/-- **Lemma (Local Mellin energy)** (`[P-06:0488–0528]`). -/
theorem localMellin : LocalMellin := by
  intro j hj a₁ a₂ ha₁ ha₁₂
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  obtain ⟨K, hK0, hK⟩ := additive_le ha₁ ha₁₂
  refine ⟨Real.exp (2 * Real.pi ^ 2) / Real.pi *
    (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) + K),
    fun Y H hH hHY s a hs => ?_⟩
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH
  have hY : 0 < Y := lt_of_lt_of_le hH0 hHY
  have hpos : ∀ w ∈ s, 0 < w := by
    intro w hw
    have h' : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le (mul_pos ha₁ hY) (hs w hw).1
    exact_mod_cast h'
  -- the Dirichlet polynomial `∑ a_w w^{it}` in the form `∑ a_w e^{it log w}`
  have hP : ∀ t : ℝ, ∑ w ∈ s, a w * (w : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ)) := fun t =>
    Finset.sum_congr rfl fun w hw => by rw [Separation.natCast_cpow_eq_phase (hpos w hw)]
  simp only [hP]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∫ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) *
      ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact integral_nonneg fun t =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑ w ∈ s, ‖a w‖ ^ 2 := ⟨_, rfl⟩
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg fun w _ => sq_nonneg _
  rw [← hX, ← hSg]
  have hc : 0 < (H / Y) ^ 2 / (16 * a₂ ^ 2) := by positivity
  have hlo : 0 < a₁ * Y / 2 := by positivity
  have hlohi : a₁ * Y / 2 ≤ 2 * a₂ * Y := by
    have h := mul_le_mul_of_nonneg_right ha₁₂ hY.le
    have h' := mul_pos ha₁ hY
    linarith
  have hκ₁ : 0 < (a₁ * Y / 2 / H) ^ 2 := by positivity
  have hγ₀ : 1 / (2 * ((H / Y) ^ 2 / (16 * a₂ ^ 2))) = 2 * (2 * a₂ * Y / H) ^ 2 := by
    rw [one_div, mul_inv, inv_div]
    simp only [div_pow]
    rw [div_div_eq_mul_div]
    ring
  -- step 1: the arc against the additive Gaussian windows
  have h1 := arc_le_gauss s a hH0
  -- step 2: additive windows against logarithmic windows
  have h2 := hK H Y hH hHY s a hs
  rw [← hSg] at h2
  -- step 3: varying width against the fixed width `1/(2c)`
  have h3 := integral_cmpWin_le s a hH0 hlo hlohi hκ₁ le_rfl (le_of_eq hγ₀.symm)
  -- step 4: the Mellin side
  obtain ⟨JT, hJT⟩ : ∃ JT : ℝ, JT = ∫ y : ℝ,
      ‖logWin s a (1 / (2 * ((H / Y) ^ 2 / (16 * a₂ ^ 2)))) y‖ ^ 2 := ⟨_, rfl⟩
  have h4 : ∫ t : ℝ, Real.exp (-((H / Y) ^ 2 / (16 * a₂ ^ 2)) * t ^ 2) *
        ‖∑ w ∈ s, a w * Separation.phase t (Real.log (w : ℝ))‖ ^ 2 =
      ((H / Y) ^ 2 / (16 * a₂ ^ 2))⁻¹ * JT := by
    rw [hJT]
    exact gauss_bridge s a (fun w : ℕ => Real.log (w : ℝ)) hc
  obtain ⟨-, h5⟩ := mellin_le s a ha₂ hH0 hY hj
  rw [h4, ← hX] at h5
  have hJTle : JT ≤ (H / Y) ^ 2 / (16 * a₂ ^ 2) *
      (Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * X) := by
    have h := mul_le_mul_of_nonneg_left h5 hc.le
    rw [mul_inv_cancel_left₀ hc.ne'] at h
    exact h
  rw [← hJT] at h3
  obtain ⟨Jc, hJc⟩ : ∃ Jc : ℝ, Jc = ∫ v in (a₁ * Y / 2)..(2 * a₂ * Y),
      ‖cmpWin s a H (Real.log v)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hJc] at h2 h3
  obtain ⟨JS, hJS⟩ : ∃ JS : ℝ, JS = ∫ v : ℝ, ‖∑ w ∈ s, a w *
      ((Real.exp (-(1 / H ^ 2) * ((w : ℝ) - v) ^ 2) : ℝ) : ℂ)‖ ^ 2 := ⟨_, rfl⟩
  rw [← hJS] at h1 h2
  -- the constants: "the outside normalization is `H⁻² Y h₀² = Y⁻¹`"
  have hYi : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hY.ne'
  have hcoef : 0 ≤ 2 * (1 / (2 * ((H / Y) ^ 2 / (16 * a₂ ^ 2)))) / (a₁ * Y / 2 / H) ^ 2 *
      (2 * a₂ * Y) := by positivity
  have hhiκ : 2 * a₂ * Y / (a₁ * Y / 2 / H) ^ 2 = 8 * a₂ * H ^ 2 / (a₁ ^ 2 * Y) := by
    rw [div_pow, div_div_eq_mul_div]
    linear_combination (8 * a₂ * H ^ 2 * a₁⁻¹ ^ 2 * Y⁻¹) * hYi
  have h3' : Jc ≤ 8 * a₂ * H ^ 2 / (a₁ ^ 2 * Y) *
      (Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * X) := by
    refine (h3.trans (mul_le_mul_of_nonneg_left hJTle hcoef)).trans (le_of_eq ?_)
    rw [const_cancel hc.ne', hhiκ]
  have hJS' : JS ≤ H ^ 2 * (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) *
      (Y⁻¹ * X) + K * ((H / Y) ^ 2 * Sg)) := by
    have e : H ^ 2 * (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * (Y⁻¹ * X) +
          K * ((H / Y) ^ 2 * Sg)) =
        2 * (8 * a₂ * H ^ 2 / (a₁ ^ 2 * Y) * (Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * X)) +
          K * ((H / Y) ^ 2 * H ^ 2) * Sg := by ring
    rw [e]
    linarith
  have hE0 : 0 ≤ Real.exp (2 * Real.pi ^ 2) / (Real.pi * H ^ 2) := by positivity
  have hA : 0 ≤ 16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) := by positivity
  have hx : 0 ≤ Y⁻¹ * X := mul_nonneg (inv_pos.mpr hY).le hX0
  have hz : 0 ≤ (H / Y) ^ 2 * Sg := mul_nonneg (sq_nonneg _) hSg0
  calc ∫ β in (-(1 / H))..(1 / H), ‖∑ w ∈ s, a w * addChar (β * (w : ℝ))‖ ^ 2
      ≤ Real.exp (2 * Real.pi ^ 2) / (Real.pi * H ^ 2) * JS := h1
    _ ≤ Real.exp (2 * Real.pi ^ 2) / (Real.pi * H ^ 2) *
          (H ^ 2 * (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * (Y⁻¹ * X) +
            K * ((H / Y) ^ 2 * Sg))) := mul_le_mul_of_nonneg_left hJS' hE0
    _ = Real.exp (2 * Real.pi ^ 2) / Real.pi *
          (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * (Y⁻¹ * X) +
            K * ((H / Y) ^ 2 * Sg)) := div_sq_mul_cancel hH0.ne'
    _ ≤ Real.exp (2 * Real.pi ^ 2) / Real.pi *
          ((16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) + K) *
            (Y⁻¹ * X + (H / Y) ^ 2 * Sg)) :=
        mul_le_mul_of_nonneg_left (add_mul_le_mul_add hA hK0 hx hz) (by positivity)
    _ = Real.exp (2 * Real.pi ^ 2) / Real.pi *
          (16 * a₂ / a₁ ^ 2 * Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) + K) *
            (Y⁻¹ * X + (H / Y) ^ 2 * Sg) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.LocalMellinWindow
public import Mathlib.Analysis.Convolution

/-!
# Logarithmic Gaussian windows of varying width

Second half of the comparison for `LocalMellin` (`[P-06:0488–0528]`). After the replacement of
`K((w-v)/H)` by `K(v log(w/v)/H)` the manuscript writes `v = Y e^u` and treats the dependence of
the width `v/H` on the centre by "two integrations by parts in `u` and the Schwartz bounds for
`K̂` … Expand in `s`, apply Minkowski and Plancherel in `u`, and use `dv ≪ Y du`."

For the Gaussian `K` this step is an exact superposition. With
`logWin γ y = ∑_w a_w e^{-γ (log w - y)²}`:

* `integral_gauss_logWin`: a window of width `γ < γ₀` is a Gaussian average of windows of the
  fixed width `γ₀`, `∫ e^{-κz²} logWin γ₀ (y - z) dz = √(π/(γ₀+κ)) logWin γ y`,
  `γ = γ₀κ/(γ₀+κ)`;
* `norm_sq_integral_le`: Cauchy–Schwarz for such an average;
* `normSq_logWin_le`: hence `|logWin γ y|² ≤ C ∫ e^{-κ₁z²} |logWin γ₀ (y-z)|² dz` uniformly for
  `κ₁ ≤ γ ≤ γ₀/2`;
* `integral_conv_logWin`: the integral over `y` of the right side is `√(π/κ₁) ∫ |logWin γ₀|²`
  (`MeasureTheory.integral_convolution`);
* `integral_comp_log`: the substitution `v = e^y`;
* `integral_cmpWin_le`: together, for `cmpWin H y = logWin ((e^y/H)²) y`,
  `∫_{lo}^{hi} |cmpWin H (log v)|² dv ≤ (2γ₀/κ₁) hi ∫ |logWin γ₀ y|² dy`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory

noncomputable section

namespace LocalMellinAux

/-- The combination of logarithmic Gaussian windows of width `γ` centred at `e^y`:
`∑_w a_w e^{-γ (log w - y)²}`. -/
def logWin (s : Finset ℕ) (a : ℕ → ℂ) (γ y : ℝ) : ℂ :=
  ∑ w ∈ s, a w * ((Real.exp (-γ * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ)

theorem continuous_logWin (s : Finset ℕ) (a : ℕ → ℂ) (γ : ℝ) : Continuous (logWin s a γ) := by
  show Continuous fun y : ℝ =>
    ∑ w ∈ s, a w * ((Real.exp (-γ * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ)
  exact continuous_finsetSum _ fun w _ => continuous_const.mul
    (Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun y : ℝ => Real.exp (-γ * (Real.log (w : ℝ) - y) ^ 2)))

theorem norm_logWin_le (s : Finset ℕ) (a : ℕ → ℂ) {γ : ℝ} (hγ : 0 ≤ γ) (y : ℝ) :
    ‖logWin s a γ y‖ ≤ ∑ w ∈ s, ‖a w‖ := by
  unfold logWin
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h : Real.exp (-γ * (Real.log (w : ℝ) - y) ^ 2) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have h0 := mul_nonneg hγ (sq_nonneg (Real.log (w : ℝ) - y))
    linarith
  exact mul_le_of_le_one_right (norm_nonneg _) h

/-- The logarithmic windows at the centre `e^y` with the matching width `(e^y/H)²`. -/
def cmpWin (s : Finset ℕ) (a : ℕ → ℂ) (H y : ℝ) : ℂ := logWin s a ((Real.exp y / H) ^ 2) y

theorem continuous_cmpWin (s : Finset ℕ) (a : ℕ → ℂ) (H : ℝ) : Continuous (cmpWin s a H) := by
  show Continuous fun y : ℝ => ∑ w ∈ s,
    a w * ((Real.exp (-(Real.exp y / H) ^ 2 * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ)
  exact continuous_finsetSum _ fun w _ => continuous_const.mul
    (Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun y : ℝ =>
        Real.exp (-(Real.exp y / H) ^ 2 * (Real.log (w : ℝ) - y) ^ 2)))

/-! ### Cauchy–Schwarz for a weighted average -/

/-- If `0 ≤ Q - 2mA + m²K` for all `m` and `K > 0`, then `A² ≤ KQ`. -/
theorem sq_le_of_quadratic {A K Q : ℝ} (hK : 0 < K)
    (h : ∀ m : ℝ, 0 ≤ Q - 2 * m * A + m ^ 2 * K) : A ^ 2 ≤ K * Q := by
  have hq : A / K * K = A := div_mul_cancel₀ _ hK.ne'
  have h1 := h (A / K)
  have h2 : (A / K) ^ 2 * K ≤ Q := by
    have e : 2 * (A / K) * A = 2 * ((A / K) ^ 2 * K) := by
      have e' : (A / K) ^ 2 * K = A / K * (A / K * K) := by ring
      rw [e', hq]
      ring
    linarith
  calc A ^ 2 = (A / K * K) ^ 2 := by rw [hq]
    _ = (A / K) ^ 2 * K * K := by ring
    _ ≤ Q * K := mul_le_mul_of_nonneg_right h2 hK.le
    _ = K * Q := mul_comm _ _

/-- **Cauchy–Schwarz for an average against a nonnegative weight**:
`‖∫ k F‖² ≤ (∫ k)(∫ k ‖F‖²)`. -/
theorem norm_sq_integral_le {k : ℝ → ℝ} {F : ℝ → ℂ} (hk0 : ∀ z, 0 ≤ k z) (hk : Integrable k)
    (hK : 0 < ∫ z, k z) (hF : Continuous F) {B : ℝ} (hFB : ∀ z, ‖F z‖ ≤ B) :
    ‖∫ z, ((k z : ℝ) : ℂ) * F z‖ ^ 2 ≤ (∫ z, k z) * ∫ z, k z * ‖F z‖ ^ 2 := by
  have hm1 : AEStronglyMeasurable (fun z => k z * ‖F z‖) :=
    hk.aestronglyMeasurable.mul hF.norm.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun z => k z * ‖F z‖ ^ 2) :=
    hk.aestronglyMeasurable.mul (hF.norm.pow 2).aestronglyMeasurable
  have hkF : Integrable (fun z => k z * ‖F z‖) :=
    Integrable.mono' (hk.mul_const B) hm1 (ae_of_all _ fun z => by
      show ‖k z * ‖F z‖‖ ≤ k z * B
      rw [Real.norm_of_nonneg (mul_nonneg (hk0 z) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hFB z) (hk0 z))
  have hkF2 : Integrable (fun z => k z * ‖F z‖ ^ 2) :=
    Integrable.mono' (hk.mul_const (B ^ 2)) hm2 (ae_of_all _ fun z => by
      show ‖k z * ‖F z‖ ^ 2‖ ≤ k z * B ^ 2
      rw [Real.norm_of_nonneg (mul_nonneg (hk0 z) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hFB z) 2) (hk0 z))
  have hnorm : ‖∫ z, ((k z : ℝ) : ℂ) * F z‖ ≤ ∫ z, k z * ‖F z‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show ‖((k z : ℝ) : ℂ) * F z‖ = k z * ‖F z‖
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hk0 z)]
  have hquad : ∀ m : ℝ, 0 ≤ (∫ z, k z * ‖F z‖ ^ 2) - 2 * m * (∫ z, k z * ‖F z‖) +
      m ^ 2 * ∫ z, k z := by
    intro m
    have i1 : Integrable (fun z => k z * ‖F z‖ ^ 2 - 2 * m * (k z * ‖F z‖)) :=
      hkF2.sub (hkF.const_mul _)
    have i2 : Integrable (fun z => m ^ 2 * k z) := hk.const_mul _
    have i3 : Integrable (fun z => 2 * m * (k z * ‖F z‖)) := hkF.const_mul _
    have h0 : 0 ≤ ∫ z, (k z * ‖F z‖ ^ 2 - 2 * m * (k z * ‖F z‖) + m ^ 2 * k z) :=
      integral_nonneg fun z => by
        have e : k z * ‖F z‖ ^ 2 - 2 * m * (k z * ‖F z‖) + m ^ 2 * k z =
            k z * (‖F z‖ - m) ^ 2 := by ring
        show 0 ≤ k z * ‖F z‖ ^ 2 - 2 * m * (k z * ‖F z‖) + m ^ 2 * k z
        rw [e]
        exact mul_nonneg (hk0 z) (sq_nonneg _)
    rw [integral_add i1 i2, integral_sub hkF2 i3, integral_const_mul, integral_const_mul] at h0
    exact h0
  calc ‖∫ z, ((k z : ℝ) : ℂ) * F z‖ ^ 2 ≤ (∫ z, k z * ‖F z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ z, k z) * ∫ z, k z * ‖F z‖ ^ 2 := sq_le_of_quadratic hK hquad

/-! ### Superposition of logarithmic windows -/

theorem integrable_gauss_conv {g κ : ℝ} (hg : 0 < g) (hκ : 0 < κ) (x : ℝ) :
    Integrable (fun z : ℝ => Real.exp (-g * (x - z) ^ 2) * Real.exp (-κ * z ^ 2)) := by
  have hgκ : g + κ ≠ 0 := (add_pos hg hκ).ne'
  have e : (fun z : ℝ => Real.exp (-g * (x - z) ^ 2) * Real.exp (-κ * z ^ 2)) =
      fun z : ℝ => Real.exp (-(g * κ / (g + κ)) * x ^ 2) *
        Real.exp (-(g + κ) * (g * x / (g + κ) - z) ^ 2) := funext fun z => gauss_conv_eq hgκ x z
  rw [e]
  exact (integrable_gauss (add_pos hg hκ) _).const_mul _

/-- **A window of width `γ₀κ/(γ₀+κ)` is a Gaussian average of windows of width `γ₀`.** -/
theorem integral_gauss_logWin (s : Finset ℕ) (a : ℕ → ℂ) {γ₀ κ : ℝ} (hγ₀ : 0 < γ₀) (hκ : 0 < κ)
    (y : ℝ) :
    ∫ z : ℝ, ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) * logWin s a γ₀ (y - z) =
      ((Real.sqrt (Real.pi / (γ₀ + κ)) : ℝ) : ℂ) * logWin s a (γ₀ * κ / (γ₀ + κ)) y := by
  have he : ∀ w : ℕ, (fun z : ℝ => ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
        (a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ))) =
      fun z : ℝ => a w * ((Real.exp (-γ₀ * (y - Real.log (w : ℝ) - z) ^ 2) *
        Real.exp (-κ * z ^ 2) : ℝ) : ℂ) := by
    intro w
    funext z
    have e : (Real.log (w : ℝ) - (y - z)) ^ 2 = (y - Real.log (w : ℝ) - z) ^ 2 := by ring
    rw [e, Complex.ofReal_mul]
    ring
  have hint : ∀ w ∈ s, Integrable (fun z : ℝ => ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
      (a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ))) := by
    intro w _
    rw [he w]
    exact ((integrable_gauss_conv hγ₀ hκ (y - Real.log (w : ℝ))).ofReal).const_mul _
  have hterm : ∀ w : ℕ, ∫ z : ℝ, ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
        (a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ)) =
      a w * ((Real.sqrt (Real.pi / (γ₀ + κ)) *
        Real.exp (-(γ₀ * κ / (γ₀ + κ)) * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ) := by
    intro w
    have e : (y - Real.log (w : ℝ)) ^ 2 = (Real.log (w : ℝ) - y) ^ 2 := by ring
    rw [he w, integral_const_mul, integral_complex_ofReal, integral_gauss_conv hγ₀ hκ, e]
  unfold logWin
  calc ∫ z : ℝ, ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
        ∑ w ∈ s, a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ)
      = ∫ z : ℝ, ∑ w ∈ s, ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
          (a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        exact Finset.mul_sum _ _ _
    _ = ∑ w ∈ s, ∫ z : ℝ, ((Real.exp (-κ * z ^ 2) : ℝ) : ℂ) *
          (a w * ((Real.exp (-γ₀ * (Real.log (w : ℝ) - (y - z)) ^ 2) : ℝ) : ℂ)) :=
        integral_finsetSum s hint
    _ = ∑ w ∈ s, a w * ((Real.sqrt (Real.pi / (γ₀ + κ)) *
          Real.exp (-(γ₀ * κ / (γ₀ + κ)) * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun w _ => hterm w
    _ = ((Real.sqrt (Real.pi / (γ₀ + κ)) : ℝ) : ℂ) * ∑ w ∈ s,
          a w * ((Real.exp (-(γ₀ * κ / (γ₀ + κ)) * (Real.log (w : ℝ) - y) ^ 2) : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Complex.ofReal_mul]
        ring

theorem integrable_gauss_mul_normSq (s : Finset ℕ) (a : ℕ → ℂ) {γ₀ κ : ℝ} (hγ₀ : 0 ≤ γ₀)
    (hκ : 0 < κ) (y : ℝ) :
    Integrable (fun z : ℝ => Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) := by
  have hc : Continuous fun z : ℝ => logWin s a γ₀ (y - z) :=
    (continuous_logWin s a γ₀).comp (by fun_prop : Continuous fun z : ℝ => y - z)
  have hm : AEStronglyMeasurable
      (fun z : ℝ => Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) :=
    (integrable_exp_neg_mul_sq hκ).aestronglyMeasurable.mul (hc.norm.pow 2).aestronglyMeasurable
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hκ).mul_const ((∑ w ∈ s, ‖a w‖) ^ 2)) hm
    (ae_of_all _ fun z => ?_)
  show ‖Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2‖ ≤
    Real.exp (-κ * z ^ 2) * (∑ w ∈ s, ‖a w‖) ^ 2
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_logWin_le s a hγ₀ _) 2) (Real.exp_pos _).le

/-- **Varying width against fixed width**: for `κ₁ ≤ γ ≤ γ₀/2`,
`|logWin γ y|² ≤ (2γ₀/π) √(π/κ₁) ∫ e^{-κ₁z²} |logWin γ₀ (y - z)|² dz`. -/
theorem normSq_logWin_le (s : Finset ℕ) (a : ℕ → ℂ) {γ₀ γ κ₁ : ℝ} (hκ₁ : 0 < κ₁) (hκγ : κ₁ ≤ γ)
    (hγ : 2 * γ ≤ γ₀) (y : ℝ) :
    ‖logWin s a γ y‖ ^ 2 ≤ 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) *
      ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 := by
  have hγ0 : 0 < γ := lt_of_lt_of_le hκ₁ hκγ
  have hγ₀ : 0 < γ₀ := by linarith
  have hd : 0 < γ₀ - γ := by linarith
  obtain ⟨κ, hκeq⟩ : ∃ κ : ℝ, κ * (γ₀ - γ) = γ * γ₀ :=
    ⟨γ * γ₀ / (γ₀ - γ), div_mul_cancel₀ _ hd.ne'⟩
  have hκ_ge : γ ≤ κ := by
    refine le_of_mul_le_mul_right ?_ hd
    rw [hκeq]
    nlinarith [sq_nonneg γ]
  have hκ_le : κ ≤ γ₀ := by
    refine le_of_mul_le_mul_right ?_ hd
    rw [hκeq]
    nlinarith [mul_nonneg hγ₀.le (sub_nonneg.mpr hγ)]
  have hκ : 0 < κ := lt_of_lt_of_le hγ0 hκ_ge
  have hγκ : 0 < γ₀ + κ := add_pos hγ₀ hκ
  have hγeq : γ₀ * κ / (γ₀ + κ) = γ := by
    rw [div_eq_iff hγκ.ne']
    linarith
  have hF1 := integral_gauss_logWin s a hγ₀ hκ y
  rw [hγeq] at hF1
  have hKint : ∫ z : ℝ, Real.exp (-κ * z ^ 2) = Real.sqrt (Real.pi / κ) := integral_gaussian κ
  have hKpos : 0 < ∫ z : ℝ, Real.exp (-κ * z ^ 2) := by
    rw [hKint]
    exact Real.sqrt_pos.mpr (div_pos Real.pi_pos hκ)
  have hc : Continuous fun z : ℝ => logWin s a γ₀ (y - z) :=
    (continuous_logWin s a γ₀).comp (by fun_prop : Continuous fun z : ℝ => y - z)
  have hCS := norm_sq_integral_le (k := fun z : ℝ => Real.exp (-κ * z ^ 2))
    (F := fun z : ℝ => logWin s a γ₀ (y - z)) (fun z => (Real.exp_pos _).le)
    (integrable_exp_neg_mul_sq hκ) hKpos hc (fun z => norm_logWin_le s a hγ₀.le (y - z))
  rw [hF1, hKint, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (div_pos Real.pi_pos hγκ).le] at hCS
  have hmono : ∫ z : ℝ, Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 ≤
      ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 := by
    refine integral_mono (integrable_gauss_mul_normSq s a hγ₀.le hκ y)
      (integrable_gauss_mul_normSq s a hγ₀.le hκ₁ y) fun z => ?_
    show Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 ≤
      Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_right (hκγ.trans hκ_ge) (sq_nonneg z)
    linarith
  have hI0 : 0 ≤ ∫ z : ℝ, Real.exp (-κ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 :=
    integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ,
      Φ = ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 := ⟨_, rfl⟩
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦ]
    exact integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rw [← hΦ] at hmono ⊢
  have hsq : Real.sqrt (Real.pi / κ) ≤ Real.sqrt (Real.pi / κ₁) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le hκ₁ (hκγ.trans hκ_ge))
  have hmain : Real.pi / (γ₀ + κ) * ‖logWin s a γ y‖ ^ 2 ≤ Real.sqrt (Real.pi / κ₁) * Φ :=
    hCS.trans (mul_le_mul hsq hmono hI0 (Real.sqrt_nonneg _))
  have hpos : 0 < Real.pi / (γ₀ + κ) := div_pos Real.pi_pos hγκ
  have hX0 : 0 ≤ Real.sqrt (Real.pi / κ₁) * Φ := mul_nonneg (Real.sqrt_nonneg _) hΦ0
  calc ‖logWin s a γ y‖ ^ 2 ≤ Real.sqrt (Real.pi / κ₁) * Φ / (Real.pi / (γ₀ + κ)) :=
        (le_div_iff₀ hpos).mpr ((mul_comm _ _).trans_le hmain)
    _ = Real.sqrt (Real.pi / κ₁) * Φ * (γ₀ + κ) / Real.pi := by rw [div_div_eq_mul_div]
    _ ≤ Real.sqrt (Real.pi / κ₁) * Φ * (2 * γ₀) / Real.pi :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hX0) Real.pi_pos.le
    _ = 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * Φ := by ring

/-- The Gaussian averages of `|logWin γ₀|²` integrate to `√(π/κ₁) ∫ |logWin γ₀|²`. -/
theorem integral_conv_logWin (s : Finset ℕ) (a : ℕ → ℂ) {γ₀ κ₁ : ℝ} (hγ₀ : 0 < γ₀)
    (hκ₁ : 0 < κ₁) :
    Integrable (fun y : ℝ =>
        ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) ∧
      ∫ y : ℝ, ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 =
        Real.sqrt (Real.pi / κ₁) * ∫ y : ℝ, ‖logWin s a γ₀ y‖ ^ 2 := by
  have hk : Integrable (fun z : ℝ => Real.exp (-κ₁ * z ^ 2)) := integrable_exp_neg_mul_sq hκ₁
  have hT : Integrable (fun y : ℝ => ‖logWin s a γ₀ y‖ ^ 2) :=
    (integral_gauss_windowSum s a (fun w : ℕ => Real.log (w : ℝ)) hγ₀).1
  have e : ∀ y : ℝ, (∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) =
      MeasureTheory.convolution (fun z : ℝ => Real.exp (-κ₁ * z ^ 2))
        (fun y : ℝ => ‖logWin s a γ₀ y‖ ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume y := by
    intro y
    rw [MeasureTheory.convolution_mul]
  have hint : Integrable (MeasureTheory.convolution (fun z : ℝ => Real.exp (-κ₁ * z ^ 2))
      (fun y : ℝ => ‖logWin s a γ₀ y‖ ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hk.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hT
  refine ⟨hint.congr (ae_of_all _ fun y => (e y).symm), ?_⟩
  rw [integral_congr_ae (ae_of_all _ e),
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hk hT, ContinuousLinearMap.mul_apply',
    integral_gaussian]

/-! ### The substitution `v = e^y` -/

/-- `∫_{lo}^{hi} g(log v) dv = ∫_{log lo}^{log hi} g(y) e^y dy`. -/
theorem integral_comp_log {g : ℝ → ℝ} (hg : Continuous g) {lo hi : ℝ} (hlo : 0 < lo)
    (hhi : 0 < hi) :
    ∫ v in lo..hi, g (Real.log v) =
      ∫ y in (Real.log lo)..(Real.log hi), g y * Real.exp y := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a := Real.log lo) (b := Real.log hi)
    (f := Real.exp) (f' := Real.exp) (g := fun v => g (Real.log v))
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
    (hg.comp_continuousOn (Real.continuousOn_log.mono (by
      rintro _ ⟨x, -, rfl⟩
      exact Set.mem_compl_singleton_iff.mpr (Real.exp_pos x).ne')))
  calc ∫ v in lo..hi, g (Real.log v)
      = ∫ v in (Real.exp (Real.log lo))..(Real.exp (Real.log hi)), g (Real.log v) := by
        rw [Real.exp_log hlo, Real.exp_log hhi]
    _ = ∫ y in (Real.log lo)..(Real.log hi),
          ((fun v => g (Real.log v)) ∘ Real.exp) y * Real.exp y := h.symm
    _ = ∫ y in (Real.log lo)..(Real.log hi), g y * Real.exp y := by
        refine intervalIntegral.integral_congr fun y _ => ?_
        simp only [Function.comp_apply, Real.log_exp]

/-- **The logarithmic windows with the matching width against the fixed width `γ₀`.** For
`κ₁ ≤ (lo/H)²` and `2(hi/H)² ≤ γ₀`,
`∫_{lo}^{hi} |cmpWin H (log v)|² dv ≤ (2γ₀/κ₁) hi ∫ |logWin γ₀ y|² dy`. -/
theorem integral_cmpWin_le (s : Finset ℕ) (a : ℕ → ℂ) {H lo hi γ₀ κ₁ : ℝ} (hH : 0 < H)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hκ₁ : 0 < κ₁) (hκlo : κ₁ ≤ (lo / H) ^ 2)
    (hγhi : 2 * (hi / H) ^ 2 ≤ γ₀) :
    ∫ v in lo..hi, ‖cmpWin s a H (Real.log v)‖ ^ 2 ≤
      2 * γ₀ / κ₁ * hi * ∫ y : ℝ, ‖logWin s a γ₀ y‖ ^ 2 := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have hγ₀ : 0 < γ₀ := lt_of_lt_of_le (by positivity) hγhi
  have hgc : Continuous fun y : ℝ => ‖cmpWin s a H y‖ ^ 2 :=
    (continuous_cmpWin s a H).norm.pow 2
  obtain ⟨hΦint, hΦ⟩ := integral_conv_logWin s a hγ₀ hκ₁
  have hloglohi : Real.log lo ≤ Real.log hi := Real.log_le_log hlo hlohi
  have hΦ0 : ∀ y : ℝ,
      0 ≤ ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 :=
    fun y => integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hc0 : 0 ≤ 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) := by positivity
  -- the substitution `v = e^y`
  rw [integral_comp_log hgc hlo hhi]
  -- the pointwise bound on `[log lo, log hi]`
  have hpt : ∀ y ∈ Set.Icc (Real.log lo) (Real.log hi), ‖cmpWin s a H y‖ ^ 2 * Real.exp y ≤
      2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * hi *
        ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 := by
    intro y hy
    have h1 : lo ≤ Real.exp y := (Real.log_le_iff_le_exp hlo).mp hy.1
    have h2 : Real.exp y ≤ hi := (Real.le_log_iff_exp_le hhi).mp hy.2
    have hκγ : κ₁ ≤ (Real.exp y / H) ^ 2 :=
      hκlo.trans (pow_le_pow_left₀ (div_nonneg hlo.le hH.le)
        (div_le_div_of_nonneg_right h1 hH.le) 2)
    have hγ : 2 * (Real.exp y / H) ^ 2 ≤ γ₀ := by
      have h := pow_le_pow_left₀ (div_nonneg (Real.exp_pos y).le hH.le)
        (div_le_div_of_nonneg_right h2 hH.le) 2
      linarith
    have hb : ‖cmpWin s a H y‖ ^ 2 ≤ 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) *
        ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 :=
      normSq_logWin_le s a hκ₁ hκγ hγ y
    calc ‖cmpWin s a H y‖ ^ 2 * Real.exp y
        ≤ 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) *
            (∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) * hi :=
          mul_le_mul hb h2 (Real.exp_pos y).le (mul_nonneg hc0 (hΦ0 y))
      _ = 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * hi *
            ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 := by ring
  have hf1 : IntervalIntegrable (fun y : ℝ => ‖cmpWin s a H y‖ ^ 2 * Real.exp y) volume
      (Real.log lo) (Real.log hi) := (hgc.mul Real.continuous_exp).intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun y : ℝ => 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * hi *
      ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2) volume
      (Real.log lo) (Real.log hi) := (hΦint.const_mul _).intervalIntegrable
  refine (intervalIntegral.integral_mono_on hloglohi hf1 hf2 hpt).trans ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hloglohi]
  have hset : ∫ y in Set.Ioc (Real.log lo) (Real.log hi),
        ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 ≤
      ∫ y : ℝ, ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2 :=
    setIntegral_le_integral hΦint (ae_of_all _ hΦ0)
  rw [hΦ] at hset
  have hsq : Real.sqrt (Real.pi / κ₁) * Real.sqrt (Real.pi / κ₁) = Real.pi / κ₁ :=
    Real.mul_self_sqrt (div_pos Real.pi_pos hκ₁).le
  have hπ : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  have e : 2 * γ₀ / Real.pi * (Real.pi / κ₁) = 2 * γ₀ / κ₁ := by
    linear_combination (2 * γ₀ * κ₁⁻¹) * hπ
  calc 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * hi *
        ∫ y in Set.Ioc (Real.log lo) (Real.log hi),
          ∫ z : ℝ, Real.exp (-κ₁ * z ^ 2) * ‖logWin s a γ₀ (y - z)‖ ^ 2
      ≤ 2 * γ₀ / Real.pi * Real.sqrt (Real.pi / κ₁) * hi *
          (Real.sqrt (Real.pi / κ₁) * ∫ y : ℝ, ‖logWin s a γ₀ y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hset (mul_nonneg hc0 hhi.le)
    _ = 2 * γ₀ / Real.pi * (Real.sqrt (Real.pi / κ₁) * Real.sqrt (Real.pi / κ₁)) * hi *
          ∫ y : ℝ, ‖logWin s a γ₀ y‖ ^ 2 := by ring
    _ = 2 * γ₀ / κ₁ * hi * ∫ y : ℝ, ‖logWin s a γ₀ y‖ ^ 2 := by rw [hsq, e]

end LocalMellinAux

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

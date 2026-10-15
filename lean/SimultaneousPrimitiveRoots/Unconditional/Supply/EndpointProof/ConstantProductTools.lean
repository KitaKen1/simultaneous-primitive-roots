module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ProductTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.DivisorModelProof
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Tools for the constant products

* `normPoly_add`: a normalized polynomial is additive in its coefficients (the model and its
  error, `[P-06:0860–0876]`).
* `integral_inv_sq_le`: `∫_a^b t^{-2} dt ≤ 1/lo` on an interval of `{lo ≤ |t|}` ("We used square
  integration of `1/|t|`, not a pointwise log saving multiplied by the full interval length",
  `[P-06:0898–0900]`).
* `eventually_exp_mul_rpow_neg_le_one`, `eventually_exp_neg_div_log_pow`: the two small errors
  `x^{-c'}` and `exp(-L/(log L)^{C})` pay for `exp(L^{.9})` and for any power of `L`
  (`[P-06:0913–0918]`).
* `eventually_rpow_lt_exp_tenth`, `rpow_lt_of_mem_markPrimes`: the marked primes exceed
  `L^{C}`, so the divisors of the model are units modulo `k ≤ L^{C_6}` (`[P-06:0881–0883]`).
* `mul_sq_mul_sq_le_rpow_neg`, `sq_rpow_mul_rpow_neg_le`: the bookkeeping of the powers of `L`.
* `integral_three_terms`, `continuousOn_inv_sq`: linearity of the integral for the three terms of
  the majorant.
* `sum_normSq_natIcc_le_of_model`: the mean square of the model error on `[R_0, ρ R_0]` from the
  dyads (`[P-06:0864–0870]`).
* `integral_normSq_normPoly_natIcc_le`: the mean-value theorem on `[R_0, ρ R_0]` for an interval
  of times of length `≤ R_0` ((cor:length-dominates-time), `[P-06:0765–0769]`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- A normalized polynomial is additive in its coefficients. -/
theorem normPoly_add (R : ℝ) (s : Finset ℕ) (f g : ℕ → ℂ) (t : ℝ) :
    normPoly R s (fun n => f n + g n) t = normPoly R s f t + normPoly R s g t := by
  have h1 : normPoly R s (fun n => f n + g n) t =
      (R : ℂ)⁻¹ * ∑ n ∈ s, (f n + g n) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have h2 : normPoly R s f t =
      (R : ℂ)⁻¹ * ∑ n ∈ s, f n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have h3 : normPoly R s g t =
      (R : ℂ)⁻¹ * ∑ n ∈ s, g n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [h1, h2, h3, ← mul_add, ← Finset.sum_add_distrib]
  exact congrArg (fun y : ℂ => (R : ℂ)⁻¹ * y) (Finset.sum_congr rfl fun n _ => add_mul _ _ _)

/-- `∫_a^b t^{-2} dt ≤ 1/lo` on an interval of `{lo ≤ |t| ≤ hi}`, `lo > 0`. -/
theorem integral_inv_sq_le {lo hi a b : ℝ} (hlo : 0 < lo) (hab : a ≤ b)
    (hr : (lo ≤ a ∧ b ≤ hi) ∨ (-hi ≤ a ∧ b ≤ -lo)) :
    ∫ t in a..b, (t ^ 2)⁻¹ ≤ lo⁻¹ := by
  have hne : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    rcases hr with h | h
    · have h0 : 0 < t := by linarith [ht.1, h.1]
      exact h0.ne'
    · have h0 : t < 0 := by linarith [ht.2, h.2]
      exact h0.ne
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have h1 : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(t ^ 2)⁻¹)) t :=
      (hasDerivAt_inv (hne t ht)).fun_neg
    rw [neg_neg] at h1
    exact h1
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc a b) :=
    ContinuousOn.inv₀ (f := fun t : ℝ => t ^ 2) (continuous_pow 2).continuousOn
      fun t ht => pow_ne_zero 2 (hne t ht)
  have hval : ∫ t in a..b, (t ^ 2)⁻¹ = -b⁻¹ - -a⁻¹ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hval]
  rcases hr with h | h
  · have ha0 : 0 < a := by linarith [h.1]
    have hb0 : 0 < b := by linarith
    have h1 : a⁻¹ ≤ lo⁻¹ := inv_anti₀ hlo h.1
    have h2 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
    linarith
  · have hb0 : b < 0 := by linarith [h.2]
    have ha0 : a < 0 := by linarith
    have h1 : (-b)⁻¹ ≤ lo⁻¹ := inv_anti₀ hlo (by linarith [h.2])
    have h2 : a⁻¹ ≤ 0 := inv_nonpos.mpr ha0.le
    rw [inv_neg] at h1
    linarith

/-- `exp(L^{.9}) x^{-c'} ≤ 1` for large `x`. -/
theorem eventually_exp_mul_rpow_neg_le_one {c' : ℝ} (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x ^ (0.9 : ℝ)) * x ^ (-c') ≤ 1 := by
  have h1 : ∀ᶠ x : ℝ in atTop, 1 / c' ≤ Real.log x ^ (0.1 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.1)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x a1 a2 a3
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hsplit : Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) = Real.log x := by
    have e : (0.9 : ℝ) + 0.1 = 1 := by norm_num
    rw [← Real.rpow_add hL0, e, Real.rpow_one]
  have h9 : 0 ≤ Real.log x ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
  have h2 : 1 ≤ Real.log x ^ (0.1 : ℝ) * c' := (div_le_iff₀ hc').mp a1
  have h3 : Real.log x ^ (0.9 : ℝ) * 1 ≤
      Real.log x ^ (0.9 : ℝ) * (Real.log x ^ (0.1 : ℝ) * c') := mul_le_mul_of_nonneg_left h2 h9
  have h4 : Real.log x ^ (0.9 : ℝ) * (Real.log x ^ (0.1 : ℝ) * c') = Real.log x * c' := by
    rw [← mul_assoc, hsplit]
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add]
  refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
  linarith

/-- The saving `exp(-L/(log L)^C)` of Lemma `lem:log-phase` pays for `exp(L^{.9})` and for any
fixed power of `L`, for large `x`. -/
theorem eventually_exp_neg_div_log_pow {C : ℝ} (hC : 0 < C) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (Real.log x ^ (0.9 : ℝ)) *
          Real.exp (-Real.log x / Real.log (Real.log x) ^ C) ≤ 1 ∧
        Real.exp (-Real.log x / Real.log (Real.log x) ^ C) * Real.log x ^ b ≤ 1 := by
  have hr : (0 : ℝ) < 0.1 / C := div_pos (by norm_num) hC
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hb1 : 0 < |b| + 1 := by linarith
  have hε : 0 < 1 / (|b| + 1) := one_div_pos.mpr hb1
  have h1 : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ ((0.1 : ℝ) / C)‖ :=
    Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_atTop hr).def one_pos)
  have h2 : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.log x)‖ ≤ 1 / (|b| + 1) * ‖Real.log x ^ (0.9 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.9)).def hε)
  filter_upwards [h1, h2, Real.tendsto_log_atTop.eventually_ge_atTop 3] with x a1 a2 a3
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have h9 : 0 ≤ Real.log x ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
  have hsplit : Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) = Real.log x := by
    have e : (0.9 : ℝ) + 0.1 = 1 := by norm_num
    rw [← Real.rpow_add hL0, e, Real.rpow_one]
  -- `(log L)^C ≤ L^{.1}`
  have hD : Real.log (Real.log x) ^ C ≤ Real.log x ^ (0.1 : ℝ) := by
    have hp : 0 ≤ Real.log x ^ ((0.1 : ℝ) / C) := Real.rpow_nonneg hL0.le _
    have h3 := a1
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLL0, abs_of_nonneg hp] at h3
    have e : (0.1 : ℝ) / C * C = 0.1 := div_mul_cancel₀ _ hC.ne'
    calc Real.log (Real.log x) ^ C ≤ (Real.log x ^ ((0.1 : ℝ) / C)) ^ C :=
          Real.rpow_le_rpow hLL0.le h3 hC.le
      _ = Real.log x ^ ((0.1 : ℝ) / C * C) := (Real.rpow_mul hL0.le ((0.1 : ℝ) / C) C).symm
      _ = Real.log x ^ (0.1 : ℝ) := by rw [e]
  have hDpos : 0 < Real.log (Real.log x) ^ C := Real.rpow_pos_of_pos hLL0 _
  -- `L^{.9} ≤ L / (log L)^C`
  have h5 : Real.log x ^ (0.9 : ℝ) ≤ Real.log x / Real.log (Real.log x) ^ C := by
    rw [le_div_iff₀ hDpos]
    calc Real.log x ^ (0.9 : ℝ) * Real.log (Real.log x) ^ C
        ≤ Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) := mul_le_mul_of_nonneg_left hD h9
      _ = Real.log x := hsplit
  have e : -Real.log x / Real.log (Real.log x) ^ C =
      -(Real.log x / Real.log (Real.log x) ^ C) := neg_div _ _
  -- `|b| log L ≤ L^{.9}`
  have h6 : Real.log (Real.log x) * |b| ≤ Real.log x ^ (0.9 : ℝ) := by
    have h7 := a2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLL0, abs_of_nonneg h9] at h7
    have h8 : Real.log (Real.log x) ≤ Real.log x ^ (0.9 : ℝ) / (|b| + 1) := by
      rw [← one_div_mul_eq_div]
      exact h7
    have h10 : Real.log (Real.log x) * (|b| + 1) ≤ Real.log x ^ (0.9 : ℝ) :=
      (le_div_iff₀ hb1).mp h8
    linarith
  have h11 : Real.log (Real.log x) * b ≤ Real.log (Real.log x) * |b| :=
    mul_le_mul_of_nonneg_left (le_abs_self b) hLL0.le
  constructor
  · rw [← Real.exp_add, e]
    refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
    linarith
  · rw [Real.rpow_def_of_pos hL0 b, ← Real.exp_add, e]
    refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
    linarith

/-- `L^C < exp(L^{1/10})` and `L ≥ e` for large `x`. -/
theorem eventually_rpow_lt_exp_tenth (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ Real.log x ∧
      Real.log x ^ C < Real.exp (Real.log x ^ (1 / 10 : ℝ)) := by
  have hc0 : 0 ≤ |C| := abs_nonneg C
  have hc1 : 0 < |C| + 1 := by linarith
  have hε : 0 < 1 / (|C| + 1) := one_div_pos.mpr hc1
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤
      1 / (|C| + 1) * ‖Real.log x ^ (1 / 10 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).def hε)
  filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x a1 a2
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) a2
  have hLL1 : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL0).mpr a2
  have hLL0 : 0 ≤ Real.log (Real.log x) := by linarith
  have hp : 0 < Real.log x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  refine ⟨a2, ?_⟩
  have h5 := a1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_pos hp] at h5
  have h7 : Real.log (Real.log x) ≤ Real.log x ^ (1 / 10 : ℝ) / (|C| + 1) := by
    rw [← one_div_mul_eq_div]
    exact h5
  have h6 : Real.log (Real.log x) * (|C| + 1) ≤ Real.log x ^ (1 / 10 : ℝ) :=
    (le_div_iff₀ hc1).mp h7
  have h8 : Real.log (Real.log x) * C ≤ Real.log (Real.log x) * |C| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hLL0
  rw [Real.rpow_def_of_pos hL0]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The marked primes exceed `L^C` once `L^C < exp(L^{1/10})`: they are at least
`exp(L^{1/10})`. -/
theorem rpow_lt_of_mem_markPrimes {K : ℕ} (𝔞 : MarkingArray K) {x : ℝ}
    {P : ActiveGroupConstants} {𝔊 : ActiveGroups} (h : 𝔊.Admissible P x)
    (hL1 : 1 ≤ Real.log x) {C : ℝ}
    (hC : Real.log x ^ C < Real.exp (Real.log x ^ (1 / 10 : ℝ))) {p : ℕ}
    (hp : p ∈ markPrimes 𝔞 x 𝔊) : Real.log x ^ C < (p : ℝ) := by
  refine lt_of_lt_of_le hC ?_
  rcases (mem_markPrimes_iff 𝔞 x 𝔊).mp hp with ⟨i, hi⟩ | ⟨g, hg⟩
  · refine le_trans (Real.exp_le_exp.mpr ?_) (mem_bandPrimes.mp hi).2.1
    exact Real.rpow_le_rpow_of_exponent_le hL1 (𝔞.gt_tenth i).le
  · rcases g with i | j
    · refine le_trans (Real.exp_le_exp.mpr ?_) (h.small_range i p hg).1
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    · refine le_trans (Real.exp_le_exp.mpr ?_) (h.big_range j p hg).1
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)

/-! ### Elementary inequalities -/

/-- `(m (u + v))² ≤ 2 m² u² + 2 m² v²`. -/
theorem sq_mul_add_le_two_mul (m u v : ℝ) :
    (m * (u + v)) ^ 2 ≤ 2 * m ^ 2 * u ^ 2 + 2 * m ^ 2 * v ^ 2 := by
  have e : 2 * m ^ 2 * u ^ 2 + 2 * m ^ 2 * v ^ 2 = (m * (u + v)) ^ 2 + (m * (u - v)) ^ 2 := by
    ring
  rw [e]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- `|z + w|² ≤ 2|z|² + 2|w|²`. -/
theorem normSq_add_le_two_mul (z w : ℂ) : ‖z + w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h1 : ‖z + w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2
  have e : 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 = (‖z‖ + ‖w‖) ^ 2 + (‖z‖ - ‖w‖) ^ 2 := by ring
  rw [e]
  exact h1.trans (le_add_of_nonneg_right (sq_nonneg _))

/-- `E L^{2C₈} η² ≤ L^{-A}` when `E η ≤ 1` and `η L^{2C₈ + A} ≤ 1`: a small error `η` pays for
the number `E` of exceptional cells and for the log powers. -/
theorem mul_sq_mul_sq_le_rpow_neg {L C₈ A E η : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (h1 : E * η ≤ 1) (h2 : η * L ^ (2 * C₈ + A) ≤ 1) :
    E * ((L ^ C₈) ^ 2 * η ^ 2) ≤ L ^ (-A) := by
  have hLnA : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL.le _
  have e1 : L ^ (2 * C₈ + A) = (L ^ C₈) ^ 2 * L ^ A := by
    have e : 2 * C₈ + A = C₈ + C₈ + A := by ring
    rw [e, Real.rpow_add hL (C₈ + C₈) A, Real.rpow_add hL C₈ C₈]
    ring
  have e2 : L ^ (-A) * L ^ A = 1 := by
    rw [← Real.rpow_add hL (-A) A, neg_add_cancel, Real.rpow_zero]
  have h4 : 0 ≤ η * L ^ (2 * C₈ + A) := mul_nonneg hη (Real.rpow_nonneg hL.le _)
  have h5 : E * η * (η * L ^ (2 * C₈ + A)) ≤ 1 :=
    calc E * η * (η * L ^ (2 * C₈ + A)) ≤ 1 * 1 := mul_le_mul h1 h2 h4 zero_le_one
      _ = 1 := one_mul 1
  calc E * ((L ^ C₈) ^ 2 * η ^ 2)
      = E * ((L ^ C₈) ^ 2 * η ^ 2) * (L ^ (-A) * L ^ A) := by rw [e2, mul_one]
    _ = E * η * (η * ((L ^ C₈) ^ 2 * L ^ A)) * L ^ (-A) := by ring
    _ = E * η * (η * L ^ (2 * C₈ + A)) * L ^ (-A) := by rw [e1]
    _ ≤ 1 * L ^ (-A) := mul_le_mul_of_nonneg_right h5 hLnA
    _ = L ^ (-A) := one_mul _

/-- `L^{2C₈} L^{-B'} ≤ L^{-A}` when `A + 2C₈ ≤ B'` and `L ≥ 1`. -/
theorem sq_rpow_mul_rpow_neg_le {L C₈ A B' : ℝ} (hL : 1 ≤ L) (h : A + 2 * C₈ ≤ B') :
    (L ^ C₈) ^ 2 * L ^ (-B') ≤ L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have e : (L ^ C₈) ^ 2 * L ^ (-B') = L ^ (C₈ + C₈ + -B') := by
    rw [Real.rpow_add hL0 (C₈ + C₈) (-B'), Real.rpow_add hL0 C₈ C₈]
    ring
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-! ### Integrals and mean squares -/

/-- `t ↦ t^{-2}` is continuous on a set without `0`. -/
theorem continuousOn_inv_sq {s : Set ℝ} (h : ∀ t ∈ s, t ≠ 0) :
    ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) s :=
  ContinuousOn.inv₀ (f := fun t : ℝ => t ^ 2) (continuous_pow 2).continuousOn
    fun t ht => pow_ne_zero 2 (h t ht)

/-- Linearity of the integral for three continuous terms. -/
theorem integral_three_terms {f₁ f₂ f₃ : ℝ → ℝ} {a b : ℝ} (c₁ c₂ c₃ : ℝ) (hab : a ≤ b)
    (h₁ : ContinuousOn f₁ (Set.Icc a b)) (h₂ : ContinuousOn f₂ (Set.Icc a b))
    (h₃ : ContinuousOn f₃ (Set.Icc a b)) :
    ∫ t in a..b, (c₁ * f₁ t + c₂ * f₂ t + c₃ * f₃ t) =
      c₁ * (∫ t in a..b, f₁ t) + c₂ * (∫ t in a..b, f₂ t) + c₃ * ∫ t in a..b, f₃ t := by
  have i₁ : IntervalIntegrable (fun t => c₁ * f₁ t) MeasureTheory.volume a b :=
    (ContinuousOn.intervalIntegrable_of_Icc hab h₁).const_mul c₁
  have i₂ : IntervalIntegrable (fun t => c₂ * f₂ t) MeasureTheory.volume a b :=
    (ContinuousOn.intervalIntegrable_of_Icc hab h₂).const_mul c₂
  have i₃ : IntervalIntegrable (fun t => c₃ * f₃ t) MeasureTheory.volume a b :=
    (ContinuousOn.intervalIntegrable_of_Icc hab h₃).const_mul c₃
  have e1 : ∫ t in a..b, (c₁ * f₁ t + c₂ * f₂ t + c₃ * f₃ t) =
      (∫ t in a..b, (c₁ * f₁ t + c₂ * f₂ t)) + ∫ t in a..b, c₃ * f₃ t :=
    intervalIntegral.integral_add (i₁.add i₂) i₃
  have e2 : ∫ t in a..b, (c₁ * f₁ t + c₂ * f₂ t) =
      (∫ t in a..b, c₁ * f₁ t) + ∫ t in a..b, c₂ * f₂ t :=
    intervalIntegral.integral_add i₁ i₂
  have e3 : ∀ (c : ℝ) (f : ℝ → ℝ), ∫ t in a..b, c * f t = c * ∫ t in a..b, f t := fun c f =>
    intervalIntegral.integral_const_mul c f
  rw [e1, e2, e3 c₁ f₁, e3 c₂ f₂, e3 c₃ f₃]

/-- The mean square of a sequence on `[R₀, ρ R₀]` from its dyadic mean squares
`∑_{R ≤ n ≤ 2R} |E_n|² ≤ M R B` (`R ≥ 1`): at most `R₀ 2^{⌈ρ⌉ + 1} |M| B`. -/
theorem sum_normSq_natIcc_le_of_model (E : ℕ → ℂ) {R₀ ρ M B : ℝ} (hR₀ : 1 ≤ R₀) (hB : 0 ≤ B)
    (h : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ natIcc R (2 * R), ‖E n‖ ^ 2 ≤ M * R * B) :
    ∑ n ∈ natIcc R₀ (ρ * R₀), ‖E n‖ ^ 2 ≤ R₀ * (2 ^ (⌈ρ⌉₊ + 1) * (|M| * B)) := by
  have hR0 : 0 < R₀ := by linarith
  have hMB : 0 ≤ |M| * B := mul_nonneg (abs_nonneg M) hB
  have hrR : ρ * R₀ ≤ 2 ^ ⌈ρ⌉₊ * R₀ := by
    have h1 : ρ ≤ (⌈ρ⌉₊ : ℝ) := Nat.le_ceil ρ
    have h2 : (⌈ρ⌉₊ : ℝ) ≤ (2 : ℝ) ^ ⌈ρ⌉₊ := by
      exact_mod_cast (Nat.lt_two_pow_self : ⌈ρ⌉₊ < 2 ^ ⌈ρ⌉₊).le
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hR0.le
  have hsq : ∑ n ∈ natIcc R₀ (ρ * R₀), ‖E n‖ ^ 2 ≤ 2 ^ (⌈ρ⌉₊ + 1) * (|M| * B * R₀) :=
    sum_normSq_natIcc_le_of_dyadic E hR0 (mul_nonneg hMB hR0.le) _ (fun j _ => by
      have hj1 : (1 : ℝ) ≤ 2 ^ j * R₀ :=
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ 2 ^ j * R₀ :=
              mul_le_mul (one_le_pow₀ one_le_two) hR₀ zero_le_one (pow_nonneg zero_le_two j)
      have hj0 : (0 : ℝ) ≤ 2 ^ j * R₀ := by linarith
      calc ∑ n ∈ natIcc (2 ^ j * R₀) (2 * (2 ^ j * R₀)), ‖E n‖ ^ 2
          ≤ M * (2 ^ j * R₀) * B := h _ hj1
        _ = M * (2 ^ j * R₀ * B) := by ring
        _ ≤ |M| * (2 ^ j * R₀ * B) :=
            mul_le_mul_of_nonneg_right (le_abs_self M) (mul_nonneg hj0 hB)
        _ = 2 ^ j * (|M| * B * R₀) := by ring) hrR
  calc ∑ n ∈ natIcc R₀ (ρ * R₀), ‖E n‖ ^ 2 ≤ 2 ^ (⌈ρ⌉₊ + 1) * (|M| * B * R₀) := hsq
    _ = R₀ * (2 ^ (⌈ρ⌉₊ + 1) * (|M| * B)) := by ring

/-- **The mean-value theorem on a range `[R₀, ρ R₀] ⊆ [1, x²]`** and an interval of times of
length `≤ R₀` ((cor:length-dominates-time)): `∫_a^b |R_0^{-1} ∑ c_n n^{it}|² dt ≤ (1 + 12ρ) L S`
when `∑ |c_n|² ≤ R₀ S`. -/
theorem integral_normSq_normPoly_natIcc_le {R₀ ρ x S : ℝ} (hR₀ : 0 < R₀) (hρ : 1 ≤ ρ)
    (hx : 1 < x) (hL1 : 1 ≤ Real.log x) (hup : ρ * R₀ ≤ x ^ (2 : ℝ)) (c : ℕ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (hlen : b - a ≤ R₀)
    (hS : ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2 ≤ R₀ * S) :
    ∫ t in a..b, ‖normPoly R₀ (natIcc R₀ (ρ * R₀)) c t‖ ^ 2 ≤
      (1 + 12 * ρ) * Real.log x * S := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hρR0 : 0 ≤ ρ * R₀ := mul_nonneg (by linarith) hR₀.le
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ, W = ⌊ρ * R₀⌋₊ := ⟨_, rfl⟩
  have hWle : (W : ℝ) ≤ ρ * R₀ := by
    rw [hWdef]
    exact Nat.floor_le hρR0
  have hWx2 : (W : ℝ) ≤ x ^ (2 : ℝ) := hWle.trans hup
  have hsub : natIcc R₀ (ρ * R₀) ⊆ Finset.Icc 1 W := by
    intro n hn
    have h1 := (mem_natIcc_of_pos hR₀).mp hn
    have hn0 : n ≠ 0 := ne_zero_of_mem_natIcc hR₀ hn
    rw [hWdef]
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_floor h1.2⟩
  have hlogW : Real.log (W : ℝ) ≤ 2 * Real.log x := by
    by_cases hW0 : W = 0
    · rw [hW0, Nat.cast_zero, Real.log_zero]
      linarith
    · have hWpos : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hW0)
      have h1 := Real.log_le_log hWpos hWx2
      rw [Real.log_rpow hx0] at h1
      exact h1
  have hlogW0 : 0 ≤ Real.log (W : ℝ) := Real.log_natCast_nonneg W
  have h2 := integral_normSq_normPoly_le (R := R₀) hsub c hab
  have h4 : (b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤
      R₀ * ((1 + 12 * ρ) * Real.log x) := by
    have h5 : 4 * (W : ℝ) * (1 + Real.log (W : ℝ)) ≤ 4 * (ρ * R₀) * (3 * Real.log x) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hWle (by norm_num)) (by linarith) (by linarith)
        (mul_nonneg (by norm_num) hρR0)
    have h6 : R₀ ≤ R₀ * Real.log x := le_mul_of_one_le_right hR₀.le hL1
    have e : R₀ * ((1 + 12 * ρ) * Real.log x) =
        R₀ * Real.log x + 4 * (ρ * R₀) * (3 * Real.log x) := by ring
    rw [e]
    linarith
  have h7 : 0 ≤ R₀ * ((1 + 12 * ρ) * Real.log x) :=
    mul_nonneg hR₀.le (mul_nonneg (by linarith) hL0.le)
  have hRR : (R₀ ^ 2)⁻¹ * (R₀ * R₀) = 1 := by
    rw [← pow_two]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hR₀.ne')
  calc ∫ t in a..b, ‖normPoly R₀ (natIcc R₀ (ρ * R₀)) c t‖ ^ 2
      ≤ (R₀ ^ 2)⁻¹ * (((b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
          ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2) := h2
    _ ≤ (R₀ ^ 2)⁻¹ * (R₀ * ((1 + 12 * ρ) * Real.log x) * (R₀ * S)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h4 hS (Finset.sum_nonneg fun n _ => sq_nonneg _) h7)
          (inv_nonneg.mpr (sq_nonneg _))
    _ = (1 + 12 * ρ) * Real.log x * S * ((R₀ ^ 2)⁻¹ * (R₀ * R₀)) := by ring
    _ = (1 + 12 * ρ) * Real.log x * S := by rw [hRR, mul_one]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

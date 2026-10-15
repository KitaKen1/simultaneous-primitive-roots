module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.BilinearFourierProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DirichletMeanSquare

/-!
# Tools for the arc energy

The elementary parts of the proof of `ArcEnergyLink d` (`[P-06:0530–0553]`,
`TwoSidedProof/ArcEnergyProof.lean`):

* real-variable facts: the width `H = Y / (x L^{C₆})` of the arcs and the time
  `T₀ = x L^{C₆ + 1}` (`arc_width`), the additive error (`additive_error_le`), the powers of `L`
  in the tail (`tail_power_le`), `Y ≤ x²` on the scales of (cor:comparison-scales)
  (`scale_le_sq`), and the arithmetic of the three pieces (`arc_final`);
* the coefficients `a_w = 𝒰(w) e(hw/k)` (`arcCoeff`): the Fourier sum on the arc at `h/k` is the
  Fourier sum of the `a_w` (`finsum_arc_eq_sum`), and the Mellin polynomial of the `a_w` is `Y`
  times the endpoint polynomial of (cor:SM) (`normSq_window_poly_eq`);
* Mellin polynomials on a window `s ⊆ [1, N]` are Dirichlet polynomials with a natural cutoff
  (`window_poly_eq`), with the mean value on an interval of length `Y`
  (`integral_window_poly_le`, from `Classical.integral_normSq_dirichletPolynomial_le_nat`);
* a comparison endpoint with cutoff supported in `[a₁, a₂]` is supported on `a₁ Y ≤ w ≤ a₂ Y`
  (`comparisonEndpoint_window`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-! ### Real-variable facts -/

/-- `e(x + y) = e(x) e(y)`. -/
theorem addChar_add (x y : ℝ) : addChar (x + y) = addChar x * addChar y := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The width `H = Y / (x L^{C₆})` of the arcs and the time `T₀ = x L^{C₆ + 1}`. -/
theorem arc_width {x L C₆ Y : ℝ} (hC₆ : 0 < C₆) (hx1 : 1 ≤ x) (hL1 : 1 < L) (hY0 : 0 < Y)
    (hT₀Y : x * L ^ (C₆ + 1) ≤ Y) :
    1 ≤ x * L ^ C₆ ∧ x ≤ x * L ^ C₆ ∧ 1 ≤ Y / (x * L ^ C₆) ∧ Y / (x * L ^ C₆) ≤ Y ∧
      L * Y ≤ Y / (x * L ^ C₆) * (x * L ^ (C₆ + 1)) ∧
      Y / (x * L ^ C₆) / Y = (x * L ^ C₆)⁻¹ ∧
      1 / (Y / (x * L ^ C₆)) = x * L ^ C₆ / Y ∧ 0 ≤ x * L ^ (C₆ + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < L := lt_trans one_pos hL1
  have hLC₆ : 1 ≤ L ^ C₆ := Real.one_le_rpow hL1.le hC₆.le
  have hq1 : 1 ≤ x * L ^ C₆ := one_le_mul_of_one_le_of_one_le hx1 hLC₆
  have hq0 : 0 < x * L ^ C₆ := lt_of_lt_of_le one_pos hq1
  have hT₀e : x * L ^ (C₆ + 1) = x * L ^ C₆ * L := by
    rw [Real.rpow_add_one hL0.ne' C₆, mul_assoc]
  have hqY : x * L ^ C₆ ≤ Y := by
    have h1 : x * L ^ C₆ * 1 ≤ x * L ^ C₆ * L := mul_le_mul_of_nonneg_left hL1.le hq0.le
    rw [mul_one] at h1
    have h2 : x * L ^ C₆ * L ≤ Y := by
      rw [← hT₀e]
      exact hT₀Y
    exact h1.trans h2
  have he : Y / (x * L ^ C₆) * (x * L ^ C₆ * L) = L * Y := by
    rw [← mul_assoc, div_mul_cancel₀ Y hq0.ne', mul_comm]
  have hΛ : L * Y = Y / (x * L ^ C₆) * (x * L ^ (C₆ + 1)) := by rw [hT₀e, he]
  have hρ : Y / (x * L ^ C₆) / Y = (x * L ^ C₆)⁻¹ := by
    rw [div_right_comm, div_self hY0.ne', one_div]
  exact ⟨hq1, le_mul_of_one_le_right hx0.le hLC₆, (one_le_div hq0).mpr hqY,
    div_le_self hY0.le hq1, le_of_eq hΛ, hρ, one_div_div _ _,
    mul_nonneg hx0.le (Real.rpow_nonneg hL0.le _)⟩

/-- The additive error of (cor:local-mellin): `q⁻² ∑ |a_w|² ≤ Y L^{-A}` for `q ≥ L^{A + C₅}`. -/
theorem additive_error_le {q L Y Sa A C₅ : ℝ} (hq1 : 1 ≤ q) (hL0 : 0 < L) (hY0 : 0 ≤ Y)
    (hSa : Sa ≤ Y * L ^ C₅) (hLq : L ^ (A + C₅) ≤ q) : (q⁻¹) ^ 2 * Sa ≤ Y * L ^ (-A) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq1
  have hLm0 : 0 ≤ L ^ (-A) := Real.rpow_nonneg hL0.le _
  have hq2 : L ^ (A + C₅) ≤ q ^ 2 := by
    have h1 : q ≤ q ^ 2 := by nlinarith
    exact hLq.trans h1
  have hC₅e : L ^ C₅ = L ^ (A + C₅) * L ^ (-A) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  have hqi : (q⁻¹) ^ 2 * q ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hq0.ne', one_pow]
  have h1 : (q⁻¹) ^ 2 * L ^ C₅ ≤ L ^ (-A) := by
    rw [hC₅e]
    calc (q⁻¹) ^ 2 * (L ^ (A + C₅) * L ^ (-A)) ≤ (q⁻¹) ^ 2 * (q ^ 2 * L ^ (-A)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq2 hLm0) (sq_nonneg _)
      _ = L ^ (-A) := by rw [← mul_assoc, hqi, one_mul]
  calc (q⁻¹) ^ 2 * Sa ≤ (q⁻¹) ^ 2 * (Y * L ^ C₅) :=
        mul_le_mul_of_nonneg_left hSa (sq_nonneg _)
    _ = Y * ((q⁻¹) ^ 2 * L ^ C₅) := by ring
    _ ≤ Y * L ^ (-A) := mul_le_mul_of_nonneg_left h1 hY0

/-- The powers of `L` in the tail: `L · L^{C₅} · L^{-(j-1)} ≤ L^{-A}` for `j - 1 ≥ A + C₅ + 3`. -/
theorem tail_power_le {L A C₅ : ℝ} {j : ℕ} (hL1 : 1 < L)
    (hjA : A + C₅ + 3 ≤ ((j - 1 : ℕ) : ℝ)) : L * L ^ C₅ * (L ^ (j - 1))⁻¹ ≤ L ^ (-A) := by
  have hL0 : 0 < L := lt_trans one_pos hL1
  have e : L * L ^ C₅ * (L ^ (j - 1))⁻¹ = L ^ (1 + C₅ + -(((j - 1 : ℕ) : ℝ))) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one, Real.rpow_neg hL0.le,
      Real.rpow_natCast]
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith)

/-- `Y ≤ x²` on the scales of (cor:comparison-scales), once `log L ≤ L^{.19}` and
`|c₂| ≤ L^{.35}`. -/
theorem scale_le_sq {x Y c₂ : ℝ} (hx0 : 0 < x) (hL1 : 1 < Real.log x)
    (hlogL : ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖)
    (hc₂L : |c₂| ≤ Real.log x ^ (0.35 : ℝ))
    (hY2 : Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))) :
    Y ≤ x ^ (2 : ℝ) := by
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1.le
  have hp19 : 0 ≤ Real.log x ^ (0.19 : ℝ) := Real.rpow_nonneg hL0.le _
  have hp46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlog19 : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ) := by
    have h' : ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ := hlogL
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0,
      abs_of_nonneg hp19] at h'
    exact h'
  have hEle : c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤ Real.log x := by
    have h1 : c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        |c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hp46) hLL0
    have h2 : |c₂| * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        Real.log x ^ (0.35 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc₂L hp46) hlog19 hLL0
        (mul_nonneg (Real.rpow_nonneg hL0.le _) hp46)
    have h3 : Real.log x ^ (0.35 : ℝ) * Real.log x ^ (0.46 : ℝ) * Real.log x ^ (0.19 : ℝ) =
        Real.log x := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      have e : (0.35 : ℝ) + 0.46 + 0.19 = 1 := by norm_num
      rw [e, Real.rpow_one]
    exact (h1.trans h2).trans (le_of_eq h3)
  have h1 : Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) ≤ x :=
    calc Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x))
        ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hEle
      _ = x := Real.exp_log hx0
  calc Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) := hY2
    _ ≤ x * x := mul_le_mul_of_nonneg_left h1 hx0.le
    _ = x ^ (2 : ℝ) := by rw [Real.rpow_two, sq]

/-- `L^E ≤ x` from the `o`-estimate `L^E = o(x)`. -/
theorem log_rpow_le_of_norm {x E : ℝ} (hx0 : 0 < x) (hL0 : 0 < Real.log x)
    (h : ‖Real.log x ^ E‖ ≤ 1 * ‖x ^ (1 : ℝ)‖) : Real.log x ^ E ≤ x := by
  rw [one_mul, Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), abs_of_pos hx0] at h
  exact h

/-- The arithmetic of the three pieces: the low times, the tail and the additive error. -/
theorem arc_final {CM ME Cs Y L Lm P Ki Iw Sa arc ρ : ℝ} (hY : 0 < Y) (hL : 1 ≤ L)
    (hLm : 0 ≤ Lm) (hP : 0 ≤ P) (hKi : 0 ≤ Ki) (hIw0 : 0 ≤ Iw) (hSa0 : 0 ≤ ρ ^ 2 * Sa)
    (harc : arc ≤ CM * (Y⁻¹ * Iw + ρ ^ 2 * Sa))
    (htail : Iw ≤ Y ^ 2 * (ME * Lm) + 2 * ((Y + Cs * Y * L) * (Y * P)) * Ki)
    (hT2 : ρ ^ 2 * Sa ≤ Y * Lm) (hpow : L * P * Ki ≤ Lm) :
    arc ≤ max CM 0 * (max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Lm := by
  have hYi : Y⁻¹ * Y = 1 := inv_mul_cancel₀ hY.ne'
  have hYi0 : 0 ≤ Y⁻¹ := inv_nonneg.mpr hY.le
  have h1 : Y⁻¹ * Iw ≤
      Y⁻¹ * (Y ^ 2 * (ME * Lm) + 2 * ((Y + Cs * Y * L) * (Y * P)) * Ki) :=
    mul_le_mul_of_nonneg_left htail hYi0
  have h2 : Y⁻¹ * (Y ^ 2 * (ME * Lm) + 2 * ((Y + Cs * Y * L) * (Y * P)) * Ki) =
      Y * ME * Lm + 2 * (1 + Cs * L) * Y * (P * Ki) := by
    linear_combination (Y * ME * Lm + 2 * (1 + Cs * L) * Y * (P * Ki)) * hYi
  have h3 : Y * ME * Lm ≤ Y * max ME 0 * Lm :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hY.le) hLm
  have h4 : 1 + Cs * L ≤ (1 + |Cs|) * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self Cs)) (by linarith : (0 : ℝ) ≤ L)]
  have hPK : 0 ≤ P * Ki := mul_nonneg hP hKi
  have h5 : 2 * (1 + Cs * L) * Y * (P * Ki) ≤ 2 * (1 + |Cs|) * Y * Lm := by
    have h6 : 2 * (1 + Cs * L) * Y * (P * Ki) ≤ 2 * ((1 + |Cs|) * L) * Y * (P * Ki) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h4 zero_le_two) hY.le) hPK
    have h7 : 2 * ((1 + |Cs|) * L) * Y * (P * Ki) = 2 * (1 + |Cs|) * Y * (L * P * Ki) := by
      ring
    have h8 : 2 * (1 + |Cs|) * Y * (L * P * Ki) ≤ 2 * (1 + |Cs|) * Y * Lm :=
      mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg zero_le_two (add_nonneg zero_le_one (abs_nonneg Cs))) hY.le)
    exact (h6.trans (le_of_eq h7)).trans h8
  have hX : Y⁻¹ * Iw + ρ ^ 2 * Sa ≤ (max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Lm := by
    have e : (max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Lm =
        Y * max ME 0 * Lm + 2 * (1 + |Cs|) * Y * Lm + Y * Lm := by ring
    rw [e]
    exact add_le_add ((h1.trans (le_of_eq h2)).trans (add_le_add h3 h5)) hT2
  have hX0 : 0 ≤ Y⁻¹ * Iw + ρ ^ 2 * Sa := add_nonneg (mul_nonneg hYi0 hIw0) hSa0
  calc arc ≤ CM * (Y⁻¹ * Iw + ρ ^ 2 * Sa) := harc
    _ ≤ max CM 0 * (Y⁻¹ * Iw + ρ ^ 2 * Sa) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hX0
    _ ≤ max CM 0 * ((max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Lm) :=
        mul_le_mul_of_nonneg_left hX (le_max_right _ _)
    _ = max CM 0 * (max ME 0 + 2 * (1 + |Cs|) + 1) * Y * Lm := by ring

/-! ### The coefficients `a_w = 𝒰(w) e(hw/k)` -/

/-- `a_w = 𝒰(w) e(hw/k)` (`[P-06:0530]`). -/
def arcCoeff (U : ℕ → ℂ) (n : ℤ) (k : ℕ) (w : ℕ) : ℂ :=
  U w * addChar ((n : ℝ) * (w : ℝ) / (k : ℝ))

theorem norm_arcCoeff (U : ℕ → ℂ) (n : ℤ) (k : ℕ) (w : ℕ) : ‖arcCoeff U n k w‖ = ‖U w‖ := by
  unfold arcCoeff
  rw [norm_mul, EndpointProof.norm_addChar, mul_one]

theorem arcCoeff_eq_zero {U : ℕ → ℂ} {w : ℕ} (h : U w = 0) (n : ℤ) (k : ℕ) :
    arcCoeff U n k w = 0 := by
  unfold arcCoeff
  rw [h, zero_mul]

/-- The Fourier sum on the arc at `h/k` is the Fourier sum of the coefficients `a_w`. -/
theorem finsum_arc_eq_sum {U : ℕ → ℂ} {s : Finset ℕ} (hUs : ∀ w : ℕ, U w ≠ 0 → w ∈ s) (n : ℤ)
    (k : ℕ) (β : ℝ) :
    ∑ᶠ w : ℕ, U w * addChar (((n : ℝ) / (k : ℝ) + β) * (w : ℝ)) =
      ∑ w ∈ s, arcCoeff U n k w * addChar (β * (w : ℝ)) := by
  have hsub : Function.support
      (fun w : ℕ => U w * addChar (((n : ℝ) / (k : ℝ) + β) * (w : ℝ))) ⊆ ↑s := by
    intro w hw
    rw [Function.mem_support] at hw
    exact Finset.mem_coe.mpr (hUs w fun h' => hw (by rw [h', zero_mul]))
  rw [finsum_eq_sum_of_support_subset _ hsub]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : ((n : ℝ) / (k : ℝ) + β) * (w : ℝ) =
      (n : ℝ) * (w : ℝ) / (k : ℝ) + β * (w : ℝ) := by ring
  unfold arcCoeff
  rw [e, addChar_add, mul_assoc]

/-- The sum of the squares of the coefficients is the sum of the squares of the sequence. -/
theorem sum_normSq_arcCoeff_eq {U : ℕ → ℂ} {N : ℕ} (hUN : ∀ w : ℕ, U w ≠ 0 → w ∈ Finset.Icc 1 N)
    (n : ℤ) (k : ℕ) :
    ∑ w ∈ Finset.Icc 1 N, ‖arcCoeff U n k w‖ ^ 2 = ∑ᶠ w : ℕ, ‖U w‖ ^ 2 := by
  have hsub : Function.support (fun w : ℕ => ‖U w‖ ^ 2) ⊆ ↑(Finset.Icc 1 N) := by
    intro w hw
    rw [Function.mem_support] at hw
    refine Finset.mem_coe.mpr (hUN w fun h' => hw ?_)
    rw [h', norm_zero]
    exact zero_pow two_ne_zero
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_congr rfl fun w _ => by rw [norm_arcCoeff]

/-- The Mellin polynomial of the coefficients is `Y` times the endpoint polynomial. -/
theorem normSq_window_poly_eq {U : ℕ → ℂ} {s : Finset ℕ} (hUs : ∀ w : ℕ, U w ≠ 0 → w ∈ s)
    {Y : ℝ} (hY0 : 0 < Y) (n : ℤ) (k : ℕ) (τ : ℝ) :
    ‖∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 =
      Y ^ 2 * ‖endpointPolynomial U Y n k τ‖ ^ 2 := by
  have hsum : ∑ w ∈ s, U w * addChar ((n : ℝ) * (w : ℝ) / (k : ℝ)) *
      (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
      ∑ w ∈ s, arcCoeff U n k w * (w : ℂ) ^ ((τ : ℂ) * Complex.I) := rfl
  rw [EndpointProof.endpointPolynomial_eq_sum hUs Y n k τ, hsum, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hY0.le, mul_pow, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hY0.ne', one_pow, one_mul]

section Window

variable {a : ℕ → ℂ} {s : Finset ℕ} {N : ℕ}

/-- A Mellin polynomial on a window is a Dirichlet polynomial with a natural cutoff. -/
theorem window_poly_eq (hsN : s ⊆ Finset.Icc 1 N) (ha0 : ∀ w, w ∉ s → a w = 0) (τ : ℝ) :
    ∑ w ∈ s, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I) = Classical.dirichletPolynomial a N τ := by
  have h1 : ∑ w ∈ s, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
      ∑ w ∈ Finset.Icc 1 N, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I) :=
    Finset.sum_subset hsN fun w _ hw => by rw [ha0 w hw, zero_mul]
  rw [h1]
  unfold Classical.dirichletPolynomial
  exact Finset.sum_congr rfl fun w _ => by rw [mul_comm (τ : ℂ) Complex.I]

theorem window_poly_fun_eq (hsN : s ⊆ Finset.Icc 1 N) (ha0 : ∀ w, w ∉ s → a w = 0) :
    (fun τ : ℝ => ‖∑ w ∈ s, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2) =
      fun τ : ℝ => ‖Classical.dirichletPolynomial a N τ‖ ^ 2 :=
  funext fun τ => by rw [window_poly_eq hsN ha0 τ]

theorem continuous_window_poly (hsN : s ⊆ Finset.Icc 1 N) (ha0 : ∀ w, w ∉ s → a w = 0) :
    Continuous fun τ : ℝ => ‖∑ w ∈ s, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 := by
  rw [window_poly_fun_eq hsN ha0]
  exact (Classical.continuous_dirichletPolynomial a N).norm.pow 2

/-- The mean square of a Mellin polynomial on a window over an interval of length `Y`. -/
theorem integral_window_poly_le (hsN : s ⊆ Finset.Icc 1 N) (ha0 : ∀ w, w ∉ s → a w = 0)
    {Y : ℝ} (hY : 0 ≤ Y) (T : ℝ) :
    ∫ τ in T..(T + Y), ‖∑ w ∈ s, a w * (w : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 ≤
      (Y + 4 * (N : ℝ) * (1 + Real.log (N : ℝ))) * ∑ w ∈ Finset.Icc 1 N, ‖a w‖ ^ 2 := by
  have h1 := Classical.integral_normSq_dirichletPolynomial_le_nat a N (a := T) (b := T + Y)
    (le_add_of_nonneg_right hY)
  rw [← window_poly_fun_eq hsN ha0] at h1
  have e : T + Y - T = Y := by ring
  rw [e] at h1
  exact h1

end Window

/-- A comparison endpoint with cutoff supported in `[a₁, a₂]` at a positive scale `Y` is
supported on `a₁ Y ≤ w ≤ a₂ Y`. -/
theorem comparisonEndpoint_window (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ)
    (𝔊 : ActiveGroups) {d : ℕ} (S : Fin d → Finset ℕ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) {ψ₁ : ℝ → ℂ} {a₁ a₂ : ℝ}
    (hsupp : Function.support ψ₁ ⊆ Set.Icc a₁ a₂) (σ : ℝ) {Y : ℝ} (hY : 0 < Y) (w : ℕ)
    (hw : comparisonEndpoint q q₀ 𝔞 x 𝔊 S t test ψ₁ σ Y w ≠ 0) :
    a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y := by
  have hψw : ψ₁ ((w : ℝ) / Y) ≠ 0 := by
    intro h'
    apply hw
    unfold comparisonEndpoint
    rw [h', zero_mul, zero_mul, zero_mul]
  have hmem : (w : ℝ) / Y ∈ Set.Icc a₁ a₂ := hsupp hψw
  exact ⟨(le_div_iff₀ hY).mp hmem.1, (div_le_iff₀ hY).mp hmem.2⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

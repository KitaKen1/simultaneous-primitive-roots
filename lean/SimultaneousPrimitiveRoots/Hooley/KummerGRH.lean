module

public import SimultaneousPrimitiveRoots.Hooley.CyclotomicSqrtRange
public import SimultaneousPrimitiveRoots.KummerContourFromGrowth
public import SimultaneousPrimitiveRoots.GaussianPrimePowerCounting

/-!
# `MainClaim` from GRH for the Kummer quotients

For a base `a` and a prime `q > a`, let `K = ℚ(ζ_q, a^(1/q))` and `E = ℚ(ζ_q)`. The project's
finite-contour machinery turns three analytic data for the quotient `ζ_K / ζ_E`

* an entire continuation `H`,
* a growth bound on circles, uniform in `q`,
* a zero condition: non-real zeros of height at most `2q²` have real part at most `1 - δ`,

into a bound for the Gaussian prime-power trace of `K` (`KummerEntireGrowthGapInputs`).
Here the zero condition is taken with `δ = 1/2`, which is what GRH for these Hecke L-functions
gives. Combined with the unconditional bound for `Θ_E` up to `q ≤ √x / log⁴ x`
(`Hooley.CyclotomicSqrtRange`), this yields the splitting estimate in Hooley's range, and hence
`MainClaim` by `mainClaim_of_grhSplittingUpTo`.

The continuation and growth are classical (Hecke; Phragmén–Lindelöf). The zero condition at
`δ = 1/2` is the generalized Riemann hypothesis for the Hecke L-functions in `ζ_K / ζ_E`. None of
the three is proved here: they are the hypothesis `KummerGRH`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter
noncomputable section

/-- **GRH for the Kummer quotients of the base `a`.** For every prime `q > a`, the quotient
`ζ_K / ζ_{ℚ(ζ_q)}` with `K = ℚ(ζ_q, a^(1/q))` has an entire continuation with the uniform growth
bound of `KummerEntireGrowthGapInputs`, and its non-real zeros of height at most `2q²` have real
part at most `1/2`. -/
def KummerGRH (a : ℕ) (C : ℝ) : Prop :=
  ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerEntireGrowthGapInputs a q (1 / 2) C

/-- `log (2q) / log x ≤ log² (q x)` once `x ≥ e`. -/
theorem log_two_mul_div_le_log_sq {q : ℕ} (hq : q.Prime) {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.log (2 * (q : ℝ)) / Real.log x ≤ Real.log ((q : ℝ) * x) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL1 : 1 ≤ Real.log x := one_le_log_of_exp_one_le hx
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hx2 : (2 : ℝ) ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hl2q : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have h1 : Real.log (2 * (q : ℝ)) / Real.log x ≤ Real.log (2 * (q : ℝ)) :=
    div_le_self hl2q hL1
  have h2 : Real.log (2 * (q : ℝ)) ≤ Real.log ((q : ℝ) * x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hqx1 : 1 ≤ Real.log ((q : ℝ) * x) := by
    calc (1 : ℝ) ≤ Real.log x := hL1
      _ ≤ Real.log ((q : ℝ) * x) := Real.log_le_log hx0 (by nlinarith)
  have h3 : Real.log ((q : ℝ) * x) ≤ Real.log ((q : ℝ) * x) ^ 2 := by nlinarith
  linarith

/-- **GRH for the Kummer quotients gives the splitting estimate in Hooley's range.** -/
theorem grhSplittingBoundUpTo_of_kummerGRH {a : ℕ} (ha : 2 ≤ a) {C : ℝ} (hC : 0 ≤ C)
    (h : KummerGRH a C) : ∃ D : ℝ, 0 ≤ D ∧ GRHSplittingBoundUpTo a D := by
  obtain ⟨CE, hCE, hcyc⟩ := exists_cyclotomicGaussian_le_sqrtRange
  have hR0 : 0 ≤ kummerGaussianLeftAverageConstant C + 1 := by
    linarith [kummerGaussianLeftAverageConstant_nonneg hC]
  refine ⟨gaussianFiniteContourCountingConstant CE C (kummerGaussianLeftAverageConstant C + 1),
    gaussianFiniteContourCountingConstant_nonneg hCE hC hR0, ?_⟩
  filter_upwards [hcyc, eventually_ge_atTop (Real.exp 1)] with x hcx hxe
  intro q hq haq hcut
  letI : Fact (2 ≤ a) := ⟨ha⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : Fact (a < q) := ⟨haq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hx2 : (2 : ℝ) ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hi := kummerFiniteContourUpperInputs_of_boundary_growth (x := x) hx1 hC
    (h q ha hq haq)
  have hbase : gaussianPrimePowerTrace (CyclotomicField q ℚ) x ≤ CE * x := hcx q hq hcut
  have htrace := primeKummerGaussianTrace_bound_of_finite_contour hx1
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hCE hC hR0 hi hbase
  have hcount := powerResidueException_count_bound_of_primePowerTrace
    (by linarith : (1 : ℝ) < x) htrace
  set D := gaussianFiniteContourCountingConstant CE C (kummerGaussianLeftAverageConstant C + 1)
    with hD
  have hD0 : 0 ≤ D := gaussianFiniteContourCountingConstant_nonneg hCE hC hR0
  have hsqrt : x ^ (1 - 1 / 2 : ℝ) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  have hlog := log_two_mul_div_le_log_sq hq hxe
  have herr : D * x ^ (1 - 1 / 2 : ℝ) * Real.log (2 * (q : ℝ)) / Real.log x ≤
      D * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 := by
    rw [hsqrt]
    have hs0 : 0 ≤ D * Real.sqrt x := mul_nonneg hD0 (Real.sqrt_nonneg x)
    calc D * Real.sqrt x * Real.log (2 * (q : ℝ)) / Real.log x
        = D * Real.sqrt x * (Real.log (2 * (q : ℝ)) / Real.log x) := by ring
      _ ≤ D * Real.sqrt x * Real.log ((q : ℝ) * x) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog hs0
  linarith

/-- **`MainClaim` from GRH for the Kummer quotients.** If every base `a ≥ 2` satisfies
`KummerGRH a C` for some `C`, then every admissible set has a positive dyadic lower bound.
Neither candidate supply nor a zero-free strip of fixed width is assumed; the hypothesis is the
generalized Riemann hypothesis for the Hecke L-functions of the Kummer fields, together with
their classical continuation and growth. -/
theorem mainClaim_of_kummerGRH
    (h : ∀ a : ℕ, 2 ≤ a → ∃ C : ℝ, 0 ≤ C ∧ KummerGRH a C) : MainClaim := by
  apply mainClaim_of_grhSplittingUpTo
  intro a ha
  obtain ⟨C, hC, hK⟩ := h a ha
  exact grhSplittingBoundUpTo_of_kummerGRH ha hC hK

end
end SimultaneousPrimitiveRoots

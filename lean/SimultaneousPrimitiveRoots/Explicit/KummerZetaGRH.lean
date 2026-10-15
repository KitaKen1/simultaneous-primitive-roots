module

public import SimultaneousPrimitiveRoots.Explicit.KummerContourFromGrowth
public import SimultaneousPrimitiveRoots.Hooley.KummerGRH
public import SimultaneousPrimitiveRoots.Hecke.KummerGrowth

/-!
# `MainClaim` from GRH for the Dedekind zeta functions of the Kummer fields (step D7)

For a base `a` and a prime `q > a` let `K = ℚ(ζ_q, a^{1/q})` and `F_K(s) = (s - 1) ζ_K(s)`.

* Continuation and growth of `F_K` are **proved** (Hecke's theta method, steps D1–D4:
  `Hecke.dedekindZetaEntire`, `Hecke.primeKummer_dedekindZetaEntire_le_sphere`).
* The finite-contour machinery of the project runs on `F_K` itself through the abstract
  hypothesis `EntireZeroData` (`Explicit/`); the pole of `ζ_K` at `1` contributes the main term
  `M(x) ≤ ŵ(1) x` in place of the cyclotomic trace (`Hecke.gaussianMainTerm_le`).
* The only remaining hypothesis is the location of the zeros, `KummerZetaGRH a`: every
  non-real zero of `F_K` in the critical strip with `|Im ρ| ≤ 2q²` has `Re ρ ≤ 1/2` — the
  generalized Riemann hypothesis for `ζ_K`, at bounded height.

`mainClaim_of_kummerZetaGRH`: if `KummerZetaGRH a` holds for every base `a ≥ 2`, then
`MainClaim`. Compared with `mainClaim_of_kummerGRH`, neither the entireness of the quotient
`ζ_K / ζ_{ℚ(ζ_q)}` (Aramata–Brauer) nor its growth is assumed, and the unconditional cyclotomic
input `exists_cyclotomicGaussian_le_sqrtRange` is not needed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Filter
noncomputable section

/-- **GRH for the Dedekind zeta functions of the Kummer fields of base `a`** (at height
`≤ 2q²`): every non-real zero `ρ` of `(s - 1) ζ_K(s)`, `K = ℚ(ζ_q, a^{1/q})`, in the critical
strip with `|Im ρ| ≤ 2q²` has `Re ρ ≤ 1/2`. -/
def KummerZetaGRH (a : ℕ) : Prop :=
  ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    ∀ i : fullQuotientZeroIndex (Hecke.dedekindZetaEntire (PrimeKummerField a q)),
      (fullQuotientIndexedZero _ i).im ≠ 0 →
      |(fullQuotientIndexedZero _ i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero _ i).re ≤ 1 / 2

/-- The growth constant of `F_K` for the base `a` (from `Hecke.primeKummer_dedekindZetaEntire_le_sphere`). -/
def kummerZetaGrowthConstant (a : ℕ) : ℝ := 320 * (3 + Real.log a / Real.log 2)

theorem kummerZetaGrowthConstant_nonneg (a : ℕ) : 0 ≤ kummerZetaGrowthConstant a := by
  unfold kummerZetaGrowthConstant
  have : 0 ≤ Real.log a / Real.log 2 :=
    div_nonneg (Real.log_natCast_nonneg a) (Real.log_nonneg (by norm_num))
  positivity

/-- Under `KummerZetaGRH`, `F_K` supplies all the analytic inputs of the finite-contour
machinery: entire zero data, growth on the contour circles, and the zero gap `δ = 1/2`. -/
theorem kummerEntireGrowthGapInputs_of_zetaGRH {a q : ℕ} [ha : Fact (2 ≤ a)]
    [hq : Fact q.Prime] [haq : Fact (a < q)] (h : KummerZetaGRH a) :
    KummerEntireGrowthGapInputs a q (1 / 2) (kummerZetaGrowthConstant a) := by
  refine ⟨Hecke.dedekindZetaEntire (PrimeKummerField a q),
    dedekindZetaEntire_entireZeroData _ _, fun U hU z hz => ?_, fun i him hle => ?_⟩
  · exact Hecke.primeKummer_dedekindZetaEntire_le_sphere a q hU hz
  · have := h q ha.out hq.out haq.out i him hle
    linarith

/-- **GRH for `ζ_K` gives the splitting estimate in Hooley's range.** -/
theorem grhSplittingBoundUpTo_of_kummerZetaGRH {a : ℕ} (ha : 2 ≤ a) (h : KummerZetaGRH a) :
    ∃ D : ℝ, 0 ≤ D ∧ GRHSplittingBoundUpTo a D := by
  set C : ℝ := kummerZetaGrowthConstant a with hCdef
  have hC : 0 ≤ C := kummerZetaGrowthConstant_nonneg a
  have hCE : 0 ≤ Hecke.gaussianMainConstant := Hecke.gaussianMainConstant_pos.le
  have hR0 : 0 ≤ kummerGaussianLeftAverageConstant C + 1 := by
    linarith [kummerGaussianLeftAverageConstant_nonneg hC]
  refine ⟨gaussianFiniteContourCountingConstant Hecke.gaussianMainConstant C
      (kummerGaussianLeftAverageConstant C + 1),
    gaussianFiniteContourCountingConstant_nonneg hCE hC hR0, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hxe
  intro q hq haq _hcut
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  have hx2 : (2 : ℝ) ≤ x := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hi := kummerFiniteContourUpperInputs_of_boundary_growth (x := x) hx1 hC
    (kummerEntireGrowthGapInputs_of_zetaGRH (a := a) (q := q) h)
  have htrace := primeKummerGaussianTrace_bound_of_finite_contour hx1
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hCE hC hR0 hi le_rfl
  have hcount := powerResidueException_count_bound_of_primePowerTrace
    (by linarith : (1 : ℝ) < x) htrace
  set D := gaussianFiniteContourCountingConstant Hecke.gaussianMainConstant C
    (kummerGaussianLeftAverageConstant C + 1) with hD
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

/-- **`MainClaim` from GRH for the Dedekind zeta functions of the Kummer fields.** If for
every base `a ≥ 2` and every prime `q > a`, the non-real zeros of `ζ_K`,
`K = ℚ(ζ_q, a^{1/q})`, of height at most `2q²` lie on or left of `Re s = 1/2`, then every
admissible set has a positive dyadic lower bound. Continuation and growth of `ζ_K` are proved,
not assumed. -/
theorem mainClaim_of_kummerZetaGRH (h : ∀ a : ℕ, 2 ≤ a → KummerZetaGRH a) : MainClaim := by
  apply mainClaim_of_grhSplittingUpTo
  intro a ha
  exact grhSplittingBoundUpTo_of_kummerZetaGRH ha (h a ha)

/-- **The generalized Riemann hypothesis for `ζ_K`**, stated for the continuation
`F_K(s) = (s - 1) ζ_K(s)` (`Hecke.dedekindZetaEntire`; Mathlib's `dedekindZeta` is only the
Dirichlet series): every zero in the open critical strip `0 < Re s < 1` has `Re s = 1/2`. -/
def DedekindZetaGRH (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ ρ : ℂ, Hecke.dedekindZetaEntire K ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2

/-- GRH for the Kummer fields of base `a` implies `KummerZetaGRH a`. -/
theorem kummerZetaGRH_of_dedekindZetaGRH {a : ℕ}
    (h : ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      DedekindZetaGRH (PrimeKummerField a q)) :
    KummerZetaGRH a := by
  intro q ha hq haq
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  intro i _him _hle
  have hz := fullQuotientIndexedZero_is_zero _ i
  obtain ⟨h0, h1⟩ := fullQuotientIndexedZero_strip _ i
  set ρ := fullQuotientIndexedZero (Hecke.dedekindZetaEntire (PrimeKummerField a q)) i
  rcases h0.lt_or_eq with h0 | h0
  · rcases h1.lt_or_eq with h1 | h1
    · exact (h q ha hq haq ρ hz h0 h1).le
    · exact absurd hz (Hecke.dedekindZetaEntire_ne_zero _ h1.ge)
  · rw [← h0]
    norm_num

/-- **`MainClaim` from GRH for the Dedekind zeta functions of the Kummer fields
`ℚ(ζ_q, a^{1/q})`** (`a ≥ 2`, `q > a` prime). -/
theorem mainClaim_of_dedekindZetaGRH
    (h : ∀ a q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      DedekindZetaGRH (PrimeKummerField a q)) : MainClaim :=
  mainClaim_of_kummerZetaGRH fun a _ => kummerZetaGRH_of_dedekindZetaGRH (h a)

/-- **Per set:** for an admissible `A`, GRH for the Dedekind zeta functions of the Kummer fields
`ℚ(ζ_q, a^{1/q})` with `a ∈ A` (all primes `q > a`) gives the positive lower density for `A`. -/
theorem positiveDyadicLowerBound_of_dedekindZetaGRH {A : Finset ℕ} (hA : Admissible A)
    (h : ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      DedekindZetaGRH (PrimeKummerField a q)) :
    PositiveDyadicLowerBound A := by
  classical
  have hD : ∀ a ∈ A, ∃ D : ℝ, 0 ≤ D ∧ GRHSplittingBoundUpTo a D := fun a haA =>
    grhSplittingBoundUpTo_of_kummerZetaGRH (hA.2.1 a haA)
      (kummerZetaGRH_of_dedekindZetaGRH (h a haA))
  choose! c hc0 hc using hD
  refine positiveDyadicLowerBound_of_grhSplittingUpTo hA (C := ∑ a ∈ A, c a)
    (Finset.sum_nonneg fun a ha => hc0 a ha) ?_
  intro a ha
  apply (hc a ha).mono
  exact Finset.single_le_sum (fun b hb => hc0 b hb) ha

/-- **GRH ⇒ `MainClaim`**: the generalized Riemann hypothesis for the Dedekind zeta functions of
all number fields implies the positive lower density of simultaneous primitive roots. -/
theorem mainClaim_of_GRH
    (h : ∀ (K : Type) [Field K] [NumberField K], DedekindZetaGRH K) : MainClaim :=
  mainClaim_of_dedekindZetaGRH fun a q ha hq haq => by
    let : Fact (2 ≤ a) := ⟨ha⟩
    let : Fact q.Prime := ⟨hq⟩
    let : Fact (a < q) := ⟨haq⟩
    exact h (PrimeKummerField a q)

end
end SimultaneousPrimitiveRoots.Explicit

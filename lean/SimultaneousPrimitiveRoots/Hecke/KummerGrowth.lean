module

public import SimultaneousPrimitiveRoots.Hecke.GrowthBound
public import SimultaneousPrimitiveRoots.KummerAbsoluteDiscriminant
public import SimultaneousPrimitiveRoots.NumberFieldZetaContinuation
public import Mathlib.Analysis.Complex.Convex

/-!
# D4 for the Kummer fields `ℚ(ζ_q, a^{1/q})`

* `dedekindZetaEntire_eqOn_normalizedZeta`: the entire function `dedekindZetaEntire K` agrees with
  the project's `numberFieldNormalizedZeta K` (TauCeti's continuation to `Re s > 1 - 1/n`) on its
  whole domain, so it is *the* entire continuation of the normalized zeta.
* `primeKummer_complexity_le`: `n + log |d_K| ≤ (3 + log a / log 2) q (q - 1) log (2q)`, from the
  project's discriminant bound `primeKummer_log_discriminant_le`.
* `primeKummer_normalizedZeta_entire_growth`: for a finite set `A` of bases there is one constant
  `C` such that for every `a ∈ A` and prime `q > a` the normalized zeta `(s - 1) ζ_K(s)` of
  `K = ℚ(ζ_q, a^{1/q})` has an entire continuation with
  `‖F(z)‖ ≤ exp (C q (q - 1) log (2q) (U + 3)²)` on the circles `|z - 2| = 2(U + 2)`.

This is the continuation-and-growth half of `KummerEntireGrowthGapInputs`, proved for `ζ_K`
itself rather than for the quotient `ζ_K / ζ_{ℚ(ζ_q)}` (whose entireness would need
Aramata–Brauer).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Module Metric Filter
open scoped Topology

/-- `dedekindZetaEntire K` is the analytic continuation of `numberFieldNormalizedZeta K`. -/
theorem dedekindZetaEntire_eqOn_normalizedZeta (K : Type*) [Field K] [NumberField K] :
    Set.EqOn (dedekindZetaEntire K) (numberFieldNormalizedZeta K)
      (numberFieldZetaContinuationDomain K) := by
  have hU := numberFieldZetaContinuationDomain_isOpen K
  have hconv : Convex ℝ (numberFieldZetaContinuationDomain K) :=
    convex_halfSpace_re_gt (1 - 1 / (finrank ℚ K : ℝ))
  have hF : AnalyticOnNhd ℂ (dedekindZetaEntire K) (numberFieldZetaContinuationDomain K) :=
    fun z _ => (differentiable_dedekindZetaEntire K).analyticAt z
  have hG : AnalyticOnNhd ℂ (numberFieldNormalizedZeta K) (numberFieldZetaContinuationDomain K) :=
    (numberFieldNormalizedZeta_differentiableOn K).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ numberFieldZetaContinuationDomain K :=
    numberFieldZetaContinuationDomain_mem K (by norm_num)
  refine hF.eqOn_of_preconnected_of_eventuallyEq hG hconv.isPreconnected h2 ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with s hs
  rw [dedekindZetaEntire_eq_mul K hs, numberFieldNormalizedZeta_eq K hs]

theorem abs_discr_eq_natAbs (K : Type*) [Field K] [NumberField K] :
    |((discr K : ℤ) : ℝ)| = ((discr K).natAbs : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- `n + log |d_K| ≤ (3 + log a / log 2) q (q - 1) log (2q)` for `K = ℚ(ζ_q, a^{1/q})`. -/
theorem primeKummer_complexity_le (a q : ℕ) [ha : Fact (2 ≤ a)] [hq : Fact q.Prime]
    [haq : Fact (a < q)] :
    (finrank ℚ (PrimeKummerField a q) : ℝ) + Real.log |((discr (PrimeKummerField a q) : ℤ) : ℝ)| ≤
      (3 + Real.log a / Real.log 2) * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)) := by
  have hdeg := primeKummerField_absolute_degree ha.out hq.out haq.out
  have hdisc := primeKummer_log_discriminant_le a q
  rw [abs_discr_eq_natAbs]
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hlog : 1 ≤ Real.log (2 * (q : ℝ)) := by
    have he : Real.exp 1 ≤ 2 * (q : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * (q : ℝ)) := Real.log_le_log (Real.exp_pos 1) he
  have hn : (finrank ℚ (PrimeKummerField a q) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
    rw [hdeg]
    push_cast [Nat.cast_sub hq.out.one_le]
    ring
  rw [hn]
  have hd : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) := by nlinarith
  have := mul_le_mul_of_nonneg_left hlog hd
  nlinarith

/-- The same with the constant `kummerDiscriminantConstant A + 1`, uniform over `a ∈ A`. -/
theorem primeKummer_complexity_le_uniform (A : Finset ℕ) {a q : ℕ} (haA : a ∈ A)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (finrank ℚ (PrimeKummerField a q) : ℝ) + Real.log |((discr (PrimeKummerField a q) : ℤ) : ℝ)| ≤
      (kummerDiscriminantConstant A + 1) * ((q : ℝ) * ((q : ℝ) - 1)) *
        Real.log (2 * (q : ℝ)) := by
  have hdeg := primeKummerField_absolute_degree ha.out hq.out haq.out
  have hdisc := primeKummer_log_discriminant_uniform A haA (a := a) (q := q)
  rw [abs_discr_eq_natAbs]
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hlog : 1 ≤ Real.log (2 * (q : ℝ)) := by
    have he : Real.exp 1 ≤ 2 * (q : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * (q : ℝ)) := Real.log_le_log (Real.exp_pos 1) he
  have hn : (finrank ℚ (PrimeKummerField a q) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
    rw [hdeg]
    push_cast [Nat.cast_sub hq.out.one_le]
    ring
  rw [hn]
  have hd : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) := by nlinarith
  have := mul_le_mul_of_nonneg_left hlog hd
  nlinarith

/-- **D4 for one Kummer field:** on the circles `|z - 2| = 2(U + 2)`,
`‖(z - 1) ζ_K(z)‖ ≤ exp (320 (3 + log a / log 2) q (q - 1) log (2q) (U + 3)²)`. -/
theorem primeKummer_dedekindZetaEntire_le_sphere (a q : ℕ) [Fact (2 ≤ a)] [Fact q.Prime]
    [Fact (a < q)] {U : ℝ} (hU : 0 ≤ U) {z : ℂ} (hz : z ∈ sphere (2 : ℂ) (2 * (U + 2))) :
    ‖dedekindZetaEntire (PrimeKummerField a q) z‖ ≤
      Real.exp (320 * (3 + Real.log a / Real.log 2) * (q : ℝ) * ((q : ℝ) - 1) *
        Real.log (2 * (q : ℝ)) * (U + 3) ^ 2) := by
  refine (norm_dedekindZetaEntire_le_sphere _ hU hz).trans (Real.exp_le_exp.mpr ?_)
  have h := primeKummer_complexity_le a q
  have hU3 : 0 ≤ (U + 3) ^ 2 := sq_nonneg _
  calc 320 * ((finrank ℚ (PrimeKummerField a q) : ℝ) +
        Real.log |((discr (PrimeKummerField a q) : ℤ) : ℝ)|) * (U + 3) ^ 2
      ≤ 320 * ((3 + Real.log a / Real.log 2) * ((q : ℝ) * ((q : ℝ) - 1)) *
          Real.log (2 * (q : ℝ))) * (U + 3) ^ 2 := by gcongr
    _ = _ := by ring

/-- **Continuation and growth of the normalized Kummer zetas, uniformly in `q`.** For a finite
set `A` of bases there is `C ≥ 0` such that for every `a ∈ A`, prime `q > a` and
`K = ℚ(ζ_q, a^{1/q})`, the normalized zeta `numberFieldNormalizedZeta K = (s - 1) ζ_K(s)` has an
entire continuation `F` with `‖F z‖ ≤ exp (C q (q - 1) log (2q) (U + 3)²)` on the circles
`|z - 2| = 2(U + 2)`. -/
theorem primeKummer_normalizedZeta_entire_growth (A : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Set.univ ∧
        Set.EqOn F (numberFieldNormalizedZeta (PrimeKummerField a q))
          (numberFieldZetaContinuationDomain (PrimeKummerField a q)) ∧
        (∀ s : ℂ, 1 < s.re → F s = (s - 1) * dedekindZeta (PrimeKummerField a q) s) ∧
        ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
          ‖F z‖ ≤ Real.exp (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2) := by
  refine ⟨320 * (kummerDiscriminantConstant A + 1), by
    have := kummerDiscriminantConstant_nonneg A
    positivity, fun a haA q ha hq haq => ?_⟩
  let : Fact (2 ≤ a) := ⟨ha⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  refine ⟨dedekindZetaEntire (PrimeKummerField a q),
    fun z _ => (differentiable_dedekindZetaEntire _).analyticAt z,
    dedekindZetaEntire_eqOn_normalizedZeta _, fun s hs => dedekindZetaEntire_eq_mul _ hs,
    fun U hU z hz => ?_⟩
  refine (norm_dedekindZetaEntire_le_sphere _ hU hz).trans (Real.exp_le_exp.mpr ?_)
  have h := primeKummer_complexity_le_uniform A haA (a := a) (q := q)
  have hU3 : 0 ≤ (U + 3) ^ 2 := sq_nonneg _
  calc 320 * ((finrank ℚ (PrimeKummerField a q) : ℝ) +
        Real.log |((discr (PrimeKummerField a q) : ℤ) : ℝ)|) * (U + 3) ^ 2
      ≤ 320 * ((kummerDiscriminantConstant A + 1) * ((q : ℝ) * ((q : ℝ) - 1)) *
          Real.log (2 * (q : ℝ))) * (U + 3) ^ 2 := by gcongr
    _ = _ := by ring

end SimultaneousPrimitiveRoots.Hecke

end

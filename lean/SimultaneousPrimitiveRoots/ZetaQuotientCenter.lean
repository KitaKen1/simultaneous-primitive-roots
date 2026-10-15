module

public import SimultaneousPrimitiveRoots.ZetaQuotientMultiplicity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
public import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Metric
open Classical
noncomputable section

/-- The actual real Euler logarithm at two. A coarse degree bound suffices for
the Jensen center; no estimate of the class-number residue is needed. -/
def numberFieldEulerLogTwo (K : Type*) [Field K] [NumberField K] : ℝ :=
  ∑' P : HeightOneSpectrum (𝓞 K),
    -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)))

theorem numberFieldEulerLogTwo_summable (K : Type*) [Field K] [NumberField K] :
    Summable (fun P : HeightOneSpectrum (𝓞 K) =>
      -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)))) :=
  TauCeti.summable_neg_log_one_sub_absNorm_rpow (by norm_num)

theorem numberFieldEulerLogTwo_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ numberFieldEulerLogTwo K := by
  apply tsum_nonneg
  intro P
  have hu : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by positivity
  have hh := P.absNorm_rpow_neg_le_half (by norm_num : (1 : ℝ) ≤ 2)
  have hp : 0 < 1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by linarith
  linarith [Real.log_le_sub_one_of_pos hp]

theorem numberFieldEulerLogTwo_le_four_degree (K : Type*) [Field K] [NumberField K] :
    numberFieldEulerLogTwo K ≤ 4 * (Module.finrank ℚ K : ℝ) := by
  have hs := TauCeti.summable_absNorm_rpow_primes_of_one_lt
    (K := K) (by norm_num : (1 : ℝ) < 2)
  have hle : numberFieldEulerLogTwo K ≤
      ∑' P : HeightOneSpectrum (𝓞 K),
        2 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by
    apply (numberFieldEulerLogTwo_summable K).tsum_le_tsum _ (hs.mul_left 2)
    intro P
    have hu : 0 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 : ℝ)) := by positivity
    have hh := P.absNorm_rpow_neg_le_half (by norm_num : (1 : ℝ) ≤ 2)
    nlinarith [Real.neg_log_one_sub_le_add_two_mul_sq hu hh]
  rw [tsum_mul_left] at hle
  have hb := TauCeti.tsum_absNorm_rpow_neg_two_le (K := K)
  linarith

theorem numberField_dedekindZeta_two_eq_exp (K : Type*) [Field K] [NumberField K] :
    dedekindZeta K 2 = (Real.exp (numberFieldEulerLogTwo K) : ℂ) := by
  simpa [numberFieldEulerLogTwo] using
    TauCeti.dedekindZeta_ofReal_eq_exp_tsum_neg_log_one_sub
      (K := K) (by norm_num : (1 : ℝ) < 2)

theorem numberField_dedekindZeta_two_norm_eq_exp (K : Type*) [Field K] [NumberField K] :
    ‖dedekindZeta K 2‖ = Real.exp (numberFieldEulerLogTwo K) := by
  rw [numberField_dedekindZeta_two_eq_exp]
  simp

theorem numberField_dedekindZeta_two_norm_one_le (K : Type*) [Field K] [NumberField K] :
    1 ≤ ‖dedekindZeta K 2‖ := by
  rw [numberField_dedekindZeta_two_norm_eq_exp]
  simpa using Real.exp_le_exp.mpr (numberFieldEulerLogTwo_nonneg K)

theorem numberField_dedekindZeta_two_norm_le_exp_degree (K : Type*)
    [Field K] [NumberField K] :
    ‖dedekindZeta K 2‖ ≤ Real.exp (4 * (Module.finrank ℚ K : ℝ)) := by
  rw [numberField_dedekindZeta_two_norm_eq_exp]
  exact Real.exp_le_exp.mpr (numberFieldEulerLogTwo_le_four_degree K)

theorem numberFieldNormalizedZeta_at_two (K : Type*) [Field K] [NumberField K] :
    numberFieldNormalizedZeta K 2 = dedekindZeta K 2 := by
  rw [numberFieldNormalizedZeta_eq K (by norm_num)]
  norm_num

/-- The only field degree in the lower center bound is that of the denominator. -/
theorem numberFieldFullQuotientContinuation_log_norm_two_lower (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H) :
    -(4 * (Module.finrank ℚ L : ℝ)) ≤ Real.log ‖H 2‖ := by
  rw [hH.2 2 (by norm_num), numberFieldNormalizedZeta_at_two,
    numberFieldNormalizedZeta_at_two, norm_div,
    numberField_dedekindZeta_two_norm_eq_exp, numberField_dedekindZeta_two_norm_eq_exp,
    Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  linarith [numberFieldEulerLogTwo_nonneg K, numberFieldEulerLogTwo_le_four_degree L]

theorem numberFieldFullQuotientContinuation_norm_two_lower (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldFullQuotientContinuation K L H) :
    Real.exp (-(4 * (Module.finrank ℚ L : ℝ))) ≤ ‖H 2‖ := by
  have hp : 0 < ‖H 2‖ := norm_pos_iff.mpr
    (numberFieldFullQuotientContinuation_ne_zero_two K L hH)
  simpa only [Real.exp_log hp] using
    Real.exp_le_exp.mpr (numberFieldFullQuotientContinuation_log_norm_two_lower K L hH)

/-- The center term is now bounded unconditionally in the field degree. The
actual entire extension and its boundary norm bound remain required inputs. -/
theorem numberFieldEntireFullQuotientContinuation_jensen_degree_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) |R|, ‖H z‖ ≤ M) :
    (((∑ᶠ s : ℂ, if s ∈ closedBall (2 : ℂ) |r|
      then (fullQuotientZeroMultiplicity H s : ℤ) else 0) : ℤ) : ℝ) ≤
        (Real.log M + 4 * (Module.finrank ℚ L : ℝ)) / Real.log (R / r) := by
  have hc := numberFieldFullQuotientContinuation_log_norm_two_lower K L
    (numberFieldEntireFullQuotientContinuation_positive K L hH)
  have hp : 0 < ‖H 2‖ := norm_pos_iff.mpr
    (numberFieldFullQuotientContinuation_ne_zero_two K L
      (numberFieldEntireFullQuotientContinuation_positive K L hH))
  have hden : 0 < Real.log (R / r) := by
    rw [← Real.log_abs]
    apply Real.log_pos
    rw [abs_div]
    exact (lt_div_iff₀ hr).mpr (by simpa using hrR)
  apply (numberFieldEntireFullQuotientContinuation_jensen_multiplicity_le K L hH hr hrR hM hb).trans
  apply div_le_div_of_nonneg_right _ hden.le
  rw [Real.log_div (by linarith : M ≠ 0) hp.ne']
  linarith

end
end SimultaneousPrimitiveRoots

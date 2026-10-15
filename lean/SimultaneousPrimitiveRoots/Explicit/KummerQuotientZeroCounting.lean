module

public import SimultaneousPrimitiveRoots.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting

/-! Generalization of `SimultaneousPrimitiveRoots.KummerQuotientZeroCounting` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Classical
noncomputable section

/-- A uniform family boundary coefficient C yields a uniform Gaussian mass
constant. The actual entire extension and quantified boundary growth are
explicit inputs; Gaussian summability and its raw mass are derived. -/
theorem kummerEntireFullQuotientContinuation_gaussianMass_of_boundary_growth
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (T + 3) ^ 2)) :
    Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientZeroIndex H,
        Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤
          kummerGaussianZeroMassConstant C *
            (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hq0 : 0 ≤ (q : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by positivity
  have hm := numberFieldEntireFullQuotientContinuation_gaussianMass_of_boundary_growth
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH hB hb
  refine ⟨hm.1, hm.2.trans ?_⟩
  rw [prime_cyclotomic_degree (E := CyclotomicField q ℚ) hq.out,
    Nat.cast_sub hq.out.one_lt.le, Nat.cast_one]
  have hcost : 4 * ((q : ℝ) - 1) ≤
      4 * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left (prime_mul_log_twice_one_le hq.out)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hq0)
    nlinarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (add_le_add_left hcost
      (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))) hl.le)
    gaussianZeroCountingConstant_nonneg
  rw [add_comm (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)))
    (4 * ((q : ℝ) - 1))]
  apply hn.trans_eq
  unfold kummerGaussianZeroMassConstant
  ring

theorem kummerFullQuotientGaussianUpperInputs_of_boundary_growth {a q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] {H : ℂ → ℂ}
    (hH : EntireZeroData
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x δ R : ℝ} (hC : 0 ≤ C)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (T + 3) ^ 2))
    (hg : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ)
    (hf : primeKummerGaussianFullSignedTrace a q x ≤
      artinGaussianZeroRemainder (fullQuotientIndexedZero H) x / ((q : ℝ) - 1) +
        R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    Countable (fullQuotientZeroIndex H) ∧
      KummerFullQuotientGaussianUpperInputs a q x δ (kummerGaussianZeroMassConstant C) R := by
  have hm := kummerEntireFullQuotientContinuation_gaussianMass_of_boundary_growth hH hC hb
  exact kummerFullQuotientGaussianUpperInputs_of_indexed_zeros hH hm.1 hm.2 hg hf

end
end SimultaneousPrimitiveRoots.Explicit

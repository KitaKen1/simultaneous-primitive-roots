module

public import SimultaneousPrimitiveRoots.GaussianZeroCounting

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

def kummerGaussianZeroMassConstant (C : ℝ) : ℝ :=
  ((C + 4) / Real.log 2) * gaussianZeroCountingConstant

theorem kummerGaussianZeroMassConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ kummerGaussianZeroMassConstant C := by
  unfold kummerGaussianZeroMassConstant
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_nonneg (div_nonneg (by linarith) hl.le) gaussianZeroCountingConstant_nonneg

theorem prime_mul_log_twice_one_le {q : ℕ} (hq : q.Prime) :
    1 ≤ (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hx : 0 < 2 * (q : ℝ) := by positivity
  have hlog : 1 - (2 * (q : ℝ))⁻¹ ≤ Real.log (2 * (q : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at h
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog hq0.le
  have heq : (q : ℝ) * (2 * (q : ℝ))⁻¹ = 1 / 2 := by field_simp
  nlinarith

/-- A uniform family boundary coefficient C yields a uniform Gaussian mass
constant. The actual entire extension and quantified boundary growth are
explicit inputs; Gaussian summability and its raw mass are derived. -/
theorem kummerEntireFullQuotientContinuation_gaussianMass_of_boundary_growth
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
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
    (hH : NumberFieldEntireFullQuotientContinuation
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
end SimultaneousPrimitiveRoots

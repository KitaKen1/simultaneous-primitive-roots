module

public import SimultaneousPrimitiveRoots.GaussianLeftZeroBounds
public import SimultaneousPrimitiveRoots.KummerQuotientZeroCounting

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- A uniform family boundary coefficient C yields a uniform Gaussian mass
constant. The actual entire extension and quantified boundary growth are
explicit inputs; Gaussian summability and its raw mass are derived. -/
theorem kummerEntireFullQuotientContinuation_leftGaussianMass_of_boundary_growth
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (T + 3) ^ 2)) :
    Summable (fun i : fullQuotientLeftZeroIndex H =>
      Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientLeftZeroIndex H,
        Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)) ≤
          (2 * kummerGaussianZeroMassConstant C) *
            (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hq0 : 0 ≤ (q : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) := by positivity
  have hm := numberFieldEntireFullQuotientContinuation_leftGaussianMass_of_boundary_growth
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
  calc
    2 * ((C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) +
        4 * ((q : ℝ) - 1)) / Real.log 2) * gaussianZeroCountingConstant =
        2 * (((C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) +
        4 * ((q : ℝ) - 1)) / Real.log 2) * gaussianZeroCountingConstant) := by ring
    _ ≤ 2 * (((C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) +
        4 * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ))) / Real.log 2) *
        gaussianZeroCountingConstant) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [add_comm] using hn
    _ = _ := by unfold kummerGaussianZeroMassConstant; ring

/-- For x >= 1, every finite set of actual negative-strip zeros has a uniform
O(q log(2q)) signed contribution after division by q-1. -/
theorem kummerEntireFullQuotientContinuation_leftFiniteSignedSum_le
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (T + 3) ^ 2))
    (S : Finset {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}) :
    (∑ s ∈ S, ((-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
      artinGaussianZeroTerm x s).re) ≤
      (2 * artinGaussianConstant * kummerGaussianZeroMassConstant C) *
        (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hm := kummerEntireFullQuotientContinuation_leftGaussianMass_of_boundary_growth hH hC hb
  have hs := fullQuotientLeftZeros_finite_signed_sum_le hx hd hm.1 S
  simp only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one] at hs
  apply hs.trans
  have hp : 0 ≤ artinGaussianConstant / ((q : ℝ) - 1) :=
    div_nonneg artinGaussianConstant_pos.le hd.le
  calc
    _ ≤ (artinGaussianConstant / ((q : ℝ) - 1)) *
        ((2 * kummerGaussianZeroMassConstant C) * (q : ℝ) * ((q : ℝ) - 1) *
          Real.log (2 * (q : ℝ))) := mul_le_mul_of_nonneg_left hm.2 hp
    _ = _ := by field_simp

end
end SimultaneousPrimitiveRoots

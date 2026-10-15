module

public import SimultaneousPrimitiveRoots.GaussianFixedHeight

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

def gaussianFixedHeightCountingConstant (CE M R : ℝ) : ℝ :=
  CE + 4 * artinGaussianConstant * M + (artinGaussianConstant * M + R)

theorem gaussianFixedHeightCountingConstant_nonneg {CE M R : ℝ}
    (hCE : 0 ≤ CE) (hM : 0 ≤ M) (hR : 0 ≤ R) :
    0 ≤ gaussianFixedHeightCountingConstant CE M R := by
  unfold gaussianFixedHeightCountingConstant
  have := artinGaussianConstant_pos
  positivity

/-- The fixed-height hypothesis is independent of x. The actual explicit
formula, nonnegative zero multiplicities, mass and trace decomposition
remain hypotheses; their analytic existence is not asserted here. -/
theorem gaussianPrimePowerTrace_fixed_height_bound {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x δ CE M R E L : ℝ} (hx : 1 ≤ x) (hδ1 : δ ≤ 1)
    (hCE : 0 ≤ CE) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ M * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ)
    (hformula : L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hE : E ≤ CE * x)
    (hfactor : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤ E + ((q : ℝ) - 1) * L) :
    let C := gaussianFixedHeightCountingConstant CE M R
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
  let CL := artinGaussianConstant * M + R
  have hCL : 0 ≤ CL := add_nonneg (mul_nonneg artinGaussianConstant_pos.le hM) hR
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hq1 : 0 ≤ (q : ℝ) - 1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hL := gaussianHeckeTrace_fixed_height_upper_bound ρ hx hδ1 hq.out.one_le hM hR
    hstrip hw hmass hlow hformula
  have ht := gaussian_q_height_tail_le (q := (q : ℝ)) (by linarith : (1 : ℝ) ≤ q)
  have hhigh : ((q : ℝ) - 1) *
      (artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
        Real.exp (-(q : ℝ) ^ 4 / 2)) ≤ 4 * artinGaussianConstant * M * x := by
    calc
      _ = (artinGaussianConstant * M * x) *
          (((q : ℝ) - 1) * (q : ℝ) * Real.log (2 * (q : ℝ)) *
            Real.exp (-(q : ℝ) ^ 4 / 2)) := by ring
      _ ≤ (artinGaussianConstant * M * x) *
          ((q : ℝ) ^ 2 * Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by have := artinGaussianConstant_pos; positivity)
        gcongr
        nlinarith
      _ ≤ (artinGaussianConstant * M * x) * 4 :=
        mul_le_mul_of_nonneg_left ht (by have := artinGaussianConstant_pos; positivity)
      _ = _ := by ring
  have htrace : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      (CE + 4 * artinGaussianConstant * M) * x +
        CL * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
    calc
      _ ≤ CE * x + ((q : ℝ) - 1) *
          (CL * x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ)) +
            artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
              Real.exp (-(q : ℝ) ^ 4 / 2)) :=
        hfactor.trans (add_le_add hE (mul_le_mul_of_nonneg_left hL hq1))
      _ = CE * x +
          CL * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) +
          ((q : ℝ) - 1) *
            (artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
              Real.exp (-(q : ℝ) ^ 4 / 2)) := by ring
      _ ≤ _ := by nlinarith [hhigh]
  apply htrace.trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCL) hx0
  · have hleading : 0 ≤ CE + 4 * artinGaussianConstant * M := by
      have := artinGaussianConstant_pos
      positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hleading)
          (mul_nonneg (Nat.cast_nonneg q) hq1)) (Real.rpow_nonneg hx0 _)) hlog

theorem powerResidueException_count_bound_of_fixed_height {ι : Type*} (ρ : ι → ℂ)
    {a q : ℕ} [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x δ CE M R E L : ℝ} (hx : 1 < x) (hδ1 : δ ≤ 1)
    (hCE : 0 ≤ CE) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ M * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ)
    (hformula : L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hE : E ≤ CE * x)
    (hfactor : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤ E + ((q : ℝ) - 1) * L) :
    let C := gaussianFixedHeightCountingConstant CE M R
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x :=
  powerResidueException_count_bound_of_primePowerTrace hx
    (gaussianPrimePowerTrace_fixed_height_bound ρ hx.le hδ1 hCE hM hR
      hstrip hw hmass hlow hformula hE hfactor)

end
end SimultaneousPrimitiveRoots

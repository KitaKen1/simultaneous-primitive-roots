module

public import SimultaneousPrimitiveRoots.GaussianPrimePowerCounting

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

/-- Keep the high-zero Gaussian tail separate instead of requiring a
height depending on log x. -/
theorem gaussian_fixed_height_tail_le {T γ : ℝ} (hT : 0 ≤ T) (hγ : T ≤ |γ|) :
    Real.exp (-γ ^ 2 / 4) ≤ Real.exp (-T ^ 2 / 8) * Real.exp (-γ ^ 2 / 8) := by
  have hs : T ^ 2 ≤ γ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hT (abs_nonneg γ)).mpr hγ
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem artinGaussianZeroTerm_norm_le_fixed_height {x δ T : ℝ} {ρ : ℂ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hσ0 : 0 ≤ ρ.re) (hσ1 : ρ.re ≤ 1)
    (hgap : ρ.re ≤ 1 - δ ∨ T ≤ |ρ.im|) :
    ‖artinGaussianZeroTerm x ρ‖ ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        Real.exp (-ρ.im ^ 2 / 8) := by
  have hx0 : 0 < x := by linarith
  have hC := artinGaussianConstant_pos
  rcases hgap with hlow | hhigh
  · have h := artinGaussianZeroTerm_norm_le_of_gap_or_height hx hσ0 hσ1
      (δ := δ) (Or.inl hlow)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hx0.le (Real.exp_pos _).le)) hC.le)
      (Real.exp_pos _).le)
  · have hpow : x ^ ρ.re ≤ x := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx hσ1
    calc
      _ ≤ artinGaussianConstant * x ^ ρ.re * Real.exp (-ρ.im ^ 2 / 4) :=
        artinGaussianZeroTerm_norm_le (by linarith) hσ0 hσ1
      _ ≤ artinGaussianConstant * x *
          (Real.exp (-T ^ 2 / 8) * Real.exp (-ρ.im ^ 2 / 8)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow artinGaussianConstant_pos.le)
          (gaussian_fixed_height_tail_le hT hhigh) (Real.exp_pos _).le
          (by have := artinGaussianConstant_pos; positivity)
      _ ≤ _ := by
        have hp : 0 ≤ x ^ (1 - δ) := Real.rpow_nonneg hx0.le _
        calc
          _ = (artinGaussianConstant * (x * Real.exp (-T ^ 2 / 8))) *
              Real.exp (-ρ.im ^ 2 / 8) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hp) hC.le)
            (Real.exp_pos _).le

/-- The zero list may repeat entries to encode nonnegative multiplicities.
Real zeros are discarded before taking absolute values. -/
theorem artinGaussianZeroRemainder_le_fixed_height {ι : Type*} (ρ : ι → ℂ)
    {x δ T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ T → (ρ i).re ≤ 1 - δ) :
    artinGaussianZeroRemainder ρ x ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        ∑' i, Real.exp (-(ρ i).im ^ 2 / 8) := by
  unfold artinGaussianZeroRemainder
  rw [← hw.tsum_mul_left]
  apply (artinGaussianZeroRemainder_summable ρ hx hstrip hw).tsum_le_tsum _ (hw.mul_left _)
  intro i
  by_cases hr : (ρ i).im = 0
  · have hz := artinGaussianZeroTerm_real_nonneg (by linarith : 0 < x) hr
    have hp : 0 ≤ (artinGaussianConstant *
        (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) * Real.exp (-(ρ i).im ^ 2 / 8) := by
      have := artinGaussianConstant_pos
      positivity
    linarith
  · have hg : (ρ i).re ≤ 1 - δ ∨ T ≤ |(ρ i).im| := by
      by_cases ht : |(ρ i).im| ≤ T
      · exact Or.inl (hlow i hr ht)
      · exact Or.inr (le_of_not_ge ht)
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (artinGaussianZeroTerm_norm_le_fixed_height hx hT (hstrip i).1 (hstrip i).2 hg))

/-- The polynomial loss from the actual degree is absorbed uniformly in q.
The constant is deliberately coarse. -/
theorem gaussian_q_height_tail_le {q : ℝ} (hq : 1 ≤ q) :
    q ^ 2 * Real.log (2 * q) * Real.exp (-q ^ 4 / 2) ≤ 4 := by
  have hq0 : 0 < q := by linarith
  have hlog : Real.log (2 * q) ≤ 2 * q := Real.log_le_self (by positivity)
  have he : q ^ 4 / 2 ≤ Real.exp (q ^ 4 / 2) := by
    linarith [Real.add_one_le_exp (q ^ 4 / 2)]
  have hprod : (q ^ 4 / 2) * Real.exp (-q ^ 4 / 2) ≤ 1 := by
    calc
      _ ≤ Real.exp (q ^ 4 / 2) * Real.exp (-q ^ 4 / 2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpow : q ^ 3 ≤ q ^ 4 := by
    calc
      q ^ 3 ≤ q ^ 3 * q := le_mul_of_one_le_right (by positivity) hq
      _ = q ^ 4 := by ring
  calc
    _ ≤ q ^ 2 * (2 * q) * Real.exp (-q ^ 4 / 2) := by gcongr
    _ = 2 * (q ^ 3 * Real.exp (-q ^ 4 / 2)) := by ring
    _ ≤ 2 * (q ^ 4 * Real.exp (-q ^ 4 / 2)) := by gcongr
    _ ≤ 4 := by nlinarith

theorem gaussianHeckeTrace_fixed_height_upper_bound {ι : Type*} (ρ : ι → ℂ)
    {x δ M R L : ℝ} {q : ℕ} (hx : 1 ≤ x) (hδ1 : δ ≤ 1) (hq : 1 ≤ q)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hmass : (∑' i, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ M * (q : ℝ) * Real.log (2 * (q : ℝ)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ 2 * (q : ℝ) ^ 2 → (ρ i).re ≤ 1 - δ)
    (hformula : L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    L ≤ (artinGaussianConstant * M + R) * x ^ (1 - δ) *
          (q : ℝ) * Real.log (2 * (q : ℝ)) +
        artinGaussianConstant * M * x * (q : ℝ) * Real.log (2 * (q : ℝ)) *
          Real.exp (-(q : ℝ) ^ 4 / 2) := by
  have hrem := artinGaussianZeroRemainder_le_fixed_height ρ hx
    (T := 2 * (q : ℝ) ^ 2) (by positivity) hstrip hw hlow
  have heq : -(2 * (q : ℝ) ^ 2) ^ 2 / 8 = -(q : ℝ) ^ 4 / 2 := by ring
  rw [heq] at hrem
  have hp : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * q)
  calc
    L ≤ artinGaussianZeroRemainder ρ x + R * (q : ℝ) * Real.log (2 * (q : ℝ)) := hformula
    _ ≤ (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-(q : ℝ) ^ 4 / 2))) *
          (M * (q : ℝ) * Real.log (2 * (q : ℝ))) +
        (R * (q : ℝ) * Real.log (2 * (q : ℝ))) * x ^ (1 - δ) := by
      apply add_le_add
      · exact hrem.trans (mul_le_mul_of_nonneg_left hmass
          (by have := artinGaussianConstant_pos; positivity))
      · exact le_mul_of_one_le_right (by positivity) hp
    _ = _ := by ring

end
end SimultaneousPrimitiveRoots

module

public import SimultaneousPrimitiveRoots.GaussianWeight
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

def artinGaussianConstant : ℝ := Real.sqrt Real.pi * Real.exp ((Real.log 2) ^ 2 + 1 / 4)

def artinGaussianZeroTerm (x : ℝ) (ρ : ℂ) : ℂ := (x : ℂ) ^ ρ * artinGaussianMellin ρ

/-- The minus sign is essential: the real zero terms may be discarded only for
an upper bound. No actual Hecke zero enumeration is asserted here. -/
def artinGaussianZeroRemainder {ι : Type*} (ρ : ι → ℂ) (x : ℝ) : ℝ :=
  ∑' i, -(artinGaussianZeroTerm x (ρ i)).re

theorem artinGaussianConstant_pos : 0 < artinGaussianConstant := by
  exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.exp_pos _)

theorem gaussian_high_tail_le {x δ γ : ℝ} (hx : 0 < x) (hheight : 8 * δ * Real.log x ≤ γ ^ 2) :
    x * Real.exp (-γ ^ 2 / 4) ≤ x ^ (1 - δ) * Real.exp (-γ ^ 2 / 8) := by
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  calc
    x * Real.exp (-γ ^ 2 / 4) = Real.exp (Real.log x + (-γ ^ 2 / 4)) := by
      rw [Real.exp_add, Real.exp_log hx]
    _ ≤ Real.exp (Real.log x * (1 - δ) + (-γ ^ 2 / 8)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem artinGaussianZeroTerm_norm_le {x : ℝ} {ρ : ℂ} (hx : 0 < x)
    (hσ0 : 0 ≤ ρ.re) (hσ1 : ρ.re ≤ 1) :
    ‖artinGaussianZeroTerm x ρ‖ ≤ artinGaussianConstant * x ^ ρ.re * Real.exp (-ρ.im ^ 2 / 4) := by
  unfold artinGaussianZeroTerm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have h := mul_le_mul_of_nonneg_left (artinGaussianMellin_norm_le hσ0 hσ1)
    (Real.rpow_nonneg hx.le ρ.re)
  simpa only [artinGaussianConstant, mul_assoc, mul_comm, mul_left_comm] using h

theorem artinGaussianZeroTerm_norm_le_half_weight {x : ℝ} {ρ : ℂ}
    (hx : 1 ≤ x) (hσ0 : 0 ≤ ρ.re) (hσ1 : ρ.re ≤ 1) :
    ‖artinGaussianZeroTerm x ρ‖ ≤
      (artinGaussianConstant * x) * Real.exp (-ρ.im ^ 2 / 8) := by
  have hpow : x ^ ρ.re ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx hσ1
  have hweight : Real.exp (-ρ.im ^ 2 / 4) ≤ Real.exp (-ρ.im ^ 2 / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ρ.im]
  calc
    _ ≤ artinGaussianConstant * x ^ ρ.re * Real.exp (-ρ.im ^ 2 / 4) :=
      artinGaussianZeroTerm_norm_le (by linarith) hσ0 hσ1
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow artinGaussianConstant_pos.le)
      hweight (Real.exp_pos _).le (by have := artinGaussianConstant_pos; positivity)

theorem artinGaussianZeroTerm_norm_le_of_gap_or_height {x δ : ℝ} {ρ : ℂ}
    (hx : 1 ≤ x) (hσ0 : 0 ≤ ρ.re) (hσ1 : ρ.re ≤ 1)
    (hgap : ρ.re ≤ 1 - δ ∨ 8 * δ * Real.log x ≤ ρ.im ^ 2) :
    ‖artinGaussianZeroTerm x ρ‖ ≤
      (artinGaussianConstant * x ^ (1 - δ)) * Real.exp (-ρ.im ^ 2 / 8) := by
  have hnorm := artinGaussianZeroTerm_norm_le (by linarith : 0 < x) hσ0 hσ1
  rcases hgap with hlow | hhigh
  · have hpow := Real.rpow_le_rpow_of_exponent_le hx hlow
    have hweight : Real.exp (-ρ.im ^ 2 / 4) ≤ Real.exp (-ρ.im ^ 2 / 8) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ρ.im]
    exact hnorm.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hpow artinGaussianConstant_pos.le) hweight
      (Real.exp_pos _).le (by have := artinGaussianConstant_pos; positivity))
  · have hpow : x ^ ρ.re ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx hσ1
    calc
      _ ≤ artinGaussianConstant * x ^ ρ.re * Real.exp (-ρ.im ^ 2 / 4) := hnorm
      _ ≤ artinGaussianConstant * (x * Real.exp (-ρ.im ^ 2 / 4)) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow artinGaussianConstant_pos.le) (Real.exp_pos _).le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          (gaussian_high_tail_le (by linarith) hhigh) artinGaussianConstant_pos.le

theorem artinGaussianZeroTerm_real_nonneg {x : ℝ} {ρ : ℂ} (hx : 0 < x) (hreal : ρ.im = 0) :
    0 ≤ (artinGaussianZeroTerm x ρ).re := by
  have hρ : ρ = (ρ.re : ℂ) := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, hreal]
  rw [hρ, artinGaussianZeroTerm, ← Complex.ofReal_cpow hx.le]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (artinGaussianMellin_real_pos _).le

/-- The low nonreal zero hypothesis only extends up to the Gaussian cutoff. -/
theorem gaussian_gap_or_height_of_finite_height {x δ : ℝ} {ρ : ℂ}
    (_hx : 1 ≤ x) (_hδ : 0 ≤ δ) (hρ : ρ.im ≠ 0)
    (hlow : ρ.im ≠ 0 → |ρ.im| ≤ Real.sqrt (8 * δ * Real.log x) → ρ.re ≤ 1 - δ) :
    ρ.re ≤ 1 - δ ∨ 8 * δ * Real.log x ≤ ρ.im ^ 2 := by
  by_cases hheight : 8 * δ * Real.log x ≤ ρ.im ^ 2
  · exact Or.inr hheight
  · apply Or.inl
    apply hlow hρ
    exact Real.le_sqrt_of_sq_le (by rw [sq_abs]; exact (lt_of_not_ge hheight).le)

theorem artinGaussianZeroRemainder_summable {ι : Type*} (ρ : ι → ℂ) {x : ℝ}
    (hx : 1 ≤ x) (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8))) :
    Summable (fun i => -(artinGaussianZeroTerm x (ρ i)).re) := by
  apply (hw.mul_left (artinGaussianConstant * x)).of_norm_bounded
  intro i
  calc
    ‖-(artinGaussianZeroTerm x (ρ i)).re‖ = |(artinGaussianZeroTerm x (ρ i)).re| := by
      rw [norm_neg, Real.norm_eq_abs]
    _ ≤ ‖artinGaussianZeroTerm x (ρ i)‖ := Complex.abs_re_le_norm _
    _ ≤ _ := artinGaussianZeroTerm_norm_le_half_weight hx (hstrip i).1 (hstrip i).2

/-- The analytic explicit formula and zero-weight estimate remain inputs.
This proves the abstract low/high zero argument with multiplicities allowed
by repeating entries of rho; real zeros are removed before taking norms. -/
theorem artinGaussianZeroRemainder_le {ι : Type*} (ρ : ι → ℂ) {x δ : ℝ}
    (hx : 1 ≤ x) (hδ : 0 ≤ δ) (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ Real.sqrt (8 * δ * Real.log x) →
      (ρ i).re ≤ 1 - δ) :
    artinGaussianZeroRemainder ρ x ≤
      (artinGaussianConstant * x ^ (1 - δ)) * ∑' i, Real.exp (-(ρ i).im ^ 2 / 8) := by
  unfold artinGaussianZeroRemainder
  rw [← hw.tsum_mul_left]
  apply (artinGaussianZeroRemainder_summable ρ hx hstrip hw).tsum_le_tsum _ (hw.mul_left _)
  intro i
  by_cases hr : (ρ i).im = 0
  · have hz := artinGaussianZeroTerm_real_nonneg (by linarith : 0 < x) hr
    have hp : 0 ≤ (artinGaussianConstant * x ^ (1 - δ)) * Real.exp (-(ρ i).im ^ 2 / 8) := by
      have := artinGaussianConstant_pos
      positivity
    linarith
  · calc
      -(artinGaussianZeroTerm x (ρ i)).re ≤ ‖artinGaussianZeroTerm x (ρ i)‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ _ := artinGaussianZeroTerm_norm_le_of_gap_or_height hx (hstrip i).1 (hstrip i).2
        (gaussian_gap_or_height_of_finite_height hx hδ hr (hlow i))

end

end SimultaneousPrimitiveRoots

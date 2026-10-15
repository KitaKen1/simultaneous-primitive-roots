module

public import SimultaneousPrimitiveRoots.GaussianFixedHeight
public import SimultaneousPrimitiveRoots.GaussianZeroCounting

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- Real zeros have nonpositive signed contribution; this pointwise inequality
also controls any finite selection without comparing signed partial sums. -/
theorem artinGaussianZeroTerm_signed_le_fixed_height {x δ T : ℝ} {ρ : ℂ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hstrip : 0 ≤ ρ.re ∧ ρ.re ≤ 1)
    (hlow : ρ.im ≠ 0 → |ρ.im| ≤ T → ρ.re ≤ 1 - δ) :
    -(artinGaussianZeroTerm x ρ).re ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        Real.exp (-ρ.im ^ 2 / 8) := by
  by_cases hr : ρ.im = 0
  · have hz := artinGaussianZeroTerm_real_nonneg (by linarith : 0 < x) hr
    have hp : 0 ≤ (artinGaussianConstant *
        (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) * Real.exp (-ρ.im ^ 2 / 8) := by
      have := artinGaussianConstant_pos
      positivity
    linarith
  · have hg : ρ.re ≤ 1 - δ ∨ T ≤ |ρ.im| := by
      by_cases ht : |ρ.im| ≤ T
      · exact Or.inl (hlow hr ht)
      · exact Or.inr (le_of_not_ge ht)
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (artinGaussianZeroTerm_norm_le_fixed_height hx hT hstrip.1 hstrip.2 hg))

theorem criticalGaussianZeroTerms_finite_real_upper {ι : Type*} (ρ : ι → ℂ)
    {x δ T : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hstrip : ∀ i, 0 ≤ (ρ i).re ∧ (ρ i).re ≤ 1)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8)))
    (hlow : ∀ i, (ρ i).im ≠ 0 → |(ρ i).im| ≤ T → (ρ i).re ≤ 1 - δ)
    (S : Finset ι) :
    (∑ i ∈ S, -(artinGaussianZeroTerm x (ρ i)).re) ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        ∑' i, Real.exp (-(ρ i).im ^ 2 / 8) := by
  have hp : 0 ≤ artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8)) := by
    have := artinGaussianConstant_pos
    positivity
  calc
    _ ≤ ∑ i ∈ S, (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        Real.exp (-(ρ i).im ^ 2 / 8) := Finset.sum_le_sum (fun i _ =>
          artinGaussianZeroTerm_signed_le_fixed_height hx hT (hstrip i) (hlow i))
    _ = (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8))) *
        ∑ i ∈ S, Real.exp (-(ρ i).im ^ 2 / 8) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum _ (fun _ _ => (Real.exp_pos _).le)) hp

/-- Distinct zeros are expanded to their natural multiplicity labels exactly.
Omitted real zeros do not invalidate the bound, since the majorant is positive. -/
theorem fullQuotientCriticalZeros_finite_signed_sum_le {H : ℂ → ℂ} {x δ T d : ℝ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) (hd : 0 < d)
    (hw : Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)))
    (hlow : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ T → (fullQuotientIndexedZero H i).re ≤ 1 - δ)
    (S : Finset {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0}) :
    (∑ s ∈ S, ((-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) *
      artinGaussianZeroTerm x s).re) ≤
      (artinGaussianConstant * (x ^ (1 - δ) + x * Real.exp (-T ^ 2 / 8)) / d) *
        ∑' i : fullQuotientZeroIndex H,
          Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8) := by
  let U : Finset (fullQuotientZeroIndex H) :=
    S.sigma (fun s => (Finset.univ : Finset (Fin (fullQuotientZeroMultiplicity H s))))
  have heq : (∑ i ∈ U, -(artinGaussianZeroTerm x (fullQuotientIndexedZero H i)).re) =
      ∑ s ∈ S, (fullQuotientZeroMultiplicity H s : ℝ) * (-(artinGaussianZeroTerm x s).re) := by
    simpa [U, fullQuotientZeroIndex, fullQuotientIndexedZero] using
      (Finset.sum_sigma S
        (fun s => (Finset.univ : Finset (Fin (fullQuotientZeroMultiplicity H s))))
        (fun i => -(artinGaussianZeroTerm x i.1.val).re))
  have hs := criticalGaussianZeroTerms_finite_real_upper (fullQuotientIndexedZero H)
    hx hT (fullQuotientIndexedZero_strip H) hw hlow U
  rw [heq] at hs
  have hpoint (s : {s : ℂ // 0 ≤ s.re ∧ s.re ≤ 1 ∧ H s = 0}) :
      ((-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) * artinGaussianZeroTerm x s).re =
      ((fullQuotientZeroMultiplicity H s : ℝ) * (-(artinGaussianZeroTerm x s).re)) / d := by
    have hr : (-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) =
        ((-(fullQuotientZeroMultiplicity H s : ℝ) / d : ℝ) : ℂ) := by push_cast; rfl
    rw [hr, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  apply (div_le_div_of_nonneg_right hs hd.le).trans_eq
  ring

end
end SimultaneousPrimitiveRoots

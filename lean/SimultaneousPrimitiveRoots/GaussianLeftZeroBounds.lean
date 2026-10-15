module

public import SimultaneousPrimitiveRoots.ZetaQuotientLeftZeroCount

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- On the negative strip, the x-power is at most one for every x >= 1. -/
theorem artinGaussianZeroTerm_norm_le_left_strip {x : ℝ} {ρ : ℂ}
    (hx : 1 ≤ x) (hσ0 : -1 ≤ ρ.re) (hσ1 : ρ.re ≤ 0) :
    ‖artinGaussianZeroTerm x ρ‖ ≤
      artinGaussianConstant * Real.exp (-ρ.im ^ 2 / 8) := by
  have hm : ‖artinGaussianMellin ρ‖ ≤
      artinGaussianConstant * Real.exp (-ρ.im ^ 2 / 8) := by
    rw [artinGaussianMellin_norm, artinGaussianConstant, mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hs : ρ.re ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ρ.im]
  unfold artinGaussianZeroTerm
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x)]
  calc
    x ^ ρ.re * ‖artinGaussianMellin ρ‖ ≤ 1 * ‖artinGaussianMellin ρ‖ :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hx hσ1) (norm_nonneg _)
    _ ≤ _ := by simpa using hm

theorem leftGaussianZeroTerms_norm_summable {ι : Type*} (ρ : ι → ℂ) {x : ℝ}
    (hx : 1 ≤ x) (hstrip : ∀ i, -1 ≤ (ρ i).re ∧ (ρ i).re < 0)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8))) :
    Summable (fun i => ‖artinGaussianZeroTerm x (ρ i)‖) := by
  apply (hw.mul_left artinGaussianConstant).of_nonneg_of_le (fun _ => norm_nonneg _)
  exact fun i => artinGaussianZeroTerm_norm_le_left_strip hx (hstrip i).1 (hstrip i).2.le

/-- This is an absolute bound, so it remains valid for any finite selected
subfamily of the actual negative-strip zeros. -/
theorem leftGaussianZeroTerms_norm_tsum_le {ι : Type*} (ρ : ι → ℂ) {x : ℝ}
    (hx : 1 ≤ x) (hstrip : ∀ i, -1 ≤ (ρ i).re ∧ (ρ i).re < 0)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8))) :
    (∑' i, ‖artinGaussianZeroTerm x (ρ i)‖) ≤
      artinGaussianConstant * ∑' i, Real.exp (-(ρ i).im ^ 2 / 8) := by
  rw [← tsum_mul_left]
  exact (leftGaussianZeroTerms_norm_summable ρ hx hstrip hw).tsum_le_tsum
    (fun i => artinGaussianZeroTerm_norm_le_left_strip hx (hstrip i).1 (hstrip i).2.le)
    (hw.mul_left artinGaussianConstant)

theorem leftGaussianZeroTerms_finite_real_upper {ι : Type*} (ρ : ι → ℂ) {x : ℝ}
    (hx : 1 ≤ x) (hstrip : ∀ i, -1 ≤ (ρ i).re ∧ (ρ i).re < 0)
    (hw : Summable (fun i => Real.exp (-(ρ i).im ^ 2 / 8))) (S : Finset ι) :
    (∑ i ∈ S, -(artinGaussianZeroTerm x (ρ i)).re) ≤
      artinGaussianConstant * ∑' i, Real.exp (-(ρ i).im ^ 2 / 8) := by
  calc
    (∑ i ∈ S, -(artinGaussianZeroTerm x (ρ i)).re) ≤
        ∑ i ∈ S, ‖artinGaussianZeroTerm x (ρ i)‖ := Finset.sum_le_sum (fun i _ =>
          (neg_le_abs _).trans (Complex.abs_re_le_norm _))
    _ ≤ ∑' i, ‖artinGaussianZeroTerm x (ρ i)‖ :=
      (leftGaussianZeroTerms_norm_summable ρ hx hstrip hw).sum_le_tsum _ (fun _ _ => norm_nonneg _)
    _ ≤ _ := leftGaussianZeroTerms_norm_tsum_le ρ hx hstrip hw

/-- Passing from distinct actual zeros to all of their multiplicity labels is
an exact finite sigma-sum identity, before comparison with the whole mass. -/
theorem fullQuotientLeftZeros_finite_multiplicity_norm_sum_le {H : ℂ → ℂ} {x : ℝ}
    (hx : 1 ≤ x)
    (hw : Summable (fun i : fullQuotientLeftZeroIndex H =>
      Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)))
    (S : Finset {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}) :
    (∑ s ∈ S, (fullQuotientZeroMultiplicity H s : ℝ) * ‖artinGaussianZeroTerm x s‖) ≤
      artinGaussianConstant * ∑' i : fullQuotientLeftZeroIndex H,
        Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8) := by
  let U : Finset (fullQuotientLeftZeroIndex H) :=
    S.sigma (fun s => (Finset.univ : Finset (Fin (fullQuotientZeroMultiplicity H s))))
  have heq : (∑ i ∈ U, ‖artinGaussianZeroTerm x (fullQuotientLeftIndexedZero H i)‖) =
      ∑ s ∈ S, (fullQuotientZeroMultiplicity H s : ℝ) * ‖artinGaussianZeroTerm x s‖ := by
    simpa [U, fullQuotientLeftZeroIndex, fullQuotientLeftIndexedZero] using
      (Finset.sum_sigma S
        (fun s => (Finset.univ : Finset (Fin (fullQuotientZeroMultiplicity H s))))
        (fun i => ‖artinGaussianZeroTerm x i.1.val‖))
  rw [← heq]
  apply le_trans ((leftGaussianZeroTerms_norm_summable (fullQuotientLeftIndexedZero H) hx
    (fullQuotientLeftIndexedZero_strip H) hw).sum_le_tsum U (fun _ _ => norm_nonneg _))
  exact leftGaussianZeroTerms_norm_tsum_le (fullQuotientLeftIndexedZero H) hx
    (fullQuotientLeftIndexedZero_strip H) hw

/-- A one-sided bound for the signed, normalized residue terms over any finite
set of actual negative-strip zeros. The actual boundary growth is separate. -/
theorem fullQuotientLeftZeros_finite_signed_sum_le {H : ℂ → ℂ} {x d : ℝ}
    (hx : 1 ≤ x) (hd : 0 < d)
    (hw : Summable (fun i : fullQuotientLeftZeroIndex H =>
      Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)))
    (S : Finset {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}) :
    (∑ s ∈ S, ((-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) *
      artinGaussianZeroTerm x s).re) ≤
      (artinGaussianConstant / d) * ∑' i : fullQuotientLeftZeroIndex H,
        Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8) := by
  have hterm (s : {s : ℂ // -1 ≤ s.re ∧ s.re < 0 ∧ H s = 0}) :
      ((-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) *
        artinGaussianZeroTerm x s).re ≤
      ((fullQuotientZeroMultiplicity H s : ℝ) * ‖artinGaussianZeroTerm x s‖) / d := by
    have hr : (-(fullQuotientZeroMultiplicity H s : ℂ) / (d : ℂ)) =
        ((-(fullQuotientZeroMultiplicity H s : ℝ) / d : ℝ) : ℂ) := by push_cast; rfl
    rw [hr, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hh := mul_le_mul_of_nonneg_left
      ((neg_le_abs (artinGaussianZeroTerm x s).re).trans (Complex.abs_re_le_norm _))
      (div_nonneg (Nat.cast_nonneg (fullQuotientZeroMultiplicity H s)) hd.le)
    convert hh using 1 <;> first | rfl | ring
  calc
    _ ≤ ∑ s ∈ S, ((fullQuotientZeroMultiplicity H s : ℝ) * ‖artinGaussianZeroTerm x s‖) / d :=
      Finset.sum_le_sum (fun s _ => hterm s)
    _ = (∑ s ∈ S, (fullQuotientZeroMultiplicity H s : ℝ) * ‖artinGaussianZeroTerm x s‖) / d :=
      (Finset.sum_div S _ d).symm
    _ ≤ (artinGaussianConstant * ∑' i : fullQuotientLeftZeroIndex H,
        Real.exp (-(fullQuotientLeftIndexedZero H i).im ^ 2 / 8)) / d :=
      div_le_div_of_nonneg_right (fullQuotientLeftZeros_finite_multiplicity_norm_sum_le hx hw S) hd.le
    _ = _ := by ring

end
end SimultaneousPrimitiveRoots

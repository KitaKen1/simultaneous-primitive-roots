module

public import SimultaneousPrimitiveRoots.ReflectionGammaKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- Shifting to the right decreases the reciprocal Gamma norm when the
imaginary part has modulus at least one. This avoids a Stirling theorem. -/
theorem reflectionGamma_inv_shift_one (z : ℂ) (hy : 1 ≤ |z.im|) :
    ‖(Complex.Gamma (z + 1))⁻¹‖ ≤ ‖(Complex.Gamma z)⁻¹‖ := by
  have hz : 1 ≤ ‖z‖ := hy.trans (Complex.abs_im_le_norm z)
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z, norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg _) hz

theorem reflectionGamma_inv_shift_nat (z : ℂ) (n : ℕ) (hy : 1 ≤ |z.im|) :
    ‖(Complex.Gamma (z + n))⁻¹‖ ≤ ‖(Complex.Gamma z)⁻¹‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := reflectionGamma_inv_shift_one (z + n) (by simpa using hy)
    simpa only [Nat.cast_succ, add_assoc] using h.trans ih

/-- On each fixed closed vertical strip the entire reciprocal Gamma
function has a uniform exponential bound, including its zeros. -/
theorem reflectionGamma_inv_strip_bound (l u : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖(Complex.Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨n, hn⟩ := exists_nat_gt u
  have hpos : 0 < 1 - u + n := by linarith
  have hc : ContinuousOn Real.Gamma (Icc (1 - u + n) (1 - l + n)) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (by
      intro x hx; exact lt_of_lt_of_le hpos hx.1)
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let R : ℝ := |l| + |u| + 2
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  let C : ℝ := max 1 (max B (G / Real.pi))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, hC, fun z hl hu => ?_⟩
  have hExp : 1 ≤ Real.exp (Real.pi * |z.im|) :=
    Real.one_le_exp (by positivity)
  by_cases hy : 1 ≤ |z.im|
  · have hs := reflectionGamma_inv_shift_nat (z - n) n (by simpa using hy)
    simp only [sub_add_cancel] at hs
    have hz : (z - n).re < 1 := by simp only [sub_re, natCast_re]; linarith
    have hx : 1 - (z - n).re ∈ Icc (1 - u + n) (1 - l + n) := by
      simp only [mem_Icc, sub_re, natCast_re]; constructor <;> linarith
    have hg : Real.Gamma (1 - (z - n).re) ≤ G :=
      (le_abs_self _).trans (hG _ hx)
    have hGC : Real.Gamma (1 - (z - n).re) / Real.pi ≤ C :=
      (div_le_div_of_nonneg_right hg Real.pi_pos.le).trans
        ((le_max_right B (G / Real.pi)).trans (le_max_right _ _))
    calc
      _ ≤ ‖(Complex.Gamma (z - n))⁻¹‖ := hs
      _ ≤ (Real.Gamma (1 - (z - n).re) / Real.pi) *
          Real.exp (Real.pi * |(z - n).im|) := reflectionGamma_inv_norm_le hz
      _ ≤ C * Real.exp (Real.pi * |z.im|) := by
        simpa using mul_le_mul_of_nonneg_right hGC (Real.exp_pos _).le
  · have him : |z.im| ≤ 1 := (lt_of_not_ge hy).le
    have hre : |z.re| ≤ |l| + |u| := by
      rw [abs_le]; constructor <;> linarith [le_abs_self u, neg_abs_le l,
        abs_nonneg l, abs_nonneg u]
    have hz : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans (by dsimp [R]; linarith)
    have hb : ‖(Complex.Gamma z)⁻¹‖ ≤ B := hB z hz
    have hBC : B ≤ C := (le_max_left B (G / Real.pi)).trans (le_max_right _ _)
    exact (hb.trans hBC).trans (le_mul_of_one_le_right hC.le hExp)

theorem reflectionGamma_exp_square_norm (z : ℂ) :
    ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2) * Real.exp (-z.im ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [sq, Complex.mul_re]
  ring

/-- A slightly coarser bound than Stirling gives is sufficient: the
factor exp(z²) absorbs exp(2*pi*r*abs(Im z)). -/
theorem reflectionGammaQuotient_strip_bound (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (l u : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖reflectionGammaQuotient C A r z‖ ≤
        B * Real.exp (-z.im ^ 2 + (2 * Real.pi * r) * |z.im|) := by
  obtain ⟨G₁, hG₁, hb₁⟩ := reflectionGamma_inv_strip_bound (l + 5 / 6) (u + 5 / 6)
  obtain ⟨G₂, hG₂, hb₂⟩ := reflectionGamma_inv_strip_bound (l + 7 / 6) (u + 7 / 6)
  have hc : ContinuousOn (fun x : ℝ => ‖(C : ℂ)⁻¹‖ * A ^ (-x) * Real.exp (x ^ 2))
      (Icc l u) := by
    exact ((continuous_const.mul ((Real.continuous_const_rpow hA.ne').comp
      continuous_neg)).mul (Real.continuous_exp.comp (continuous_pow 2))).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let B : ℝ := (max M 1) * (G₁ * G₂) ^ r
  have hB : 0 < B := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    (pow_pos (mul_pos hG₁ hG₂) _)
  refine ⟨B, hB, fun z hl hu => ?_⟩
  have h1 := hb₁ (z + 5 / 6) (by simp; linarith) (by simp; linarith)
  have h2 := hb₂ (z + 7 / 6) (by simp; linarith) (by simp; linarith)
  have hi1 : (z + (5 / 6 : ℂ)).im = z.im := by norm_num [Complex.add_im, Complex.div_im]
  have hi2 : (z + (7 / 6 : ℂ)).im = z.im := by norm_num [Complex.add_im, Complex.div_im]
  rw [hi1] at h1
  rw [hi2] at h2
  have hp : ‖(Complex.Gamma (z + 5 / 6))⁻¹ * (Complex.Gamma (z + 7 / 6))⁻¹‖ ^ r ≤
      ((G₁ * G₂) * Real.exp (2 * Real.pi * |z.im|)) ^ r := by
    apply pow_le_pow_left₀ (by positivity)
    rw [norm_mul]
    calc
      _ ≤ (G₁ * Real.exp (Real.pi * |z.im|)) *
          (G₂ * Real.exp (Real.pi * |z.im|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show 2 * Real.pi * |z.im| = Real.pi * |z.im| + Real.pi * |z.im| by ring,
          Real.exp_add]
        ring
  have hm : ‖(C : ℂ)⁻¹‖ * A ^ (-z.re) * Real.exp (z.re ^ 2) ≤ max M 1 :=
    ((le_abs_self _).trans (hM _ ⟨hl, hu⟩)).trans (le_max_left _ _)
  rw [reflectionGammaQuotient, norm_mul, norm_mul, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hA, neg_re, reflectionGamma_exp_square_norm]
  calc
    _ = (‖(C : ℂ)⁻¹‖ * A ^ (-z.re) * Real.exp (z.re ^ 2)) *
        Real.exp (-z.im ^ 2) *
        ‖(Complex.Gamma (z + 5 / 6))⁻¹ * (Complex.Gamma (z + 7 / 6))⁻¹‖ ^ r := by ring
    _ ≤ (max M 1) * Real.exp (-z.im ^ 2) *
        ((G₁ * G₂) * Real.exp (2 * Real.pi * |z.im|)) ^ r :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le) hp
        (by positivity) (by positivity)
    _ = B * Real.exp (-z.im ^ 2 + (2 * Real.pi * r) * |z.im|) := by
      rw [mul_pow, ← Real.exp_nat_mul, Real.exp_add]
      rw [show (r : ℝ) * (2 * Real.pi * |z.im|) = (2 * Real.pi * r) * |z.im| by ring]
      dsimp [B]
      ring

theorem reflectionGamma_absorb_linear (a y : ℝ) :
    -y ^ 2 + a * |y| ≤ -(1 / 2 : ℝ) * y ^ 2 + a ^ 2 / 2 := by
  nlinarith [sq_nonneg (|y| - a), sq_abs y]

theorem reflectionGammaQuotient_strip_gaussian (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (l u : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, l ≤ z.re → z.re ≤ u →
      ‖reflectionGammaQuotient C A r z‖ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2) := by
  obtain ⟨B, hB, hb⟩ := reflectionGammaQuotient_strip_bound C hA r l u
  refine ⟨B * Real.exp ((2 * Real.pi * r) ^ 2 / 2), by positivity,
    fun z hl hu => (hb z hl hu).trans ?_⟩
  calc
    _ ≤ B * Real.exp (-(1 / 2 : ℝ) * z.im ^ 2 + (2 * Real.pi * r) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (reflectionGamma_absorb_linear _ _)) hB.le
    _ = _ := by rw [Real.exp_add]; ring

/-- Absolute convergence on every actual vertical line is a conclusion
of the explicit reciprocal-Gamma formula. -/
theorem reflectionGammaQuotient_integrable_line (C : ℝ) {A : ℝ} (hA : 0 < A)
    (r : ℕ) (σ : ℝ) :
    Integrable (fun y : ℝ => reflectionGammaQuotient C A r ((σ : ℂ) + y * I)) := by
  obtain ⟨B, _, hb⟩ := reflectionGammaQuotient_strip_gaussian C hA r σ σ
  have hc : Continuous (fun y : ℝ => reflectionGammaQuotient C A r ((σ : ℂ) + y * I)) :=
    (reflectionGammaQuotient_entire C hA r).continuous.comp (by fun_prop)
  apply ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).const_mul B).mono'
    hc.aestronglyMeasurable
  apply ae_of_all
  intro y
  simpa using hb ((σ : ℂ) + y * I) (by simp) (by simp)

end
end SimultaneousPrimitiveRoots

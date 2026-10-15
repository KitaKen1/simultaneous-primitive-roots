module

public import Mathlib.Analysis.MellinTransform
public import Compat4331.ExpSubstitution
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set

noncomputable section

/-- The positive smoothing weight of research_note_ja.md. Only positive t
enters its Mellin transform. -/
def artinGaussianWeight (t : ℝ) : ℝ :=
  Real.exp ((Real.log 2) ^ 2 - (Real.log t) ^ 2)

def artinGaussianMellin (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp (((Real.log 2) ^ 2 : ℝ) + s ^ 2 / 4)

def artinGaussianLogKernel (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ) ^ 2 + s * u + ((Real.log 2) ^ 2 : ℝ))

theorem artinGaussianWeight_pos (t : ℝ) : 0 < artinGaussianWeight t := Real.exp_pos _

theorem artinGaussianWeight_ge_one {t : ℝ} (ht : 1 ≤ t) (ht2 : t ≤ 2) :
    1 ≤ artinGaussianWeight t := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlog2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) ht2
  apply Real.one_le_exp_iff.mpr
  nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

theorem artinGaussianLogKernel_integrable (s : ℂ) :
    Integrable (artinGaussianLogKernel s) := by
  change Integrable (fun u : ℝ => Complex.exp (-(u : ℂ) ^ 2 + s * u + ((Real.log 2) ^ 2 : ℝ)))
  simpa only [neg_one_mul] using
    integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) s (((Real.log 2) ^ 2 : ℝ) : ℂ)

theorem artinGaussianLogKernel_integral (s : ℂ) :
    (∫ u : ℝ, artinGaussianLogKernel s u) = artinGaussianMellin s := by
  have h := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num) s
    (((Real.log 2) ^ 2 : ℝ) : ℂ)
  have hsqrt : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    have hc : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hc, ← Complex.ofReal_cpow Real.pi_pos.le, Real.sqrt_eq_rpow]
  change (∫ u : ℝ, Complex.exp (-(u : ℂ) ^ 2 + s * u + ((Real.log 2) ^ 2 : ℝ))) = _
  simp only [neg_one_mul, neg_neg, mul_neg, mul_one, div_one, div_neg, sub_neg_eq_add] at h
  rw [hsqrt] at h
  exact h

theorem artinGaussianWeight_exp_substitution (s : ℂ) (u : ℝ) :
    Real.exp u • (((Real.exp u : ℝ) : ℂ) ^ (s - 1) •
      ((artinGaussianWeight (Real.exp u) : ℝ) : ℂ)) = artinGaussianLogKernel s u := by
  rw [artinGaussianWeight, Real.log_exp, artinGaussianLogKernel]
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  have hlog : Complex.log (Complex.exp (u : ℂ)) = (u : ℂ) := by
    apply Complex.log_exp <;> simp only [Complex.ofReal_im] <;> linarith [Real.pi_pos]
  rw [hlog, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem artinGaussianWeight_hasMellin (s : ℂ) :
    HasMellin (fun t => ((artinGaussianWeight t : ℝ) : ℂ)) s (artinGaussianMellin s) := by
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) • ((artinGaussianWeight t : ℝ) : ℂ)
  have hsub : (fun u : ℝ => Real.exp u • g (Real.exp u)) = artinGaussianLogKernel s := by
    funext u
    exact artinGaussianWeight_exp_substitution s u
  constructor
  · change IntegrableOn g (Ioi 0)
    rw [← integrable_comp_exp, hsub]
    exact artinGaussianLogKernel_integrable s
  · change (∫ t in Ioi 0, g t) = _
    rw [← integral_comp_exp, hsub, artinGaussianLogKernel_integral]

theorem artinGaussianMellin_norm (s : ℂ) :
    ‖artinGaussianMellin s‖ = Real.sqrt Real.pi *
      Real.exp ((Real.log 2) ^ 2 + (s.re ^ 2 - s.im ^ 2) / 4) := by
  unfold artinGaussianMellin
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  congr 2
  simp only [sq, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.div_ofNat_re]

theorem artinGaussianMellin_real_pos (β : ℝ) :
    0 < (artinGaussianMellin (β : ℂ)).re := by
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  unfold artinGaussianMellin
  have heq : (((Real.log 2) ^ 2 : ℝ) : ℂ) + (β : ℂ) ^ 2 / 4 =
      (((Real.log 2) ^ 2 + β ^ 2 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos hsqrt (Real.exp_pos _)

theorem artinGaussianMellin_norm_le {s : ℂ} (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖artinGaussianMellin s‖ ≤
      (Real.sqrt Real.pi * Real.exp ((Real.log 2) ^ 2 + 1 / 4)) *
        Real.exp (-s.im ^ 2 / 4) := by
  rw [artinGaussianMellin_norm, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith

end

end SimultaneousPrimitiveRoots

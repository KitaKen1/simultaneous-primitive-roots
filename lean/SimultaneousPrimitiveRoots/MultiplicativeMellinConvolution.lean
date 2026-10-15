module

public import SimultaneousPrimitiveRoots.PositiveMultiplicativeMeasure
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology Convolution
noncomputable section

def artinMellinLogPullback (f : ℝ → ℂ) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-s * u) * f (Real.exp (-u))

theorem artinMultiplicative_power_density {T : ℝ} (hT : 0 < T) (s w : ℂ) :
    T⁻¹ • ((T : ℂ) ^ s * w) = (T : ℂ) ^ (s - 1) * w := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hT)),
    Complex.cpow_one]
  simp only [real_smul, Complex.ofReal_inv]
  ring

theorem artinMellin_convergent_iff_multiplicative (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (fun T : ℝ => (T : ℂ) ^ s * f T)
      artinPositiveMultiplicativeMeasure := by
  rw [artinPositiveMultiplicative_integrable_iff]
  exact (integrableOn_congr_fun (fun T hT => artinMultiplicative_power_density hT s (f T))
    measurableSet_Ioi).symm

theorem artinMellin_eq_multiplicative (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ T, (T : ℂ) ^ s * f T ∂artinPositiveMultiplicativeMeasure := by
  rw [artinPositiveMultiplicative_integral, mellin]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  simpa only [smul_eq_mul] using (artinMultiplicative_power_density hT s (f T)).symm

theorem artinMellin_exp_power (s : ℂ) (u : ℝ) :
    (Real.exp (-u) : ℂ) ^ s = Complex.exp (-s * u) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos (-u)).le, Real.log_exp]
  congr 1
  push_cast
  ring

theorem artinMellin_convergent_iff_logPullback (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (artinMellinLogPullback f s) := by
  rw [artinMellin_convergent_iff_multiplicative,
    artinPositiveMultiplicative_integrable_exp_iff]
  have heq : (fun u : ℝ => (Real.exp u : ℂ) ^ s * f (Real.exp u)) =
      fun u => artinMellinLogPullback f s (-u) := by
    funext u
    simp only [artinMellinLogPullback, neg_neg, ← artinMellin_exp_power]
  rw [heq]
  constructor
  · intro h
    simpa only [neg_neg] using h.comp_neg
  · intro h
    exact h.comp_neg

theorem artinMellin_eq_integral_logPullback (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u, artinMellinLogPullback f s u := by
  rw [artinMellin_eq_multiplicative, artinPositiveMultiplicative_integral_exp]
  have heq : (fun u : ℝ => (Real.exp u : ℂ) ^ s * f (Real.exp u)) =
      fun u => artinMellinLogPullback f s (-u) := by
    funext u
    simp only [artinMellinLogPullback, neg_neg, ← artinMellin_exp_power]
  rw [heq]
  exact integral_neg_eq_self (artinMellinLogPullback f s) volume

/-- The actual integral against dt/t, not a definition by its desired transform. -/
def artinMultiplicativeConvolution (f g : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t, f t * g (u / t) ∂artinPositiveMultiplicativeMeasure

theorem artinMultiplicativeConvolution_log (f g : ℝ → ℂ) (u : ℝ) :
    artinMultiplicativeConvolution f g (Real.exp (-u)) =
      ∫ v, f (Real.exp (-v)) * g (Real.exp (-(u - v))) := by
  rw [artinMultiplicativeConvolution, artinPositiveMultiplicative_integral_exp]
  have heq : (fun v : ℝ => f (Real.exp v) * g (Real.exp (-u) / Real.exp v)) =
      fun v => (fun w : ℝ => f (Real.exp (-w)) * g (Real.exp (-(u - w)))) (-v) := by
    funext v
    rw [← Real.exp_sub]
    simp only [neg_neg]
    congr 3
    ring
  rw [heq]
  exact integral_neg_eq_self
    (fun v : ℝ => f (Real.exp (-v)) * g (Real.exp (-(u - v)))) volume

theorem artinMellinLogPullback_convolution (f g : ℝ → ℂ) (s : ℂ) (u : ℝ) :
    artinMellinLogPullback (artinMultiplicativeConvolution f g) s u =
      convolution (artinMellinLogPullback f s) (artinMellinLogPullback g s)
        (ContinuousLinearMap.mul ℂ ℂ) volume u := by
  rw [artinMellinLogPullback, artinMultiplicativeConvolution_log, ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  simp only [artinMellinLogPullback, ContinuousLinearMap.mul_apply']
  rw [show -s * (u : ℂ) = -s * (v : ℂ) + -s * ((u - v : ℝ) : ℂ) by
    push_cast; ring, Complex.exp_add]
  ring

/-- Absolute convergence follows from the product-space convolution theorem. -/
theorem artinMultiplicativeConvolution_mellin_convergent {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (artinMultiplicativeConvolution f g) s := by
  rw [artinMellin_convergent_iff_logPullback]
  have heq := funext (artinMellinLogPullback_convolution f g s)
  rw [heq]
  exact ((artinMellin_convergent_iff_logPullback f s).mp hf).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) ((artinMellin_convergent_iff_logPullback g s).mp hg)

/-- Fubini identifies the convergent Mellin transform of the actual convolution. -/
theorem artinMultiplicativeConvolution_mellin {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (artinMultiplicativeConvolution f g) s = mellin f s * mellin g s := by
  rw [artinMellin_eq_integral_logPullback]
  simp_rw [artinMellinLogPullback_convolution]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    ((artinMellin_convergent_iff_logPullback f s).mp hf)
    ((artinMellin_convergent_iff_logPullback g s).mp hg)]
  simp only [ContinuousLinearMap.mul_apply', ← artinMellin_eq_integral_logPullback]

theorem artinMultiplicative_integral_comp_mul (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t, f (a * t) ∂artinPositiveMultiplicativeMeasure) =
      ∫ t, f t ∂artinPositiveMultiplicativeMeasure := by
  have h := mellin_comp_mul_left f 0 ha
  simpa only [artinMellin_eq_multiplicative, neg_zero, Complex.cpow_zero,
    one_mul, one_smul] using h

theorem artinMultiplicative_integrable_comp_mul_iff (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => f (a * t)) artinPositiveMultiplicativeMeasure ↔
      Integrable f artinPositiveMultiplicativeMeasure := by
  have h := MellinConvergent.comp_mul_left (f := f) (s := 0) ha
  simpa only [artinMellin_convergent_iff_multiplicative, Complex.cpow_zero, one_mul] using h

end
end SimultaneousPrimitiveRoots

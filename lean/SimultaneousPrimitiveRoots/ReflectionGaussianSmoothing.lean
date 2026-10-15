module

public import SimultaneousPrimitiveRoots.ReflectionProfileSmoothing
public import SimultaneousPrimitiveRoots.BesselFiniteProfile
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

theorem reflectionGaussian_vertical_integrable :
    VerticalIntegrable (fun z : ℂ => Complex.exp (z ^ 2)) 0 := by
  have h := integrable_cexp_quadratic' (b := (-1 : ℂ)) (by norm_num) 0 0
  apply h.congr
  apply ae_of_all
  intro y
  simp only [Complex.ofReal_zero, zero_add, zero_mul, add_zero, mul_pow, Complex.I_sq]
  congr 1
  ring

theorem reflectionGaussian_inverse_integrand {u : ℝ} (hu : 0 < u) (y : ℝ) :
    (u : ℂ) ^ (-((y : ℂ) * I)) * Complex.exp (((y : ℂ) * I) ^ 2) =
      Complex.exp ((-1 : ℂ) * (y : ℂ) ^ 2 + (-(Real.log u : ℂ) * I) * y + 0) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)),
    ← Complex.ofReal_log hu.le, ← Complex.exp_add]
  simp only [mul_pow, Complex.I_sq]
  congr 1
  ring

theorem reflectionGaussian_mellinInv {u : ℝ} (hu : 0 < u) :
    mellinInv 0 (fun z : ℂ => Complex.exp (z ^ 2)) u = reflectionLogGaussian u := by
  rw [mellinInv]
  simp only [Complex.ofReal_zero, zero_add, smul_eq_mul, Complex.real_smul]
  simp_rw [reflectionGaussian_inverse_integrand hu]
  rw [integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num)]
  have hsqrt : ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt Real.pi : ℂ) := by
    norm_num only [neg_neg, div_one]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow Real.pi_pos.le, ← Real.sqrt_eq_rpow]
  rw [hsqrt]
  have hexp : (0 : ℂ) - (-(Real.log u : ℂ) * I) ^ 2 / (4 * (-1)) =
      -((Real.log u : ℂ) ^ 2) / 4 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hexp, reflectionLogGaussian]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))
  have hsquare : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  field_simp
  linear_combination hsquare

theorem reflectionMellinSmoothing_mellin_vertical {C A : ℝ} (hC : C ≠ 0)
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ}
    (hV : ∀ y : ℝ, MellinConvergent V ((y : ℂ) * I))
    (hM : ∀ y : ℝ, mellin V ((y : ℂ) * I) =
      (C : ℂ) * (A : ℂ) ^ ((y : ℂ) * I) *
        (Complex.Gamma ((y : ℂ) * I + 5 / 6) *
          Complex.Gamma ((y : ℂ) * I + 7 / 6)) ^ r)
    (y : ℝ) :
    mellin (reflectionMellinSmoothing C A r V) ((y : ℂ) * I) =
      Complex.exp (((y : ℂ) * I) ^ 2) := by
  rw [reflectionMellinSmoothing, artinMultiplicativeConvolution_mellin
    (reflectionKernelReciprocal_mellin_convergent C hA r _) (hV y),
    reflectionKernelReciprocal_mellin C hA r, hM y]
  exact reflectionGammaQuotient_cancel hC hA r (by simp)

/-- Actual absolute integrability and continuity permit Mellin inversion.
The profile's entire Mellin formula and continuity are not required inputs:
its absolutely convergent formula on the single line Re(s)=0 suffices. -/
theorem reflectionMellinSmoothing_eq_gaussian {C A : ℝ} (hC : C ≠ 0)
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ}
    (hV : ∀ y : ℝ, MellinConvergent V ((y : ℂ) * I))
    (hM : ∀ y : ℝ, mellin V ((y : ℂ) * I) =
      (C : ℂ) * (A : ℂ) ^ ((y : ℂ) * I) *
        (Complex.Gamma ((y : ℂ) * I + 5 / 6) *
          Complex.Gamma ((y : ℂ) * I + 7 / 6)) ^ r)
    {u : ℝ} (hu : 0 < u) :
    reflectionMellinSmoothing C A r V u = reflectionLogGaussian u := by
  have hV0 : MellinConvergent V 0 := by simpa using hV 0
  have hc := reflectionMellinSmoothing_continuousOn C hA r hV0
  have hF : VerticalIntegrable (mellin (reflectionMellinSmoothing C A r V)) 0 := by
    change Integrable (fun y : ℝ => mellin (reflectionMellinSmoothing C A r V)
      ((0 : ℂ) + y * I))
    simp_rw [zero_add, reflectionMellinSmoothing_mellin_vertical hC hA r hV hM]
    simpa only [VerticalIntegrable, Complex.ofReal_zero, zero_add]
      using reflectionGaussian_vertical_integrable
  rw [← mellinInv_mellin_eq 0 (reflectionMellinSmoothing C A r V) hu
    (reflectionMellinSmoothing_mellin_convergent C hA r hV0) hF
    (hc.continuousAt (isOpen_Ioi.mem_nhds hu))]
  have he : mellinInv 0 (mellin (reflectionMellinSmoothing C A r V)) u =
      mellinInv 0 (fun z : ℂ => Complex.exp (z ^ 2)) u := by
    unfold mellinInv
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro y
    simp only [Complex.ofReal_zero, zero_add]
    rw [reflectionMellinSmoothing_mellin_vertical hC hA r hV hM]
  rw [he, reflectionGaussian_mellinInv hu]

theorem reflectionProfile_actual_integral_eq_gaussian {C A : ℝ} (hC : C ≠ 0)
    (hA : 0 < A) (r : ℕ) {V : ℝ → ℂ}
    (hV : ∀ y : ℝ, MellinConvergent V ((y : ℂ) * I))
    (hM : ∀ y : ℝ, mellin V ((y : ℂ) * I) =
      (C : ℂ) * (A : ℂ) ^ ((y : ℂ) * I) *
        (Complex.Gamma ((y : ℂ) * I + 5 / 6) *
          Complex.Gamma ((y : ℂ) * I + 7 / 6)) ^ r)
    {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel C A r T * V (u * T) ∂artinPositiveMultiplicativeMeasure) =
      reflectionLogGaussian u := by
  rw [← reflectionMellinSmoothing_integral]
  exact reflectionMellinSmoothing_eq_gaussian hC hA r hV hM hu

/-- Unconditional Gaussian smoothing for the constructed finite product of
actual local K integrals. Identity with the paper Haar profile remains open. -/
theorem artinBesselFiniteProfile_gaussian_smoothing {D c : ℝ} (hD : 0 < D)
    (hc : 0 < c) {ds : List ℝ} (hds : ∀ d ∈ ds, 0 < d) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (D * artinBesselProductC c ds) (artinBesselProductA c ds)
      (ds.length + 1) T * artinBesselFiniteProfile D c ds (u * T)
        ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  have hp := artinBesselFiniteProfile_constants_pos hD hc hds
  apply reflectionProfile_actual_integral_eq_gaussian (ne_of_gt hp.1) hp.2 _ _ _ hu
  · intro y
    exact artinBesselFiniteProfile_mellin_convergent D hc hds (by simp)
  · intro y
    exact artinBesselFiniteProfile_mellin D hc hds (by simp)

end
end SimultaneousPrimitiveRoots

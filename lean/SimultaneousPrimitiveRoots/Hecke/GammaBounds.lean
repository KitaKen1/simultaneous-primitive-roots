module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Elementary bounds for the complex Gamma function

* `norm_Gamma_le_Gamma_re`: `‖Γ(s)‖ ≤ Γ(re s)` for `re s > 0` (from the Euler integral).
* `norm_sin_le_exp`: `‖sin z‖ ≤ exp |im z|`.
* `norm_inv_Gamma_le`: `‖Γ(s)⁻¹‖ ≤ Γ(1 - re s) exp(π |im s|) / π` for `re s < 1`
  (from the reflection formula).

These are the Gamma-factor inputs for the growth bounds of `(s - 1) ζ_K(s)` (step D4).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open MeasureTheory Set Complex
open scoped Real

/-- `‖Γ(s)‖ ≤ Γ(re s)` for `re s > 0`. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]

/-- `‖sin z‖ ≤ exp |im z|`. -/
theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    simp
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
        gcongr
        exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ Real.exp |z.im| := by
        have ha := Real.exp_le_exp.mpr (le_abs_self z.im)
        have hb := Real.exp_le_exp.mpr (neg_le_abs z.im)
        linarith

/-- The reflection formula in the form `Γ(s)⁻¹ = Γ(1 - s) sin(π s) / π` for `re s < 1`. -/
theorem inv_Gamma_eq_reflection {s : ℂ} (hs : s.re < 1) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1 - s) * Complex.sin (π * s) / π := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  by_cases hG : Complex.Gamma s = 0
  · -- `s` is a nonpositive integer, so `sin (π s) = 0`
    rw [hG, inv_zero]
    obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff s).mp hG
    rw [hm, show (π : ℂ) * -(m : ℂ) = -((m : ℂ) * π) by ring, Complex.sin_neg,
      Complex.sin_nat_mul_pi]
    simp
  · have hrefl := Complex.Gamma_mul_Gamma_one_sub s
    have hsin : Complex.sin (π * s) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hrefl
      rcases mul_eq_zero.mp hrefl with h | h
      · exact hG h
      · -- `Γ(1 - s) = 0` forces `1 - s = -m`, impossible for `re s < 1`
        obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff (1 - s)).mp h
        have hre := congrArg Complex.re hm
        simp at hre
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
    field_simp
    rw [hrefl]
    field_simp

/-- `‖Γ(s)⁻¹‖ ≤ Γ(1 - re s) exp(π |im s|) / π` for `re s < 1`. -/
theorem norm_inv_Gamma_le {s : ℂ} (hs : s.re < 1) :
    ‖(Complex.Gamma s)⁻¹‖ ≤ Real.Gamma (1 - s.re) * Real.exp (π * |s.im|) / π := by
  rw [inv_Gamma_eq_reflection hs, norm_div, norm_mul]
  have h1 : ‖Complex.Gamma (1 - s)‖ ≤ Real.Gamma (1 - s.re) := by
    have := norm_Gamma_le_Gamma_re (s := 1 - s) (by simp; linarith)
    simpa using this
  have h2 : ‖Complex.sin (π * s)‖ ≤ Real.exp (π * |s.im|) := by
    have := norm_sin_le_exp (π * s)
    have him : ((π : ℂ) * s).im = π * s.im := by simp
    rw [him, abs_mul, abs_of_pos Real.pi_pos] at this
    exact this
  have hπ : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hπ]
  have hΓ : 0 ≤ Real.Gamma (1 - s.re) := (Real.Gamma_pos_of_pos (by linarith)).le
  gcongr

end SimultaneousPrimitiveRoots.Hecke

end

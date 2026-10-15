/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
/- Backport for Lean/Mathlib v4.33.1 from Mathlib f6090c7. -/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

public section

namespace MeasureTheory
open Real Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_comp_exp (g : ℝ → E) :
    ∫ x, exp x • g (exp x) = ∫ y in Ioi 0, g y := by
  symm
  rw [← range_exp, ← image_univ]
  simpa using integral_image_eq_integral_abs_deriv_smul .univ
    (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

theorem integrable_comp_exp (g : ℝ → E) :
    Integrable (fun x ↦ exp x • g (exp x)) ↔ IntegrableOn g (Ioi 0) := by
  rw [← integrableOn_univ, ← range_exp, ← image_univ]
  symm
  simpa using integrableOn_image_iff_integrableOn_abs_deriv_smul
    .univ (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn g

theorem integrableOn_comp_log_Ioi_zero (g : ℝ → E) :
    IntegrableOn (fun x ↦ x⁻¹ • g (log x)) (Ioi 0) ↔ Integrable g := by
  simpa using (integrable_comp_exp (fun x ↦ x⁻¹ • g (log x))).symm

end MeasureTheory

namespace MeasureTheory
open Real Set

/-- Log-Cauchy density integrability, using exp substitution. -/
theorem integrableOn_Ioi_zero_inv_mul_one_add_log_sq {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (fun t ↦ (t * (1 + (b * log t) ^ 2))⁻¹) (Ioi 0) := by
  have heq : (fun t ↦ (t * (1 + (b * log t) ^ 2))⁻¹) =
      fun t ↦ t⁻¹ • (1 + (b * log t) ^ 2)⁻¹ := by
    ext; simp [mul_comm]
  rw [heq, integrableOn_comp_log_Ioi_zero (fun u : ℝ ↦ (1 + (b * u) ^ 2)⁻¹)]
  have h := (integrable_inv_one_add_sq.comp_mul_left' hb)
  simpa using h

end MeasureTheory

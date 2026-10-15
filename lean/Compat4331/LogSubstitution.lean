/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2:
MeasureTheory/Integral/IntegralEqImproper.lean. -/
module

public import Compat4331.ExpSubstitution

public section

namespace MeasureTheory

open Real Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Substitution `y = log x` in integrals over `Ioi 0`. -/
theorem integral_comp_log_Ioi_zero (g : ℝ → E) :
    ∫ x in Ioi 0, x⁻¹ • g (log x) = ∫ y, g y := by
  simpa using (integral_comp_exp (fun x ↦ x⁻¹ • g (log x))).symm

end MeasureTheory

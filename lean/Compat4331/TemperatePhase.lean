/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2:
Analysis/Distribution/TemperateGrowth.lean. -/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

noncomputable section

open scoped ContDiff

@[fun_prop]
theorem Real.hasTemperateGrowth_sin :
    Real.sin.HasTemperateGrowth := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_sin_le_one n x

@[fun_prop]
theorem Real.hasTemperateGrowth_cos :
    Real.cos.HasTemperateGrowth := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using Real.abs_iteratedDeriv_cos_le_one n x

/-- The function `x ↦ exp (x * I)` has temperate growth. -/
@[fun_prop]
theorem Complex.hasTemperateGrowth_exp_mul_I :
    (fun x : ℝ ↦ Complex.exp (x * Complex.I)).HasTemperateGrowth := by
  simp only [Complex.exp_ofReal_mul_I]
  fun_prop

/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
/- Backport for Lean/Mathlib v4.33.1 from Mathlib f6090c7. -/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Tactic

public section

namespace PowerSeries
variable {R : Type*} [CommRing R]

theorem constantCoeff_subst_of_constantCoeff_zero {a : R⟦X⟧}
    (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  rw [constantCoeff_eq, constantCoeff_subst (HasSubst.of_constantCoeff_zero' ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [map_pow, ← constantCoeff_eq, ha, zero_pow hn]
    simp

lemma eq_substInvOfIsUnit_of_subst_eq_X (P : R⟦X⟧)
    (hP : constantCoeff P = 0) (hP' : IsUnit (coeff 1 P))
    {Q : R⟦X⟧} (hQ : HasSubst Q) (hPQ : P.subst Q = X) :
    Q = P.substInvOfIsUnit hP' := calc
  _ = PowerSeries.subst Q X := (subst_X hQ).symm
  _ = _ := by
    rw [← P.subst_substInvOfIsUnit_left hP hP',
      subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hP) hQ _, hPQ, X_subst _]

lemma subst_eq_X_of_subst_eq_X (P : R⟦X⟧)
    (hP : constantCoeff P = 0) (hP' : IsUnit (coeff 1 P))
    {Q : R⟦X⟧} (hQ : HasSubst Q) (hPQ : P.subst Q = X) :
    Q.subst P = X := by
  rw [P.eq_substInvOfIsUnit_of_subst_eq_X hP hP' hQ hPQ, P.subst_substInvOfIsUnit_left hP hP']

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The formal derivative of log(1+X) times (1+X) is one. -/
theorem derivative_log_mul_one_add_X : (derivative A) (log A) * (1 + X) = 1 := by
  have h : (derivative A) (log A) = mk (fun n ↦ (-1 : A) ^ n) := by
    simpa using (deriv_log (A := A))
  rw [h]
  have hh := congrArg (rescale (-1 : A)) (mk_one_mul_one_sub_eq_one A)
  simpa [rescale_mk, rescale_neg_one_X, sub_neg_eq_add] using hh

omit [Algebra ℚ A] in
theorem eq_of_derivative_mul_one_add_X_eq_self [IsAddTorsionFree A]
    {g : A⟦X⟧} (hderiv : (derivative _) g * (1 + X) = g) :
    g = constantCoeff g • (1 + X) := by
  have : Invertible (1 + X : A⟦X⟧) := (isUnit_iff_constantCoeff.mpr (by simp)).invertible
  have hcu : constantCoeff (⅟(1 + X) : A⟦X⟧) = 1 := by
    have h := congrArg (constantCoeff (R := A)) (mul_invOf_self (1 + X : A⟦X⟧))
    rw [map_mul] at h
    simpa using h
  have hg : g * ⅟(1 + X) = (derivative _) g := by
    conv_lhs => rw [← hderiv]
    rw [mul_assoc, mul_invOf_self, mul_one]
  have key : g * ⅟(1 + X) = C (constantCoeff g) := by
    refine derivative.ext ?_ ?_
    · simp only [Derivation.leibniz, derivative_invOf, map_add, derivative_one, derivative_X,
        zero_add, derivative_C, mul_one, smul_eq_mul, ← hg]
      ring
    · simp [hcu]
  rw [smul_eq_C_mul, ← key, mul_assoc, invOf_mul_self, mul_one]

variable (A) in
theorem subst_exp_log : (exp A).subst (log A) = 1 + X := by
  have : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  have hderiv : (derivative _) ((exp A).subst (log A)) * (1 + X) = (exp A).subst (log A) := by
    rw [derivative_subst (hg := HasSubst.log), derivative_exp, mul_assoc,
      derivative_log_mul_one_add_X, mul_one]
  have hconst : constantCoeff ((exp A).subst (log A)) = 1 := by
    rw [constantCoeff_subst_of_constantCoeff_zero constantCoeff_log, constantCoeff_exp]
  have h := eq_of_derivative_mul_one_add_X_eq_self hderiv
  rwa [hconst, one_smul] at h

variable (A) in
theorem subst_log_exp_sub_one : (log A).subst (exp A - 1) = X := by
  apply subst_eq_X_of_subst_eq_X (P := exp A - 1)
  · simp [constantCoeff_exp]
  · simp [coeff_exp]
  · exact HasSubst.log
  · rw [subst_sub HasSubst.log, subst_exp_log A, ← coe_substAlgHom HasSubst.log (R := A), map_one]
    ring

variable (A) in
@[simp]
theorem logOf_exp : logOf (exp A) = X :=
  subst_log_exp_sub_one A

end PowerSeries

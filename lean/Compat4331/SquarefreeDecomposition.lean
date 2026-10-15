/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/Algebra/Squarefree/Basic.lean, for Lean/Mathlib v4.33.1. -/
module

public import Mathlib.Algebra.Squarefree.Basic

public section

namespace UniqueFactorizationMonoid

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/-- Every element of a unique factorization monoid is a square times a squarefree element. -/
theorem _root_.exists_sq_mul_squarefree (x : R) : ∃ e d : R, e ^ 2 * d = x ∧ Squarefree d := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => exact ⟨0, 1, by simp, squarefree_one⟩
  | unit u hu => exact ⟨1, u, by simp, hu.squarefree⟩
  | mul z p hz hp ih =>
    obtain ⟨e, d, rfl, hd⟩ := ih
    by_cases hpd : p ∣ d
    · obtain ⟨d', rfl⟩ := hpd
      exact ⟨e * p, d', by simp only [pow_two]; ac_rfl, hd.of_mul_right⟩
    · refine ⟨e, d * p, by ac_rfl, ?_⟩
      rw [squarefree_mul_iff]
      exact ⟨(hp.isRelPrime_iff_not_dvd.mpr hpd).symm, hd, hp.squarefree⟩

end UniqueFactorizationMonoid

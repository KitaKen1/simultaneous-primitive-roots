/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean, for Lean/Mathlib v4.33.1. -/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

public section

namespace Multiset

lemma esymm_of_card_lt {R : Type*} [CommSemiring R] {s : Multiset R} {n : ℕ}
    (h : s.card < n) : s.esymm n = 0 := by
  simp [esymm, powersetCard_eq_empty _ h]

end Multiset

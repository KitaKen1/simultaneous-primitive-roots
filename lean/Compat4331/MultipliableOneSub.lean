/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/Analysis/SpecialFunctions/Log/Summable.lean, for Lean/Mathlib v4.33.1. -/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable

public section

variable {ι : Type*} {R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → R}

lemma multipliable_one_sub_of_summable [CompleteSpace R] (hf : Summable fun i ↦ ‖f i‖) :
    Multipliable fun i ↦ (1 - f i) := by
  have : Summable fun i ↦ ‖-f i‖ := by simpa using hf
  simpa [← sub_eq_add_neg] using multipliable_one_add_of_summable this

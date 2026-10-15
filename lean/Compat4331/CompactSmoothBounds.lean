/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/Analysis/Calculus/ContDiff/Basic.lean, for Lean/Mathlib v4.33.1. -/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Data.Finset.Lattice.Fold

public section

open scoped ContDiff

/-- The iterated derivatives up to order `m` of a smooth compactly supported function are
uniformly bounded. -/
lemma HasCompactSupport.exists_bound_iteratedFDeriv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
    (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key (i : ℕ) : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  let A : ℕ → ℝ := fun i => Classical.choose (key i)
  have hA (i : ℕ) (y : E) : ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ A i :=
    Classical.choose_spec (key i) y
  let C : ℝ := max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro i hi y
  exact (hA i y).trans
    ((Finset.le_sup' A (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))).trans (le_max_right _ _))

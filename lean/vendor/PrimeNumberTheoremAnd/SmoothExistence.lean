/-
Compatibility module for `PrimeNumberTheoremAnd/SmoothExistence.lean` as patched by openai/math
(`lean/patches/PrimeNumberTheoremAnd-lean4341.patch`, which reduces the upstream file to the single
declaration `smooth_urysohn_support_Ioo`). The statement is the one in that patch; the proof is the
vendored `Erdos970.smooth_urysohn_support_Ioo`, which the same patch adds with the same statement.
Imported by `ArtinPrimitiveRoots.Ext.SplittingInputs` (cadamcat/artin-primitive-roots-lean4).
-/
import PrimeNumberTheoremAnd.Erdos970.SmoothExistence

open scoped ContDiff

/-- A smooth Urysohn function: `1` on `[b, c]`, with support exactly `(a, d)`. -/
theorem smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) :=
  Erdos970.smooth_urysohn_support_Ioo h1 h3

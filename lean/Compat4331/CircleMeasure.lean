/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2,
   Mathlib/MeasureTheory/Group/Circle.lean, for Lean/Mathlib v4.33.1. -/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

public section

namespace Circle

instance : MeasurableSpace Circle := inferInstanceAs <| MeasurableSpace <| Subtype _

instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

protected lemma measurable_coe : Measurable fun x : Circle ↦ (x : ℂ) := measurable_subtype_coe

protected lemma measurable_iff {X : Type*} [MeasurableSpace X] {f : X → Circle} :
    Measurable f ↔ Measurable fun x ↦ (f x : ℂ) := measurable_comap_iff

end Circle

/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
/- Backport of Mathlib's nonzero-ideal finite-quotient instance for v4.33.1. -/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

public section

namespace Ring.HasFiniteQuotients

instance instFiniteIdealQuotient4331 {R : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    {I : Ideal R} [NeZero I] : Finite (R ⧸ I) :=
  finiteQuotient (NeZero.ne I)

end Ring.HasFiniteQuotients

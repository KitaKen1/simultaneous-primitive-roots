/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
/- Backport for Lean/Mathlib v4.33.1 from Mathlib f6090c7. -/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

public section

open scoped ComplexOrder

namespace Matrix
variable {𝕜 n : Type*} [RCLike 𝕜]

lemma posSemidef_is_closed : IsClosed {A : Matrix n n 𝕜 | A.PosSemidef} := by
  rw [show {A | A.PosSemidef} = {A : Matrix n n 𝕜 | A.IsHermitian} ∩
    ⋂ x : n →₀ 𝕜, {A | 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj} by aesop]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · refine isClosed_iInter <| fun _ ↦ isClosed_le continuous_const ?_
    simp only [Finsupp.sum]
    fun_prop

end Matrix

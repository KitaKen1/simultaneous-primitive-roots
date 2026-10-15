/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
/- Backport from Mathlib f6090c7 for Lean/Mathlib v4.33.1. -/
module
public import Mathlib.RingTheory.Ideal.Pointwise

public section
open scoped Pointwise
namespace Ideal
variable {M : Type*} [Group M]

@[simp] theorem mem_inertia {R : Type*} [Ring R] [MulSemiringAction M R]
    {I : Ideal R} {σ : M} : σ ∈ I.inertia M ↔ ∀ x, σ • x - x ∈ I := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
theorem inertia_smul {R : Type*} [Ring R] [MulSemiringAction M R]
    (g : M) (I : Ideal R) : (g • I).inertia M = (I.inertia M).map (MulAut.conj g) := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · rw [mem_inertia] at hx ⊢
      intro y
      have h := (mem_pointwise_smul_iff_inv_smul_mem).mp (hx (g • y))
      simpa [mul_smul, smul_sub] using h
    · simp [MulAut.conj_apply, mul_assoc]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [mem_inertia] at hy ⊢
    intro z
    rw [mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.conj_apply, mul_smul, smul_sub] using hy (g⁻¹ • z)

end Ideal

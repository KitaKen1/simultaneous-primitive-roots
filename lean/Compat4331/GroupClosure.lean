/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Algebra.Group.Pointwise

/-! A closure formula for a group neighborhood basis using the v4.33.1 basis API. -/

public section

open Filter Set
open scoped Topology Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem Filter.HasBasis.iInter_mul_right_eq_closure {ι : Type*} {s : Set G} {p : ι → Prop}
    {U : ι → Set G} (hU : (𝓝 1).HasBasis p U) :
    (⋂ (i) (_ : p i), s * U i) = closure s := by
  ext x
  have hinv : Filter.map Inv.inv (𝓝 (1 : G)) = 𝓝 1 := by
    change (𝓝 (1 : G))⁻¹ = 𝓝 1
    rw [← nhds_inv, inv_one]
  have hmap : Filter.map ((x * ·) ∘ Inv.inv) (𝓝 (1 : G)) = 𝓝 x := by
    rw [← Filter.map_map, hinv, map_mul_left_nhds_one]
  have hbasis : (𝓝 x).HasBasis p (fun i ↦ (fun u ↦ x * u⁻¹) '' U i) := by
    have h := hU.map ((x * ·) ∘ Inv.inv)
    rw [hmap] at h
    simpa only [Function.comp_def] using h
  simp only [Set.mem_iInter, mem_closure_iff_nhds_basis hbasis]
  refine forall₂_congr fun i hi ↦ ⟨?_, ?_⟩
  · rintro ⟨a, ha, b, hbi, rfl⟩
    exact ⟨a, ha, b, hbi, by simp⟩
  · rintro ⟨y, hy, b, hbi, heq⟩
    exact ⟨y, hy, b, hbi, by rw [← heq]; simp⟩

module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostRowBounds
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SurvivorPermutations

/-!
# Continuing zero hits in actual ghost deletion

All counts refer to positions. Selecting a old zero-hit positions leaves
exactly the survivor zero count; arbitrary complement enumeration is retained.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I J P : Type*} {R : P → Type*} {k a : ℕ}

attribute [local instance] Classical.propDecidable

theorem ghost_zero_count_eq_sum [Fintype I] [∀ p, Zero (R p)]
    (x : I → Σ p, R p) :
    ghostZeroCount x = ∑ i, if (x i).2 = 0 then (1 : ℕ) else 0 := by
  classical
  simp [ghostZeroCount]

/-- A position equivalence preserves zero-hit multiplicity. -/
theorem ghost_zero_count_equiv [Fintype I] [Fintype J] [∀ p, Zero (R p)]
    (e : I ≃ J) (x : J → Σ p, R p) : ghostZeroCount (x ∘ e) = ghostZeroCount x := by
  classical
  simp only [ghost_zero_count_eq_sum, Function.comp_apply]
  exact e.sum_comp (fun i => if (x i).2 = 0 then (1 : ℕ) else 0)

/-- The partition bijection splits the actual count into survivor and selected counts. -/
theorem ghost_zero_count_rebuild [∀ p, Zero (R p)] (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Σ p, R p) (p : Fin a → Σ p, R p) :
    ghostZeroCount ((retrievalCoordinates e).symm (u, p)) =
      ghostZeroCount u + ghostZeroCount p := by
  classical
  simp only [ghost_zero_count_eq_sum]
  rw [← (retrievalPartition e).sum_comp
    (fun i => if (((retrievalCoordinates e).symm (u, p)) i).2 = 0 then (1 : ℕ) else 0),
    Fintype.sum_sum_type]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : Σ p, R p => if z.2 = 0 then (1 : ℕ) else 0)
      (retrievalCoordinates_rebuild_position e u p (Sum.inl i))
  · apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : Σ p, R p => if z.2 = 0 then (1 : ℕ) else 0)
      (retrievalCoordinates_rebuild_position e u p (Sum.inr i))

theorem ghost_zero_count_all_zero [Fintype I] [∀ p, Zero (R p)]
    (x : I → Σ p, R p) (hx : ∀ i, (x i).2 = 0) : ghostZeroCount x = Fintype.card I := by
  classical
  rw [ghost_zero_count_eq_sum]
  simp [hx]

/-- The continuing-hit exponent in the actual row is exactly the survivor count. -/
theorem ghost_continuing_count_rebuild [∀ p, Zero (R p)] (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Σ p, R p) (p : Fin a → Σ p, R p) (hp : ∀ i, (p i).2 = 0) :
    ghostZeroCount ((retrievalCoordinates e).symm (u, p)) - a = ghostZeroCount u := by
  rw [ghost_zero_count_rebuild, ghost_zero_count_all_zero p hp, Fintype.card_fin,
    Nat.add_sub_cancel]

/-- Eligibility of the actual selected position set is eligibility of each indexed slot. -/
theorem ghost_selected_zero_iff [∀ p, Zero (R p)] (e : Fin a ↪ Fin (k + a))
    (x : Fin (k + a) → Σ p, R p) :
    (∀ i ∈ Finset.univ.map e, (x i).2 = 0) ↔ ∀ h, (x (e h)).2 = 0 := by
  classical
  simp only [Finset.forall_mem_map, Finset.mem_univ, forall_const]

theorem ghost_selected_zero_rebuild_iff [∀ p, Zero (R p)] (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Σ p, R p) (p : Fin a → Σ p, R p) :
    (∀ i ∈ Finset.univ.map e, (((retrievalCoordinates e).symm (u, p)) i).2 = 0) ↔
      ∀ h, (p h).2 = 0 := by
  rw [ghost_selected_zero_iff]
  apply forall_congr'
  intro h
  exact eq_iff_iff.mp (congrArg (fun z : Σ p, R p => z.2 = 0)
    (retrievalCoordinates_rebuild_selected e u p h))

/-- Old-memory/subset permutation preserves the actual ghost deletion eligibility. -/
theorem ghost_selected_zero_permutation_iff [∀ p, Zero (R p)]
    (σ : Equiv.Perm (Fin (k + a))) (s : Finset (Fin (k + a)))
    (x : Fin (k + a) → Σ p, R p) :
    (∀ i ∈ s.map σ.toEmbedding, ((x ∘ σ.symm) i).2 = 0) ↔
      ∀ i ∈ s, (x i).2 = 0 := by
  classical
  rw [Finset.forall_mem_map]
  change (∀ i ∈ s, (((x ∘ σ.symm) ∘ σ) i).2 = 0) ↔ ∀ i ∈ s, (x i).2 = 0
  have h : (x ∘ σ.symm) ∘ σ = x := by
    funext i
    exact congrArg x (σ.symm_apply_apply i)
  rw [h]

end SimultaneousPrimitiveRoots.Unconditional.Graph

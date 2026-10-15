module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.IndexedMemory
public import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.Ring

/-!
# Finite joint edge measure under reversal

For each finite memory-size sector, residue translation preserves the survivor
product weight, while reversal exchanges the promotion and storage tuples.
Tests may depend jointly on both endpoint memories, so endpoint restrictions
and their transposes are included. This is an exact finite identity, not a
proof of the infinite memory operator or its conditional norm bound.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {k a b : ℕ} {Z P K : Type*}

/-- Coordinatewise maps commute with concatenation of the two memory blocks. -/
theorem memoryJoin_map (T : Z → Z) (u : Fin k → Z) (p : Fin a → Z) :
    T ∘ memoryJoin u p = memoryJoin (T ∘ u) (T ∘ p) := by
  funext i
  simp only [memoryJoin, Function.comp_apply]
  cases finSumFinEquiv.symm i <;> rfl

/-- A measure-preserving particle bijection preserves every survivor product. -/
theorem memory_translation_weight [CommMonoid K] (T : Z ≃ Z) (w : Z → K)
    (hw : ∀ z, w (T z) = w z) (u : Fin k → Z) :
    (∏ i, w ((T ∘ u) i)) = ∏ i, w (u i) := by
  simp only [Function.comp_apply, hw]

/-- Joint finite edge sum with arbitrary tests on both endpoint memories.
`promote` and `store` include their required residue anchors. -/
noncomputable def finiteEdgeJointSum [CommSemiring K] [Fintype Z] [Fintype P]
    (w : Z → K) (ν : P → K) (promote store : P → Z) (T : Z ≃ Z)
    (E : (Fin (k + a) → Z) → (Fin (k + b) → Z) → K) : K := by
  classical
  exact ∑ u : Fin k → Z, ∑ p : Fin a → P, ∑ s : Fin b → P,
    (∏ i, w (u i)) * (∏ h, ν (p h)) * (∏ h, ν (s h)) *
      E (memoryJoin u (promote ∘ p)) (memoryJoin (T ∘ u) (store ∘ s))

/-- Reversal exchanges stores and promotions and transposes every joint restriction.
The survivor and prime-label weights are unchanged, without distinctness of values. -/
theorem finite_edge_joint_reversal [CommSemiring K] [Fintype Z] [Fintype P]
    (w : Z → K) (ν : P → K) (promote store : P → Z) (T : Z ≃ Z)
    (hw : ∀ z, w (T z) = w z)
    (E : (Fin (k + a) → Z) → (Fin (k + b) → Z) → K) :
    finiteEdgeJointSum w ν promote store T E =
      finiteEdgeJointSum w ν store promote T.symm (fun y x => E x y) := by
  classical
  let τ : (Fin k → Z) ≃ (Fin k → Z) := (Equiv.refl _).arrowCongr T.symm
  have hw' : ∀ z, w (T.symm z) = w z := fun z => by
    simpa only [Equiv.apply_symm_apply] using (hw (T.symm z)).symm
  unfold finiteEdgeJointSum
  rw [← τ.sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ p : Fin a → P, ∑ s : Fin b → P,
    (∏ i, w ((T.symm ∘ u) i)) * (∏ h, ν (p h)) * (∏ h, ν (s h)) *
      E (memoryJoin (T.symm ∘ u) (promote ∘ p))
        (memoryJoin (T ∘ (T.symm ∘ u)) (store ∘ s))) = _
  have hu : T ∘ (T.symm ∘ u) = u := by
    funext i
    exact T.apply_symm_apply (u i)
  rw [memory_translation_weight T.symm w hw', hu, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Residue translation with a different additive residue group at each prime. -/
def residueTranslation {R : P → Type*} [∀ p, AddGroup (R p)]
    (δ : ∀ p, R p) : (Σ p, R p) ≃ (Σ p, R p) :=
  Equiv.sigmaCongrRight (fun p => Equiv.addLeft (δ p))

/-- Counting residue mass carries the prime weight unchanged by translation. -/
theorem residue_translation_weight {R : P → Type*} [∀ p, AddGroup (R p)]
    (δ : ∀ p, R p) (ν : P → K) (z : Σ p, R p) :
    ν ((residueTranslation δ z).1) = ν z.1 := rfl

/-- The actual anchored residue edge has the same finite joint measure on reversal.
At each prescribed anchor counting measure selects one point; no inverse residue
cardinality is introduced. The prime labels may repeat across indexed particles. -/
theorem residue_edge_joint_reversal {R : P → Type*} [∀ p, AddGroup (R p)]
    [CommSemiring K] [Fintype P] [∀ p, Fintype (R p)]
    (δ : ∀ p, R p) (ν : P → K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K) :
    finiteEdgeJointSum (fun z : Σ p, R p => ν z.1) ν
      (fun p => ⟨p, -δ p⟩) (fun p => ⟨p, δ p⟩) (residueTranslation δ) E =
    finiteEdgeJointSum (fun z : Σ p, R p => ν z.1) ν
      (fun p => ⟨p, δ p⟩) (fun p => ⟨p, -δ p⟩) (residueTranslation δ).symm
      (fun y x => E x y) :=
  finite_edge_joint_reversal _ ν _ _ (residueTranslation δ)
    (residue_translation_weight δ ν) E

end SimultaneousPrimitiveRoots.Unconditional.Graph

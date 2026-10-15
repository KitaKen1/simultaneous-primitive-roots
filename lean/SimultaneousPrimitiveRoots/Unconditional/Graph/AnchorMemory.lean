module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.IndexedMemory

/-!
# Forced anchors in counting residue measure

A particle alphabet is the dependent sum of the residue alphabets at its prime
labels. Splitting a tuple into labels and residues is an actual bijection.
Forcing each residue to one prescribed anchor leaves precisely one prime weight
per indexed particle, even when prime labels repeat. No inverse residue
cardinality occurs. Full ghost operators and norm bounds remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I P K : Type*} {R : P → Type*} {k a : ℕ}

attribute [local instance] Classical.propDecidable

/-- Prime and residue coordinates of a particle tuple, retaining all positions. -/
def memoryPrimeResidueCoordinates :
    (I → Σ p, R p) ≃ (Σ q : I → P, ∀ i, R (q i)) where
  toFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  invFun qr := fun i => ⟨qr.1 i, qr.2 i⟩
  left_inv x := by
    funext i
    rfl
  right_inv qr := by
    cases qr
    rfl

/-- A prime tuple with each residue fixed at its prescribed anchor. -/
def anchoredMemory (α : ∀ p, R p) (q : I → P) : I → Σ p, R p :=
  fun i => ⟨q i, α (q i)⟩

/-- A forced residue is one point of counting measure and leaves its prime weight. -/
theorem anchor_point_counting [CommSemiring K] [Fintype P] [∀ p, Fintype (R p)]
    (ν : P → K) (α : ∀ p, R p) (F : (Σ p, R p) → K) :
    (∑ z : Σ p, R p, ν z.1 * F z *
      (if z.2 = α z.1 then 1 else 0)) = ∑ p, ν p * F ⟨p, α p⟩ := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Simultaneously forcing all anchors retains indexed multiplicities exactly. -/
theorem anchor_tuple_counting [CommSemiring K] [Fintype I] [Fintype P]
    [∀ p, Fintype (R p)] (ν : P → K) (α : ∀ p, R p)
    (F : (I → Σ p, R p) → K) :
    (∑ x : I → Σ p, R p, (∏ i, ν (x i).1) * F x *
      (if ∀ i, (x i).2 = α (x i).1 then 1 else 0)) =
      ∑ q : I → P, (∏ i, ν (q i)) * F (anchoredMemory α q) := by
  classical
  rw [← memoryPrimeResidueCoordinates.symm.sum_comp
    (fun x : I → Σ p, R p => (∏ i, ν (x i).1) * F x *
      (if ∀ i, (x i).2 = α (x i).1 then 1 else 0)), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  change (∑ r : ∀ i, R (q i), (∏ i, ν (q i)) * F (fun i => ⟨q i, r i⟩) *
    (if ∀ i, r i = α (q i) then 1 else 0)) = _
  simp_rw [← funext_iff, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

/-- Indexed retrieval of an anchored prime tuple leaves one prime factor per slot. -/
theorem ordered_anchor_retrieval_joint_sum [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [DecidableEq P] [∀ p, DecidableEq (R p)]
    (ν : P → K) (α : ∀ p, R p)
    (F : (Fin (k + a) → Σ p, R p) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) (x : Fin (k + a) → Σ p, R p),
      F (x ∘ σ) = F x) (q : Fin a → P) :
    (∑ e : Fin a ↪ Fin (k + a), ∑ x : Fin (k + a) → Σ p, R p,
      (∏ i, ν (x i).1) * F x *
        (if (fun h => x (e h)) = anchoredMemory α q then 1 else 0)) /
          ((k + a).factorial : K) =
    (∑ u : Fin k → Σ p, R p,
      (∏ i, ν (u i).1) * (∏ h, ν (q h)) * F (memoryJoin u (anchoredMemory α q))) /
        (k.factorial : K) := by
  classical
  simpa only [anchoredMemory] using
    ordered_retrieval_fixed_tuple (fun z : Σ p, R p => ν z.1) F hF (anchoredMemory α q)

end SimultaneousPrimitiveRoots.Unconditional.Graph

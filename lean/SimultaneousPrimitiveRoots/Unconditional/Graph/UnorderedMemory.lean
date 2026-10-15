module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.IndexedMemory
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Unordered choices retain their indexed multiplicities

The range of an ordered retrieval is an unordered subset of old positions.
Each subset of size a has a! enumerations, independent of particle values.
This is the required conversion from indexed ordered sums to actual ghost
deletion subsets; it does not replace repeated numerical values by a set.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I K : Type*} {a : ℕ} [Fintype I] [DecidableEq I]

/-- The fiber of the position range consists exactly of all its enumerations. -/
noncomputable def retrievalRangeFiberEquiv (s : Finset I) :
    {e : Fin a ↪ I // Finset.univ.map e = s} ≃ (Fin a ≃ s) := by
  classical
  refine
    { toFun := fun e => Equiv.ofBijective
        (fun i => ⟨e.1 i, ?_⟩) ⟨?_, ?_⟩
      invFun := fun f => ⟨f.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hm : e.1 i ∈ Finset.univ.map e.1 :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact (congrArg (fun t : Finset I => e.1 i ∈ t) e.2).mp hm
  · intro i j hij
    exact e.1.injective (congrArg Subtype.val hij)
  · intro x
    have hx : x.1 ∈ Finset.univ.map e.1 := by simpa only [e.2] using x.2
    rw [Finset.mem_map] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact ⟨i, Subtype.ext hi⟩
  · ext i
    constructor
    · intro hi
      obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
      exact hj ▸ (f j).2
    · intro hi
      obtain ⟨j, hj⟩ := f.surjective ⟨i, hi⟩
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
  · intro e
    apply Subtype.ext
    ext i
    rfl
  · intro f
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

/-- Exactly a! ordered choices have a given unordered position subset of size a. -/
theorem retrieval_range_fiber_card (s : Finset I) :
    Fintype.card {e : Fin a ↪ I // Finset.univ.map e = s} =
      if s.card = a then a.factorial else 0 := by
  classical
  by_cases hs : s.card = a
  · rw [if_pos hs, Fintype.card_congr (retrievalRangeFiberEquiv s),
      Fintype.card_equiv (s.equivFinOfCardEq hs).symm, Fintype.card_fin]
  · rw [if_neg hs]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun e => hs ?_⟩
    rw [← e.2, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Summing ordered retrievals counts every unordered subset exactly a! times. -/
theorem retrieval_range_sum [CommSemiring K] (G : Finset I → K) :
    (∑ e : Fin a ↪ I, G (Finset.univ.map e)) =
      (a.factorial : K) * ∑ s : Finset I with s.card = a, G s := by
  classical
  rw [← Fintype.sum_fiberwise' (fun e : Fin a ↪ I => Finset.univ.map e) G]
  simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, retrieval_range_fiber_card]
  calc
    _ = ∑ s : Finset I, if s.card = a then (a.factorial : K) * G s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    _ = (a.factorial : K) * ∑ s : Finset I with s.card = a, G s := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]

/-- The actual unordered position-subset sum has the ghost factorial joint weight.
Coefficients must be equivariant under simultaneous position/subset permutations. -/
theorem unordered_equivariant_deletion_joint_sum
    {k : ℕ} {Z : Type*} [Fintype Z] [Field K] [CharZero K] (w : Z → K)
    (L : Finset (Fin (k + a)) → (Fin (k + a) → Z) → K)
    (hL : ∀ (σ : Equiv.Perm (Fin (k + a)))
      (s : Finset (Fin (k + a))) (x : Fin (k + a) → Z),
      L (s.map σ.toEmbedding) (x ∘ σ.symm) = L s x) :
    (∑ s : Finset (Fin (k + a)) with s.card = a,
      ∑ x : Fin (k + a) → Z, (∏ i, w (x i)) * L s x) / ((k + a).factorial : K) =
    (∑ u : Fin k → Z, ∑ p : Fin a → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) *
        L (Finset.univ.map (Fin.natAddEmb k)) (memoryJoin u p)) /
          ((k.factorial : K) * (a.factorial : K)) := by
  classical
  have hh := ordered_equivariant_retrieval_joint_sum w
    (fun e x => L (Finset.univ.map e) x) (fun σ e x => by
      simpa only [Finset.map_map] using hL σ (Finset.univ.map e) x)
  rw [retrieval_range_sum (fun s => ∑ x : Fin (k + a) → Z,
    (∏ i, w (x i)) * L s x)] at hh
  have hj : ((k + a).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have ha : (a.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply (div_eq_div_iff hj (mul_ne_zero hk ha)).mpr
  have hc := (div_eq_div_iff hj hk).mp hh
  calc
    _ = ((a.factorial : K) * (∑ s : Finset (Fin (k + a)) with s.card = a,
      ∑ x : Fin (k + a) → Z, (∏ i, w (x i)) * L s x)) * (k.factorial : K) := by ring
    _ = _ := hc

end SimultaneousPrimitiveRoots.Unconditional.Graph

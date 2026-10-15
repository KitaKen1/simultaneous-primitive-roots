module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.FactorialMemory
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Indexed retrieval and finite joint sums

Memory coordinates are positions, not distinct particle values. An ordered
retrieval is an embedding of its prescribed slots into the old positions.
Splitting off those positions is a bijection even when particle values repeat.
These finite identities are prerequisites for the full measure-theoretic
memory adjoint and its conditional norm bounds.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {k a : ℕ} {Z : Type*}

/-- The positions surviving an ordered retrieval have exactly the expected size. -/
theorem retrieval_complement_card (e : Fin a ↪ Fin (k + a)) :
    Fintype.card ↥(Set.range e)ᶜ = k := by
  classical
  rw [Fintype.card_compl_set, Fintype.card_range, Fintype.card_fin,
    Fintype.card_fin, Nat.add_sub_cancel_right]

/-- An arbitrary enumeration of the surviving positions; no particle is identified. -/
noncomputable def retrievalComplementEquiv (e : Fin a ↪ Fin (k + a)) :
    ↥(Set.range e)ᶜ ≃ Fin k := by
  classical
  exact Fintype.equivFinOfCardEq (retrieval_complement_card e)

/-- Surviving positions first, then the ordered selected positions. -/
noncomputable def retrievalPartition (e : Fin a ↪ Fin (k + a)) :
    Fin k ⊕ Fin a ≃ Fin (k + a) := by
  classical
  exact (Equiv.sumComm _ _).trans <|
    ((Equiv.ofInjective e e.injective).sumCongr
      (retrievalComplementEquiv e).symm).trans (Equiv.Set.sumCompl (Set.range e))

/-- Selected coordinates retain their prescribed order. -/
theorem retrievalPartition_selected (e : Fin a ↪ Fin (k + a)) (i : Fin a) :
    retrievalPartition e (Sum.inr i) = e i := by
  classical
  simp [retrievalPartition]

/-- A genuine bijection from an old memory to survivor and retrieval tuples. -/
noncomputable def retrievalCoordinates (e : Fin a ↪ Fin (k + a)) :
    (Fin (k + a) → Z) ≃ (Fin k → Z) × (Fin a → Z) :=
  ((retrievalPartition e).symm.arrowCongr (Equiv.refl Z)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The second tuple is evaluation at the chosen indices, including repeats of values. -/
theorem retrievalCoordinates_selected (e : Fin a ↪ Fin (k + a))
    (x : Fin (k + a) → Z) (i : Fin a) :
    (retrievalCoordinates e x).2 i = x (e i) := by
  simp [retrievalCoordinates, Equiv.arrowCongr, retrievalPartition_selected]

/-- Rebuilding a memory recovers every ordered selected value. -/
theorem retrievalCoordinates_rebuild_selected (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Z) (p : Fin a → Z) (i : Fin a) :
    (retrievalCoordinates e).symm (u, p) (e i) = p i := by
  have h := retrievalCoordinates_selected e ((retrievalCoordinates e).symm (u, p)) i
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Reconstruction is exactly the inverse position change on both blocks. -/
theorem retrievalCoordinates_rebuild_position (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Z) (p : Fin a → Z) (i : Fin k ⊕ Fin a) :
    (retrievalCoordinates e).symm (u, p) (retrievalPartition e i) =
      Sum.elim u p i := by
  simp [retrievalCoordinates, Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]

/-- Product weights split under the position bijection, including repeated values. -/
theorem retrieval_product_weight {K : Type*} [CommMonoid K]
    (e : Fin a ↪ Fin (k + a)) (w : Z → K) (u : Fin k → Z) (p : Fin a → Z) :
    (∏ i, w ((retrievalCoordinates e).symm (u, p) i)) =
      (∏ i, w (u i)) * ∏ h, w (p h) := by
  rw [← (retrievalPartition e).prod_comp
    (fun i => w ((retrievalCoordinates e).symm (u, p) i)), Fintype.prod_sum_type]
  simp only [retrievalCoordinates_rebuild_position, Sum.elim_inl, Sum.elim_inr]

/-- Finite product-measure change of variables for a fixed ordered retrieval. -/
theorem retrieval_joint_sum {K : Type*} [CommSemiring K] [Fintype Z]
    (e : Fin a ↪ Fin (k + a)) (w : Z → K)
    (F : (Fin (k + a) → Z) → K) (H : (Fin a → Z) → K) :
    (∑ x : Fin (k + a) → Z,
      (∏ i, w (x i)) * F x * H (fun h => x (e h))) =
    ∑ u : Fin k → Z, ∑ p : Fin a → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) *
        F ((retrievalCoordinates e).symm (u, p)) * H p := by
  classical
  rw [← (retrievalCoordinates (Z := Z) e).symm.sum_comp
    (fun x => (∏ i, w (x i)) * F x * H (fun h => x (e h))), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro p _
  rw [retrieval_product_weight]
  congr 1
  congr 1
  funext h
  exact retrievalCoordinates_rebuild_selected e u p h

/-- Canonical concatenation of survivor and selected tuples. -/
def memoryJoin (u : Fin k → Z) (p : Fin a → Z) : Fin (k + a) → Z :=
  Sum.elim u p ∘ finSumFinEquiv.symm

/-- A symmetric test has the same value in every indexed reconstruction. -/
theorem retrieval_rebuild_symmetric {K : Type*}
    (F : (Fin (k + a) → Z) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) (x : Fin (k + a) → Z),
      F (x ∘ σ) = F x)
    (e : Fin a ↪ Fin (k + a)) (u : Fin k → Z) (p : Fin a → Z) :
    F ((retrievalCoordinates e).symm (u, p)) = F (memoryJoin u p) := by
  let σ : Equiv.Perm (Fin (k + a)) := (retrievalPartition e).symm.trans finSumFinEquiv
  have hx : (retrievalCoordinates e).symm (u, p) = memoryJoin u p ∘ σ := by
    funext i
    simp [retrievalCoordinates, memoryJoin, Equiv.arrowCongr,
      Equiv.sumArrowEquivProdArrow, σ]
  rw [hx]
  exact hF σ (memoryJoin u p)

/-- The fixed-retrieval joint sum is independent of the chosen old positions. -/
theorem retrieval_joint_sum_symmetric {K : Type*} [CommSemiring K] [Fintype Z]
    (w : Z → K) (F : (Fin (k + a) → Z) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) (x : Fin (k + a) → Z),
      F (x ∘ σ) = F x)
    (H : (Fin a → Z) → K) (e : Fin a ↪ Fin (k + a)) :
    (∑ x : Fin (k + a) → Z,
      (∏ i, w (x i)) * F x * H (fun h => x (e h))) =
    ∑ u : Fin k → Z, ∑ p : Fin a → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) * F (memoryJoin u p) * H p := by
  rw [retrieval_joint_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro p _
  rw [retrieval_rebuild_symmetric F hF]

/-- Summing all indexed retrievals cancels the old memory factorial exactly. -/
theorem ordered_retrieval_joint_sum {K : Type*} [Field K] [CharZero K] [Fintype Z]
    (w : Z → K) (F : (Fin (k + a) → Z) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) (x : Fin (k + a) → Z),
      F (x ∘ σ) = F x)
    (H : (Fin a → Z) → K) :
    (∑ e : Fin a ↪ Fin (k + a), ∑ x : Fin (k + a) → Z,
      (∏ i, w (x i)) * F x * H (fun h => x (e h))) / ((k + a).factorial : K) =
    (∑ u : Fin k → Z, ∑ p : Fin a → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) * F (memoryJoin u p) * H p) /
        (k.factorial : K) := by
  classical
  simp_rw [retrieval_joint_sum_symmetric w F hF H]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  rw [mul_comm ((k + a).descFactorial a : K), mul_div_assoc,
    ordered_retrieval_factorial (Nat.le_add_left a k), Nat.add_sub_cancel_right,
    mul_one_div]

/-- Forcing each retrieval to one required value leaves its product weight once.
The required tuple may repeat values; only the selected indices are distinct. -/
theorem ordered_retrieval_fixed_tuple {K : Type*} [Field K] [CharZero K]
    [Fintype Z] [DecidableEq Z]
    (w : Z → K) (F : (Fin (k + a) → Z) → K)
    (hF : ∀ (σ : Equiv.Perm (Fin (k + a))) (x : Fin (k + a) → Z),
      F (x ∘ σ) = F x)
    (p : Fin a → Z) :
    (∑ e : Fin a ↪ Fin (k + a), ∑ x : Fin (k + a) → Z,
      (∏ i, w (x i)) * F x *
        (if (fun h => x (e h)) = p then 1 else 0)) / ((k + a).factorial : K) =
    (∑ u : Fin k → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) * F (memoryJoin u p)) /
        (k.factorial : K) := by
  classical
  rw [ordered_retrieval_joint_sum w F hF (fun q => if q = p then 1 else 0)]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The position permutation taking this retrieval to the canonical final block. -/
noncomputable def retrievalReindex (e : Fin a ↪ Fin (k + a)) :
    Equiv.Perm (Fin (k + a)) :=
  (retrievalPartition e).symm.trans finSumFinEquiv

/-- The reindexing keeps the order of the selected slots. -/
theorem retrievalReindex_selected (e : Fin a ↪ Fin (k + a)) (i : Fin a) :
    retrievalReindex e (e i) = Fin.natAdd k i := by
  rw [← retrievalPartition_selected e i]
  simp [retrievalReindex]

/-- Reindexing the reconstructed memory gives the canonical concatenation. -/
theorem retrievalReindex_memory (e : Fin a ↪ Fin (k + a))
    (u : Fin k → Z) (p : Fin a → Z) :
    (retrievalCoordinates e).symm (u, p) ∘ (retrievalReindex e).symm =
      memoryJoin u p := by
  funext i
  simp [retrievalCoordinates, retrievalReindex, memoryJoin,
    Equiv.arrowCongr, Equiv.sumArrowEquivProdArrow]

/-- Equivariant choice coefficients obey the full indexed factorial joint identity.
This allows coefficients depending jointly on the old memory and selected indices;
arbitrary index-dependent coefficients do not satisfy the stated equivariance. -/
theorem ordered_equivariant_retrieval_joint_sum
    {K : Type*} [Field K] [CharZero K] [Fintype Z] (w : Z → K)
    (L : (Fin a ↪ Fin (k + a)) → (Fin (k + a) → Z) → K)
    (hL : ∀ (σ : Equiv.Perm (Fin (k + a)))
      (e : Fin a ↪ Fin (k + a)) (x : Fin (k + a) → Z),
      L (e.trans σ.toEmbedding) (x ∘ σ.symm) = L e x) :
    (∑ e : Fin a ↪ Fin (k + a), ∑ x : Fin (k + a) → Z,
      (∏ i, w (x i)) * L e x) / ((k + a).factorial : K) =
    (∑ u : Fin k → Z, ∑ p : Fin a → Z,
      (∏ i, w (u i)) * (∏ h, w (p h)) *
        L (Fin.natAddEmb k) (memoryJoin u p)) / (k.factorial : K) := by
  classical
  have hd (e : Fin a ↪ Fin (k + a)) :
      (∑ x : Fin (k + a) → Z, (∏ i, w (x i)) * L e x) =
        ∑ u : Fin k → Z, ∑ p : Fin a → Z,
          (∏ i, w (u i)) * (∏ h, w (p h)) *
            L (Fin.natAddEmb k) (memoryJoin u p) := by
    rw [← (retrievalCoordinates (Z := Z) e).symm.sum_comp
      (fun x => (∏ i, w (x i)) * L e x), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro p _
    have he : e.trans (retrievalReindex e).toEmbedding = Fin.natAddEmb k := by
      ext i
      exact congrArg Fin.val (retrievalReindex_selected e i)
    have hl := hL (retrievalReindex e) e ((retrievalCoordinates e).symm (u, p))
    rw [he, retrievalReindex_memory] at hl
    rw [retrieval_product_weight, hl]
  simp_rw [hd]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  rw [mul_comm ((k + a).descFactorial a : K), mul_div_assoc,
    ordered_retrieval_factorial (Nat.le_add_left a k), Nat.add_sub_cancel_right,
    mul_one_div]

end SimultaneousPrimitiveRoots.Unconditional.Graph

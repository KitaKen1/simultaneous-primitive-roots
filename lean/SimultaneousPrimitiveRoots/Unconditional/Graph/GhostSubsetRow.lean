module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostSelection
import Mathlib.Tactic.Ring

/-!
# Actual finite ghost deletion rows

This is the position-subset row of [S, eq:ghost-row], paired with a joint
endpoint test. The residue alphabet carries counting measure. Symmetry is
assumed explicitly at both Fock endpoints; repeated particle values are kept.
The infinite operator and its conditional norm estimates remain separate.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {P K : Type*} {R : P → Type*} {k a b : ℕ}

attribute [local instance] Classical.propDecidable

/-- Actual deletion coefficient for a position subset and a fixed birth sector. -/
noncomputable def finiteGhostSubsetCoefficient [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) : K := by
  classical
  exact if hs : s.card = a then
    if ∀ i ∈ s, (x i).2 = 0 then
      A ^ (ghostZeroCount x - a) *
        ∑ q : Fin b → P, (∏ i, ν (q i)) *
          E x (memoryJoin (retrievalCoordinates (subsetRetrieval s hs) x).1
            (anchoredMemory (fun p => (0 : R p)) q))
    else 0
  else 0

/-- The actual ghost coefficient is equivariant under old-position/subset transport. -/
theorem finite_ghost_subset_coefficient_covariance [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y)
    (σ : Equiv.Perm (Fin (k + a))) (s : Finset (Fin (k + a)))
    (x : Fin (k + a) → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A E (s.map σ.toEmbedding) (x ∘ σ.symm) =
      finiteGhostSubsetCoefficient ν A E s x := by
  classical
  by_cases hs : s.card = a
  · have hs' : (s.map σ.toEmbedding).card = a := by simpa only [Finset.card_map] using hs
    simp only [finiteGhostSubsetCoefficient, dif_pos hs, dif_pos hs']
    by_cases hx : ∀ i ∈ s, (x i).2 = 0
    · have hx' := (ghost_selected_zero_permutation_iff σ s x).mpr hx
      rw [if_pos hx', if_pos hx, ghost_zero_count_equiv σ.symm x]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      rw [subset_survivor_test_covariance σ s hs
        (fun y => E (x ∘ σ.symm) y) (fun π y => hEnew π _ y)]
      exact hEold σ.symm x _
    · have hx' : ¬ ∀ i ∈ s.map σ.toEmbedding, ((x ∘ σ.symm) i).2 = 0 :=
        fun h => hx ((ghost_selected_zero_permutation_iff σ s x).mp h)
      rw [if_neg hx', if_neg hx]
  · have hs' : (s.map σ.toEmbedding).card ≠ a := by simpa only [Finset.card_map] using hs
    simp only [finiteGhostSubsetCoefficient, dif_neg hs, dif_neg hs']

/-- Rebuilding the actual selected set gives exactly survivor damping and zero anchors. -/
theorem finite_ghost_subset_coefficient_rebuild [CommSemiring K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y)
    (e : Fin a ↪ Fin (k + a)) (u : Fin k → Σ p, R p) (p : Fin a → Σ p, R p) :
    finiteGhostSubsetCoefficient ν A E (Finset.univ.map e)
      ((retrievalCoordinates e).symm (u, p)) =
      if ∀ i, (p i).2 = 0 then
        A ^ ghostZeroCount u * ∑ q : Fin b → P, (∏ i, ν (q i)) *
          E (memoryJoin u p) (memoryJoin u (anchoredMemory (fun p => (0 : R p)) q))
      else 0 := by
  classical
  have hs : (Finset.univ.map e).card = a := by simp
  have he : Set.range e = Set.range (subsetRetrieval (Finset.univ.map e) hs) := by
    rw [subsetRetrieval_set_range]
    ext i
    simp
  unfold finiteGhostSubsetCoefficient
  rw [dif_pos hs]
  by_cases hp : ∀ i, (p i).2 = 0
  · rw [if_pos ((ghost_selected_zero_rebuild_iff e u p).mpr hp),
      if_pos hp, ghost_continuing_count_rebuild e u p hp]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    rw [retrieval_survivor_test_same_range e _ he
      (fun y => E ((retrievalCoordinates e).symm (u, p)) y)
      (fun σ y => hEnew σ _ y), Equiv.apply_symm_apply]
    exact retrieval_rebuild_symmetric
      (fun x => E x (memoryJoin u (anchoredMemory (fun p => (0 : R p)) q)))
      (fun σ x => hEold σ x _) e u p
  · rw [if_neg (fun hx => hp ((ghost_selected_zero_rebuild_iff e u p).mp hx)),
      if_neg hp]

/-- A fixed ordered enumeration of an actual deleted subset gives the ghost joint sum.
Forcing its residues contributes one prime weight per deleted position, without 1/p. -/
theorem finite_ghost_subset_fixed_joint_sum [CommSemiring K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y)
    (e : Fin a ↪ Fin (k + a)) :
    (∑ x : Fin (k + a) → Σ p, R p, (∏ i, ν (x i).1) *
      finiteGhostSubsetCoefficient ν A E (Finset.univ.map e) x) =
      finiteEdgeJointSum (ghostPointWeight ν A) ν
        (fun p => ⟨p, 0⟩) (fun p => ⟨p, 0⟩) (Equiv.refl _) E := by
  classical
  rw [← (retrievalCoordinates (Z := Σ p, R p) e).symm.sum_comp
    (fun x => (∏ i, ν (x i).1) *
      finiteGhostSubsetCoefficient ν A E (Finset.univ.map e) x), Fintype.sum_prod_type]
  unfold finiteEdgeJointSum
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [retrieval_product_weight e (fun z : Σ p, R p => ν z.1),
    finite_ghost_subset_coefficient_rebuild ν A E hEold hEnew e u]
  let F : (Fin a → Σ p, R p) → K := fun p =>
    A ^ ghostZeroCount u * ∑ q : Fin b → P, (∏ i, ν (q i)) *
      E (memoryJoin u p) (memoryJoin u (anchoredMemory (fun p => (0 : R p)) q))
  calc
    _ = (∏ i, ν (u i).1) * ∑ p : Fin a → Σ p, R p,
        (∏ i, ν (p i).1) * F p * (if ∀ i, (p i).2 = 0 then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      change _ = _ * (_ * (A ^ ghostZeroCount u * _) * _)
      split_ifs <;> ring
    _ = (∏ i, ν (u i).1) * ∑ p : Fin a → P,
        (∏ i, ν (p i)) * F (anchoredMemory (fun p => (0 : R p)) p) := by
      congr 1
      convert anchor_tuple_counting ν (fun p => (0 : R p)) F using 1
      all_goals
        apply Finset.sum_congr (Finset.ext (fun _ => by simp))
        intro p _
        first | rfl | (split_ifs <;> rfl)
    _ = _ := by
      simp only [F, Finset.mul_sum, ghost_survivor_weight]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      change _ = _ * _ * _ * E _ (memoryJoin u _)
      dsimp only [anchoredMemory, Function.comp_def]
      ring_nf
      rfl

/-- Summing actual unordered deletion subsets gives precisely the k!a! joint weight. -/
theorem finite_ghost_subset_factorial_joint_sum [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y) :
    (∑ s : Finset (Fin (k + a)) with s.card = a,
      ∑ x : Fin (k + a) → Σ p, R p, (∏ i, ν (x i).1) *
        finiteGhostSubsetCoefficient ν A E s x) / ((k + a).factorial : K) =
      finiteEdgeJointSum (ghostPointWeight ν A) ν
        (fun p => ⟨p, 0⟩) (fun p => ⟨p, 0⟩) (Equiv.refl _) E /
          ((k.factorial : K) * (a.factorial : K)) := by
  classical
  have hh :
      ((a.factorial : K) * ∑ s : Finset (Fin (k + a)) with s.card = a,
        ∑ x : Fin (k + a) → Σ p, R p, (∏ i, ν (x i).1) *
          finiteGhostSubsetCoefficient ν A E s x) / ((k + a).factorial : K) =
      finiteEdgeJointSum (ghostPointWeight ν A) ν
        (fun p => ⟨p, 0⟩) (fun p => ⟨p, 0⟩) (Equiv.refl _) E / (k.factorial : K) := by
    rw [← retrieval_range_sum (fun s => ∑ x : Fin (k + a) → Σ p, R p,
      (∏ i, ν (x i).1) * finiteGhostSubsetCoefficient ν A E s x)]
    simp_rw [finite_ghost_subset_fixed_joint_sum ν A E hEold hEnew]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    rw [mul_comm ((k + a).descFactorial a : K), mul_div_assoc,
      ordered_retrieval_factorial (Nat.le_add_left a k), Nat.add_sub_cancel_right,
      mul_one_div]
  have hj : ((k + a).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have ha : (a.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply (div_eq_div_iff hj (mul_ne_zero hk ha)).mpr
  have hc := (div_eq_div_iff hj hk).mp hh
  calc
    _ = ((a.factorial : K) * (∑ s : Finset (Fin (k + a)) with s.card = a,
      ∑ x : Fin (k + a) → Σ p, R p, (∏ i, ν (x i).1) *
        finiteGhostSubsetCoefficient ν A E s x)) * (k.factorial : K) := by ring
    _ = _ := hc

/-- The signed actual subset row, paired in the old factorial counting measure.
The birth factor b! is retained; D and C may have either sign. -/
noncomputable def finiteGhostSubsetJoint [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K) : K := by
  classical
  exact (D ^ a * C ^ b) *
    ((∑ s : Finset (Fin (k + a)) with s.card = a,
      ∑ x : Fin (k + a) → Σ p, R p, (∏ i, ν (x i).1) *
        finiteGhostSubsetCoefficient ν A E s x) / ((k + a).factorial : K)) /
          (b.factorial : K)

/-- Exact identification of the actual finite subset row with [S, eq:ghost-joint-integral]. -/
theorem finite_ghost_subset_joint_identification [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y) :
    finiteGhostSubsetJoint ν A D C E = finiteGhostJointSector ν A D C E := by
  classical
  unfold finiteGhostSubsetJoint finiteGhostJointSector
  rw [finite_ghost_subset_factorial_joint_sum ν A E hEold hEnew]
  rw [mul_div_assoc, div_div, ← mul_div_assoc]

/-- The actual finite ghost row transposes by interchanging deletion and creation.
Both endpoint restrictions are carried by E, with their Fock symmetry explicit. -/
theorem finite_ghost_subset_joint_reversal [Field K] [CharZero K] [Fintype P]
    [∀ p, Fintype (R p)] [∀ p, Zero (R p)] (ν : P → K) (A D C : K)
    (E : (Fin (k + a) → Σ p, R p) → (Fin (k + b) → Σ p, R p) → K)
    (hEold : ∀ (σ : Equiv.Perm (Fin (k + a))) x y, E (x ∘ σ) y = E x y)
    (hEnew : ∀ (σ : Equiv.Perm (Fin (k + b))) x y, E x (y ∘ σ) = E x y) :
    finiteGhostSubsetJoint ν A D C E =
      finiteGhostSubsetJoint ν A C D (fun y x => E x y) := by
  rw [finite_ghost_subset_joint_identification ν A D C E hEold hEnew,
    finite_ghost_sector_reversal,
    finite_ghost_subset_joint_identification ν A C D (fun y x => E x y)
      (fun σ y x => hEnew σ x y) (fun σ y x => hEold σ x y)]

end SimultaneousPrimitiveRoots.Unconditional.Graph

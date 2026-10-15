module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.UnorderedMemory

/-!
# Survivor enumeration and symmetric endpoint tests

Deleting a position subset leaves an arbitrarily enumerated complement.
This file compares the actual enumerations by index permutations, including
transport by old-memory permutations. Values need not be distinct.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

variable {k a b : ℕ} {Z K : Type*}

/-- The survivor tuple evaluates the old memory at the chosen complement enumeration. -/
theorem retrievalCoordinates_survivor (e : Fin a ↪ Fin (k + a))
    (x : Fin (k + a) → Z) (i : Fin k) :
    (retrievalCoordinates e x).1 i = x (((retrievalComplementEquiv e).symm i).1) := by
  simp [retrievalCoordinates, retrievalPartition, Equiv.arrowCongr]

/-- A survivor permutation extends to the endpoint, fixing all newly born slots. -/
def survivorBlockPermutation (τ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + b)) :=
  finSumFinEquiv.symm.trans ((τ.sumCongr (Equiv.refl (Fin b))).trans finSumFinEquiv)

theorem memoryJoin_survivor_permutation (τ : Equiv.Perm (Fin k))
    (u : Fin k → Z) (p : Fin b → Z) :
    memoryJoin (u ∘ τ) p = memoryJoin u p ∘ survivorBlockPermutation τ := by
  funext i
  simp only [memoryJoin, survivorBlockPermutation, Function.comp_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  cases finSumFinEquiv.symm i <;> rfl

/-- Symmetric endpoint tests absorb the actual survivor permutation. -/
theorem memoryJoin_survivor_symmetric (H : (Fin (k + b) → Z) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Z), H (x ∘ σ) = H x)
    (τ : Equiv.Perm (Fin k)) (u : Fin k → Z) (p : Fin b → Z) :
    H (memoryJoin (u ∘ τ) p) = H (memoryJoin u p) := by
  rw [memoryJoin_survivor_permutation]
  exact hH _ _

/-- Equal selected position ranges give a single complement permutation for all memories. -/
theorem retrieval_survivors_same_range (e f : Fin a ↪ Fin (k + a))
    (hef : Set.range e = Set.range f) :
    ∃ τ : Equiv.Perm (Fin k), ∀ x : Fin (k + a) → Z,
      (retrievalCoordinates f x).1 = (retrievalCoordinates e x).1 ∘ τ := by
  classical
  let γ : ↥(Set.range f)ᶜ ≃ ↥(Set.range e)ᶜ :=
    Equiv.setCongr (congrArg (fun s : Set (Fin (k + a)) => sᶜ) hef.symm)
  let τ : Equiv.Perm (Fin k) := (retrievalComplementEquiv f).symm.trans
    (γ.trans (retrievalComplementEquiv e))
  refine ⟨τ, fun x => ?_⟩
  funext i
  simp [Function.comp_apply, retrievalCoordinates_survivor, τ, γ]

/-- Deleting the same positions gives the same symmetric test for every survivor ordering. -/
theorem retrieval_survivor_test_same_range (e f : Fin a ↪ Fin (k + a))
    (hef : Set.range e = Set.range f) (H : (Fin (k + b) → Z) → K)
    (hH : ∀ (σ : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Z), H (x ∘ σ) = H x)
    (x : Fin (k + a) → Z) (p : Fin b → Z) :
    H (memoryJoin (retrievalCoordinates f x).1 p) =
      H (memoryJoin (retrievalCoordinates e x).1 p) := by
  obtain ⟨τ, hτ⟩ := retrieval_survivors_same_range (Z := Z) e f hef
  rw [hτ x]
  exact memoryJoin_survivor_symmetric H hH τ _ p

/-- Transport the complement itself by an old-position permutation. -/
def retrievalComplementMap (σ : Equiv.Perm (Fin (k + a))) (e : Fin a ↪ Fin (k + a)) :
    ↥(Set.range e)ᶜ ≃ ↥(Set.range (e.trans σ.toEmbedding))ᶜ where
  toFun x := ⟨σ x.1, by
    rintro ⟨i, hi⟩
    exact x.2 ⟨i, σ.injective hi⟩⟩
  invFun x := ⟨σ.symm x.1, by
    rintro ⟨i, hi⟩
    apply x.2
    refine ⟨i, ?_⟩
    change σ (e i) = x.1
    rw [hi, Equiv.apply_symm_apply]⟩
  left_inv x := by apply Subtype.ext; exact σ.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact σ.apply_symm_apply x.1

/-- Transported retrieval coordinates differ only by a survivor permutation. -/
theorem retrieval_survivors_permutation_covariance
    (σ : Equiv.Perm (Fin (k + a))) (e : Fin a ↪ Fin (k + a)) :
    ∃ τ : Equiv.Perm (Fin k), ∀ x : Fin (k + a) → Z,
      (retrievalCoordinates (e.trans σ.toEmbedding) (x ∘ σ.symm)).1 =
        (retrievalCoordinates e x).1 ∘ τ := by
  let τ : Equiv.Perm (Fin k) :=
    (retrievalComplementEquiv (e.trans σ.toEmbedding)).symm.trans
      ((retrievalComplementMap σ e).symm.trans (retrievalComplementEquiv e))
  refine ⟨τ, fun x => ?_⟩
  funext i
  simp [Function.comp_apply, retrievalCoordinates_survivor, τ, retrievalComplementMap]

/-- The actual transported survivor test is equivariant, independently of complement order. -/
theorem retrieval_survivor_test_covariance
    (σ : Equiv.Perm (Fin (k + a))) (e f : Fin a ↪ Fin (k + a))
    (hef : Set.range f = Set.range (e.trans σ.toEmbedding))
    (H : (Fin (k + b) → Z) → K)
    (hH : ∀ (π : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Z), H (x ∘ π) = H x)
    (x : Fin (k + a) → Z) (p : Fin b → Z) :
    H (memoryJoin (retrievalCoordinates f (x ∘ σ.symm)).1 p) =
      H (memoryJoin (retrievalCoordinates e x).1 p) := by
  rw [retrieval_survivor_test_same_range (e.trans σ.toEmbedding) f hef.symm H hH]
  obtain ⟨τ, hτ⟩ := retrieval_survivors_permutation_covariance (Z := Z) σ e
  rw [hτ x]
  exact memoryJoin_survivor_symmetric H hH τ _ p

/-- Choose an ordered enumeration of an actual deleted position subset. -/
noncomputable def subsetRetrieval (s : Finset (Fin (k + a))) (hs : s.card = a) :
    Fin a ↪ Fin (k + a) :=
  ((retrievalRangeFiberEquiv s).symm ((s.equivFinOfCardEq hs).symm)).1

theorem subsetRetrieval_range (s : Finset (Fin (k + a))) (hs : s.card = a) :
    Finset.univ.map (subsetRetrieval s hs) = s :=
  ((retrievalRangeFiberEquiv s).symm ((s.equivFinOfCardEq hs).symm)).2

theorem subsetRetrieval_set_range (s : Finset (Fin (k + a))) (hs : s.card = a) :
    Set.range (subsetRetrieval s hs) = (s : Set (Fin (k + a))) := by
  classical
  ext i
  have h := congrArg (fun t : Finset (Fin (k + a)) => i ∈ t) (subsetRetrieval_range s hs)
  simpa only [Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range,
    Finset.mem_coe] using (eq_iff_iff.mp h)

/-- Actual subset deletion and survivor reconstruction are equivariant for symmetric tests. -/
theorem subset_survivor_test_covariance
    (σ : Equiv.Perm (Fin (k + a))) (s : Finset (Fin (k + a))) (hs : s.card = a)
    (H : (Fin (k + b) → Z) → K)
    (hH : ∀ (π : Equiv.Perm (Fin (k + b))) (x : Fin (k + b) → Z), H (x ∘ π) = H x)
    (x : Fin (k + a) → Z) (p : Fin b → Z) :
    H (memoryJoin
      (retrievalCoordinates (subsetRetrieval (s.map σ.toEmbedding)
        (by simpa only [Finset.card_map] using hs)) (x ∘ σ.symm)).1 p) =
      H (memoryJoin (retrievalCoordinates (subsetRetrieval s hs) x).1 p) := by
  apply retrieval_survivor_test_covariance σ (subsetRetrieval s hs) _ _ H hH x p
  ext i
  rw [subsetRetrieval_set_range]
  change i ∈ s.map σ.toEmbedding ↔ ∃ j, σ (subsetRetrieval s hs j) = i
  rw [Finset.mem_map]
  constructor
  · rintro ⟨z, hz, hzi⟩
    have hz' : z ∈ Set.range (subsetRetrieval s hs) := by
      rw [subsetRetrieval_set_range]
      exact hz
    obtain ⟨j, hj⟩ := hz'
    exact ⟨j, by rw [hj]; exact hzi⟩
  · rintro ⟨j, hji⟩
    refine ⟨subsetRetrieval s hs j, ?_, hji⟩
    have hj : subsetRetrieval s hs j ∈ Set.range (subsetRetrieval s hs) := ⟨j, rfl⟩
    rw [subsetRetrieval_set_range] at hj
    exact hj

end SimultaneousPrimitiveRoots.Unconditional.Graph

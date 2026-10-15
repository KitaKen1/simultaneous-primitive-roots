module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Rows
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The comparisons: pairs of nonempty sets of probes in the two blocks

Source: `verification/stage7-sources/S-03.tex`, lines 441–454 and 606–620.

"For every pair of nonempty subsets `A ⊆ ℐ₁`, `B ⊆ ℐ₂`, free exactly `A ∪ B`" [S-03:0448–0450].
The statement layer indexes the comparisons by the families `C` with `IsComparison blk m C`;
here they are identified with the pairs `(A, B)` of nonempty sets of coordinates, `A` among the
probes of the first block and `B` among those of the second:

* `sum_comparison_eq` — a signed sum over the comparisons is a double sum over `A` and `B`, with
  `(-1)^{|C|} = (-1)^{|A|} (-1)^{|B|}`;
* `card_comparison_le` — "the number of comparisons is at most `2^P`" [S-03:0619–0620], here
  `2^{m |ℬ|}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

variable {B : Type} [Fintype B] [DecidableEq B] {J ℓ : ℕ}

/-- The big groups of the block `b`. -/
def blockSet (blk : B → Bool) (b : Bool) : Finset B := Finset.univ.filter fun g => blk g = b

omit [DecidableEq B] in
theorem mem_blockSet {blk : B → Bool} {b : Bool} {g : B} : g ∈ blockSet blk b ↔ blk g = b := by
  simp [blockSet]

theorem mem_probeSet_iff {m : ℕ} {G : Finset B} {g : B} {s : Slot J ℓ} :
    (g, s) ∈ probeSet J ℓ m G ↔ g ∈ G ∧ ∃ i, i ∈ probeSlots J m ∧ s = Sum.inl i := by
  unfold probeSet
  rw [mem_slotSet]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hg : g ∈ G
    · rw [if_pos hg] at hi
      exact ⟨hg, i, hi, rfl⟩
    · rw [if_neg hg] at hi
      exact absurd hi (Finset.notMem_empty i)
  · rintro ⟨hg, i, hi, rfl⟩
    refine ⟨i, ?_, rfl⟩
    rw [if_pos hg]
    exact hi

/-- The family of slot sets of a set of coordinates. -/
def famOf (U : Finset (B × Slot J ℓ)) : B → Finset (Fin J) :=
  fun g => Finset.univ.filter fun i => (g, (Sum.inl i : Slot J ℓ)) ∈ U

omit [Fintype B] in
theorem mem_famOf {U : Finset (B × Slot J ℓ)} {g : B} {i : Fin J} :
    i ∈ famOf U g ↔ (g, (Sum.inl i : Slot J ℓ)) ∈ U := by
  simp [famOf]

omit [DecidableEq B] in
theorem card_slotSet_restrict (blk : B → Bool) (C : B → Finset (Fin J)) :
    (slotSet ℓ (restrictBlock blk true C)).card + (slotSet ℓ (restrictBlock blk false C)).card =
      ∑ g, (C g).card := by
  rw [card_slotSet, card_slotSet, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  cases hb : blk g
  · rw [restrictBlock_of_ne C (by simp [hb] : ¬ blk g = true), restrictBlock_of_eq C hb,
      Finset.card_empty, zero_add]
  · rw [restrictBlock_of_eq C hb, restrictBlock_of_ne C (by simp [hb] : ¬ blk g = false),
      Finset.card_empty, add_zero]

theorem slotSet_restrict_mem {blk : B → Bool} {m : ℕ} {b : Bool} {C : B → Finset (Fin J)}
    (hsub : ∀ g, C g ⊆ probeSlots J m) (hne : ∃ g, blk g = b ∧ (C g).Nonempty) :
    slotSet ℓ (restrictBlock blk b C) ∈
      (probeSet J ℓ m (blockSet blk b)).powerset.erase ∅ := by
  rw [Finset.mem_erase, Finset.mem_powerset]
  constructor
  · obtain ⟨g, hg, i, hi⟩ := hne
    intro hempty
    have hmem : (g, (Sum.inl i : Slot J ℓ)) ∈ slotSet ℓ (restrictBlock blk b C) :=
      inl_mem_slotSet.mpr (by
        rw [restrictBlock_of_eq C hg]
        exact hi)
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  · rintro ⟨g, s⟩ hk
    obtain ⟨i, hi, rfl⟩ := mem_slotSet.mp hk
    have hb : blk g = b := by
      by_contra hb
      rw [restrictBlock_of_ne C hb] at hi
      exact Finset.notMem_empty i hi
    rw [restrictBlock_of_eq C hb] at hi
    exact mem_probeSet_iff.mpr ⟨mem_blockSet.mpr hb, i, hsub g hi, rfl⟩

theorem slotSet_restrict_famOf (blk : B → Bool) {m : ℕ} {b : Bool}
    {A Bc : Finset (B × Slot J ℓ)} (hA : A ⊆ probeSet J ℓ m (blockSet blk b))
    (hB : Bc ⊆ probeSet J ℓ m (blockSet blk (!b))) :
    slotSet ℓ (restrictBlock blk b (famOf (A ∪ Bc))) = A := by
  ext ⟨g, s⟩
  constructor
  · intro hk
    obtain ⟨i, hi, rfl⟩ := mem_slotSet.mp hk
    have hb : blk g = b := by
      by_contra hb
      rw [restrictBlock_of_ne _ hb] at hi
      exact Finset.notMem_empty i hi
    rw [restrictBlock_of_eq _ hb, mem_famOf, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hi
    · have hg := (mem_probeSet_iff.mp (hB hi)).1
      rw [mem_blockSet, hb] at hg
      exact absurd hg (by cases b <;> simp)
  · intro hk
    obtain ⟨hg, i, _, rfl⟩ := mem_probeSet_iff.mp (hA hk)
    have hb : blk g = b := mem_blockSet.mp hg
    refine inl_mem_slotSet.mpr ?_
    rw [restrictBlock_of_eq _ hb, mem_famOf]
    exact Finset.mem_union_left _ hk

theorem famOf_slotSet_union (blk : B → Bool) (C : B → Finset (Fin J)) :
    famOf (slotSet ℓ (restrictBlock blk true C) ∪ slotSet ℓ (restrictBlock blk false C)) =
      C := by
  funext g
  ext i
  rw [mem_famOf, ← slotSet_split blk C, inl_mem_slotSet]

theorem isComparison_famOf (blk : B → Bool) {m : ℕ} {A Bc : Finset (B × Slot J ℓ)}
    (hA : A ∈ (probeSet J ℓ m (blockSet blk true)).powerset.erase ∅)
    (hB : Bc ∈ (probeSet J ℓ m (blockSet blk false)).powerset.erase ∅) :
    IsComparison blk m (famOf (A ∪ Bc)) := by
  obtain ⟨hA0, hA1⟩ := Finset.mem_erase.mp hA
  obtain ⟨hB0, hB1⟩ := Finset.mem_erase.mp hB
  rw [Finset.mem_powerset] at hA1 hB1
  refine ⟨fun g i hi => ?_, ?_, ?_⟩
  · rw [mem_famOf, Finset.mem_union] at hi
    rcases hi with hi | hi
    · obtain ⟨_, i', hi', heq⟩ := mem_probeSet_iff.mp (hA1 hi)
      rw [Sum.inl.inj heq]
      exact hi'
    · obtain ⟨_, i', hi', heq⟩ := mem_probeSet_iff.mp (hB1 hi)
      rw [Sum.inl.inj heq]
      exact hi'
  · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hA0
    obtain ⟨g, s⟩ := k
    obtain ⟨hg, i, _, rfl⟩ := mem_probeSet_iff.mp (hA1 hk)
    exact ⟨g, mem_blockSet.mp hg, i, mem_famOf.mpr (Finset.mem_union_left _ hk)⟩
  · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hB0
    obtain ⟨g, s⟩ := k
    obtain ⟨hg, i, _, rfl⟩ := mem_probeSet_iff.mp (hB1 hk)
    exact ⟨g, mem_blockSet.mp hg, i, mem_famOf.mpr (Finset.mem_union_right _ hk)⟩

/-- **The comparisons are the pairs of nonempty sets of probes of the two blocks**
[S-03:0448–0450]: a signed sum over the comparisons, as a double sum. -/
theorem sum_comparison_eq (blk : B → Bool) (m : ℕ)
    (Φ : Finset (B × Slot J ℓ) → Finset (B × Slot J ℓ) → ℂ) :
    ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
          Φ (slotSet ℓ (restrictBlock blk true C.1)) (slotSet ℓ (restrictBlock blk false C.1)) =
      ∑ A ∈ (probeSet J ℓ m (blockSet blk true)).powerset.erase ∅,
        ∑ Bc ∈ (probeSet J ℓ m (blockSet blk false)).powerset.erase ∅,
          (-1 : ℂ) ^ A.card * ((-1 : ℂ) ^ Bc.card * Φ A Bc) := by
  have h1 : ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
          Φ (slotSet ℓ (restrictBlock blk true C.1)) (slotSet ℓ (restrictBlock blk false C.1)) =
      ∑ x ∈ ((probeSet J ℓ m (blockSet blk true)).powerset.erase ∅) ×ˢ
          ((probeSet J ℓ m (blockSet blk false)).powerset.erase ∅),
        (-1 : ℂ) ^ x.1.card * ((-1 : ℂ) ^ x.2.card * Φ x.1 x.2) := by
    refine Finset.sum_bij'
      (fun C _ => (slotSet ℓ (restrictBlock blk true C.1),
        slotSet ℓ (restrictBlock blk false C.1)))
      (fun x hx => ⟨famOf (x.1 ∪ x.2),
        isComparison_famOf blk (Finset.mem_product.mp hx).1 (Finset.mem_product.mp hx).2⟩)
      (fun C _ => Finset.mem_product.mpr
        ⟨slotSet_restrict_mem C.2.1 C.2.2.1, slotSet_restrict_mem C.2.1 C.2.2.2⟩)
      (fun x hx => Finset.mem_univ _)
      (fun C _ => Subtype.ext (famOf_slotSet_union blk C.1))
      (fun x hx => ?_)
      (fun C _ => ?_)
    · obtain ⟨hA, hB⟩ := Finset.mem_product.mp hx
      have hA1 := Finset.mem_powerset.mp (Finset.mem_erase.mp hA).2
      have hB1 := Finset.mem_powerset.mp (Finset.mem_erase.mp hB).2
      refine Prod.ext ?_ ?_
      · show slotSet ℓ (restrictBlock blk true (famOf (x.1 ∪ x.2))) = x.1
        exact slotSet_restrict_famOf blk hA1 hB1
      · show slotSet ℓ (restrictBlock blk false (famOf (x.1 ∪ x.2))) = x.2
        rw [Finset.union_comm]
        exact slotSet_restrict_famOf blk hB1 hA1
    · show (-1 : ℂ) ^ (∑ g, (C.1 g).card) * Φ _ _ =
        (-1 : ℂ) ^ (slotSet ℓ (restrictBlock blk true C.1)).card *
          ((-1 : ℂ) ^ (slotSet ℓ (restrictBlock blk false C.1)).card * Φ _ _)
      rw [← card_slotSet_restrict (ℓ := ℓ) blk C.1, pow_add, mul_assoc]
  exact h1.trans (Finset.sum_product _ _ _)

/-- **The number of comparisons** [S-03:0619–0620]: at most `2^{m |ℬ|}`. -/
theorem card_comparison_le (blk : B → Bool) (m : ℕ) :
    Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} ≤
      2 ^ (m * Fintype.card B) := by
  have h1 : Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} ≤
      (Fintype.piFinset fun _ : B => (probeSlots J m).powerset).card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun C => C.1) ?_ ?_
    · intro C _
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      exact fun g => Finset.mem_powerset.mpr (C.2.1 g)
    · intro C _ C' _ h
      exact Subtype.ext h
  have h2 : (Fintype.piFinset fun _ : B => (probeSlots J m).powerset).card =
      (2 ^ (probeSlots J m).card) ^ Fintype.card B := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Finset.card_powerset]
  have h3 : (2 ^ (probeSlots J m).card) ^ Fintype.card B ≤ 2 ^ (m * Fintype.card B) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left
      (Nat.pow_le_pow_right (by norm_num) (card_probeSlots_le J m)) _
  calc Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C}
      ≤ (Fintype.piFinset fun _ : B => (probeSlots J m).powerset).card := h1
    _ = (2 ^ (probeSlots J m).card) ^ Fintype.card B := h2
    _ ≤ 2 ^ (m * Fintype.card B) := h3

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

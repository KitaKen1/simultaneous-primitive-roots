module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Inserting a new address into a collection of blocks

Source: `verification/stage7-sources/S-02.tex`, lines 1070–1105 (`[S-02:1070–1105]`).

The two combinatorial statements of `History.lean`, (eq:distinct-indicator)
(`DistinctIndicatorExpansion`) and (eq:rank-coefficient-count) (`RankCoefficientCount`), are sums
over the collections `π` of pairwise disjoint blocks of size at least two. Both are proved by
induction on the set of addresses, and the induction step is the same bijection, which is the
subject of this file. It is the paper's "interpret a block of size `h` as a cycle on its `h`
addresses" [S-02:1085–1087] in the form of the insertion of a new point into a permutation written
as a product of cycles: the new point is a fixed point, or it is inserted behind one of the old
points.

* `blockColl s` — the collections of blocks inside a set `s` of addresses
  (`blockColl univ = blockCollections I`, `blockColl_univ`).
* `blockParts s π` — the partition of `s` into the blocks of `π` and the singletons of the
  addresses which are in no block.
* `blockIns a π X` — the collection in which the new address `a` has joined the part `X`: the block
  `X ∪ {a}` replaces the block `X` of `π` (or is a new block of size two if `X` is a singleton).
* `sum_blockColl_insert` — **the insertion step**: for `a ∉ s`,
  `∑_{π ⊆ s ∪ {a}} f(π) = ∑_{π ⊆ s} (f(π) + ∑_{X ∈ parts(π)} f(π with a inserted into X))`.
* `blockMu_blockIns`, `blockRank_blockIns`, `blockConstraint_blockIns`, `sum_blockParts` — the
  effect of the insertion on `μ(π)` (a factor `-|X|`: "there are `(h-1)!` such cycles, each with
  sign `(-1)^{h-1}`"), on `r(π)` (one more), on the constraint `𝒞_π`, and the fact that the parts
  partition `s`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section BlockInsertion

variable {I : Type}

open _root_.Classical in
/-- **The collections of blocks inside `s`**: the sets `π` of pairwise disjoint subsets of `s`,
every one of size at least two. For `s = univ` these are the collections of
(eq:distinct-birth-expansion) (`blockColl_univ`). -/
def blockColl (s : Finset I) : Finset (Finset (Finset I)) :=
  s.powerset.powerset.filter fun π =>
    (∀ b ∈ π, 2 ≤ b.card) ∧ ∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b'

theorem mem_blockColl {s : Finset I} {π : Finset (Finset I)} :
    π ∈ blockColl s ↔ (∀ b ∈ π, b ⊆ s) ∧ (∀ b ∈ π, 2 ≤ b.card) ∧
      ∀ b ∈ π, ∀ b' ∈ π, b ≠ b' → Disjoint b b' := by
  classical
  unfold blockColl
  rw [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun b hb => Finset.mem_powerset.mp (h1 hb), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun b hb => Finset.mem_powerset.mpr (h1 b hb), h2⟩

/-- The collections of blocks inside the set of all addresses are the collections of
(eq:distinct-birth-expansion). -/
theorem blockColl_univ [Fintype I] :
    blockColl (Finset.univ : Finset I) = blockCollections I := by
  ext π
  rw [mem_blockColl, mem_blockCollections]
  exact and_iff_right fun b _ => Finset.subset_univ b

/-- The empty set of addresses carries only the empty collection. -/
theorem blockColl_empty : blockColl (∅ : Finset I) = {∅} := by
  ext π
  rw [mem_blockColl, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2, -⟩
    refine Finset.eq_empty_of_forall_notMem fun b hb => ?_
    have hb0 : b = ∅ := Finset.subset_empty.mp (h1 b hb)
    have h := h2 b hb
    rw [hb0, Finset.card_empty] at h
    omega
  · intro h
    rw [h]
    exact ⟨fun b hb => absurd hb (Finset.notMem_empty b),
      fun b hb => absurd hb (Finset.notMem_empty b),
      fun b hb => absurd hb (Finset.notMem_empty b)⟩

variable [DecidableEq I]

/-- **The partition of `s` belonging to a collection `π`**: the blocks of `π` and the singletons
of the addresses of `s` which are in no block. -/
def blockParts (s : Finset I) (π : Finset (Finset I)) : Finset (Finset I) :=
  π ∪ (s.filter fun i => ¬∃ b ∈ π, i ∈ b).image fun i => ({i} : Finset I)

/-- **The new address `a` joins the part `X`**: the block `X ∪ {a}` replaces `X`. -/
def blockIns (a : I) (π : Finset (Finset I)) (X : Finset I) : Finset (Finset I) :=
  insert (insert a X) (π.erase X)

/-- Remove the address `a` from every block, and drop the blocks which become singletons. -/
def blockRes (a : I) (π : Finset (Finset I)) : Finset (Finset I) :=
  (π.image fun b => b.erase a).filter fun b => 2 ≤ b.card

/-- The block of `π` which contains `a` (the union of all such blocks). -/
def blockAt (a : I) (π : Finset (Finset I)) : Finset I :=
  (π.filter fun b => a ∈ b).biUnion id

theorem mem_blockParts {s : Finset I} {π : Finset (Finset I)} {X : Finset I} :
    X ∈ blockParts s π ↔ X ∈ π ∨ ∃ i, (i ∈ s ∧ ∀ b ∈ π, i ∉ b) ∧ X = {i} := by
  unfold blockParts
  rw [Finset.mem_union, Finset.mem_image]
  refine or_congr_right ?_
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
    exact ⟨i, ⟨hi1, fun b hb hib => hi2 ⟨b, hb, hib⟩⟩, rfl⟩
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨hi1, ?_⟩, rfl⟩
    rintro ⟨b, hb, hib⟩
    exact hi2 b hb hib

theorem blockParts_subset {s : Finset I} {π : Finset (Finset I)} (hπ : π ∈ blockColl s)
    {X : Finset I} (hX : X ∈ blockParts s π) : X ⊆ s := by
  rcases mem_blockParts.mp hX with h | ⟨i, hi, rfl⟩
  · exact (mem_blockColl.mp hπ).1 X h
  · exact Finset.singleton_subset_iff.mpr hi.1

theorem blockParts_card_pos {s : Finset I} {π : Finset (Finset I)} (hπ : π ∈ blockColl s)
    {X : Finset I} (hX : X ∈ blockParts s π) : 0 < X.card := by
  rcases mem_blockParts.mp hX with h | ⟨i, -, rfl⟩
  · have h2 := (mem_blockColl.mp hπ).2.1 X h
    omega
  · rw [Finset.card_singleton]
    exact Nat.zero_lt_one

theorem blockParts_disjoint {s : Finset I} {π : Finset (Finset I)} (hπ : π ∈ blockColl s)
    {X : Finset I} (hX : X ∈ blockParts s π) {b : Finset I} (hb : b ∈ π) (hne : b ≠ X) :
    Disjoint b X := by
  rcases mem_blockParts.mp hX with h | ⟨i, hi, rfl⟩
  · exact (mem_blockColl.mp hπ).2.2 b hb X h hne
  · exact Finset.disjoint_singleton_right.mpr (hi.2 b hb)

theorem blockParts_mem_of_two_le {s : Finset I} {π : Finset (Finset I)} {X : Finset I}
    (hX : X ∈ blockParts s π) (h2 : 2 ≤ X.card) : X ∈ π := by
  rcases mem_blockParts.mp hX with h | ⟨i, -, rfl⟩
  · exact h
  · rw [Finset.card_singleton] at h2
    exact absurd h2 (by omega)

/-- **The parts partition `s`**: a sum over the addresses of `s` is the sum over the parts of the
sums over each part. -/
theorem sum_blockParts {M : Type*} [AddCommMonoid M] {s : Finset I} {π : Finset (Finset I)}
    (hπ : π ∈ blockColl s) (g : I → M) :
    ∑ X ∈ blockParts s π, ∑ i ∈ X, g i = ∑ i ∈ s, g i := by
  obtain ⟨h1, -, h3⟩ := mem_blockColl.mp hπ
  have hdisj : Disjoint π
      ((s.filter fun i => ¬∃ b ∈ π, i ∈ b).image fun i => ({i} : Finset I)) := by
    rw [Finset.disjoint_left]
    intro X hXπ hXim
    obtain ⟨i, hi, hiX⟩ := Finset.mem_image.mp hXim
    refine (Finset.mem_filter.mp hi).2 ⟨X, hXπ, ?_⟩
    rw [← hiX]
    exact Finset.mem_singleton_self i
  have hinj : Set.InjOn (fun i => ({i} : Finset I))
      ((s.filter fun i => ¬∃ b ∈ π, i ∈ b : Finset I) : Set I) := by
    intro i _ j _ hij
    exact Finset.singleton_injective hij
  have hblocks : ∑ X ∈ π, ∑ i ∈ X, g i =
      ∑ i ∈ s.filter (fun i => ∃ b ∈ π, i ∈ b), g i := by
    have hcover : (s.filter fun i => ∃ b ∈ π, i ∈ b) = π.biUnion id := by
      ext i
      rw [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨-, b, hb, hi⟩
        exact ⟨b, hb, hi⟩
      · rintro ⟨b, hb, hi⟩
        exact ⟨h1 b hb hi, b, hb, hi⟩
    rw [hcover]
    exact (Finset.sum_biUnion fun b hb b' hb' hne => h3 b hb b' hb' hne).symm
  have hfree : ∑ X ∈ (s.filter fun i => ¬∃ b ∈ π, i ∈ b).image (fun i => ({i} : Finset I)),
      ∑ i ∈ X, g i = ∑ i ∈ s.filter (fun i => ¬∃ b ∈ π, i ∈ b), g i :=
    (Finset.sum_image hinj).trans (Finset.sum_congr rfl fun i _ => Finset.sum_singleton g i)
  unfold blockParts
  rw [Finset.sum_union hdisj, hblocks, hfree]
  exact Finset.sum_filter_add_sum_filter_not s (fun i => ∃ b ∈ π, i ∈ b) g

/-! ### The insertion is a bijection -/

/-- The collections inside `s ∪ {a}` in which no block contains `a` are the collections inside
`s`. -/
theorem blockColl_insert_filter_not {a : I} {s : Finset I} (ha : a ∉ s) :
    ((blockColl (insert a s)).filter fun π => ¬∃ b ∈ π, a ∈ b) = blockColl s := by
  ext π
  rw [Finset.mem_filter, mem_blockColl, mem_blockColl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun b hb => ?_, h2⟩
    have hab : a ∉ b := fun hab => h3 ⟨b, hb, hab⟩
    exact (Finset.subset_insert_iff_of_notMem hab).mp (h1 b hb)
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun b hb => Finset.Subset.trans (h1 b hb) (Finset.subset_insert a s), h2⟩, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact ha (h1 b hb hab)

/-- The collection with `a` inserted into the part `X` is a collection inside `s ∪ {a}`. -/
theorem blockIns_mem {a : I} {s : Finset I} (ha : a ∉ s) {π : Finset (Finset I)}
    (hπ : π ∈ blockColl s) {X : Finset I} (hX : X ∈ blockParts s π) :
    blockIns a π X ∈ blockColl (insert a s) := by
  obtain ⟨h1, h2, h3⟩ := mem_blockColl.mp hπ
  have hXs : X ⊆ s := blockParts_subset hπ hX
  have haX : a ∉ X := fun h => ha (hXs h)
  have hXpos : 0 < X.card := blockParts_card_pos hπ hX
  rw [mem_blockColl]
  unfold blockIns
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun b hb b' hb' hne => ?_⟩
  · rcases Finset.mem_insert.mp hb with hbX | hb1
    · rw [hbX]
      exact Finset.insert_subset_insert a hXs
    · exact Finset.Subset.trans (h1 b (Finset.mem_of_mem_erase hb1)) (Finset.subset_insert a s)
  · rcases Finset.mem_insert.mp hb with hbX | hb1
    · rw [hbX, Finset.card_insert_of_notMem haX]
      omega
    · exact h2 b (Finset.mem_of_mem_erase hb1)
  · rcases Finset.mem_insert.mp hb with hbX | hb1
    · rcases Finset.mem_insert.mp hb' with hbX' | hb1'
      · exact absurd (hbX.trans hbX'.symm) hne
      · have hb'π := Finset.mem_of_mem_erase hb1'
        rw [hbX]
        refine Finset.disjoint_insert_left.mpr ⟨fun h => ha (h1 b' hb'π h), ?_⟩
        exact (blockParts_disjoint hπ hX hb'π (Finset.ne_of_mem_erase hb1')).symm
    · have hbπ := Finset.mem_of_mem_erase hb1
      rcases Finset.mem_insert.mp hb' with hbX' | hb1'
      · rw [hbX']
        refine Finset.disjoint_insert_right.mpr ⟨fun h => ha (h1 b hbπ h), ?_⟩
        exact blockParts_disjoint hπ hX hbπ (Finset.ne_of_mem_erase hb1)
      · exact h3 b hbπ b' (Finset.mem_of_mem_erase hb1') hne

/-- The block of a collection which contains `a`. -/
theorem blockAt_eq {a : I} {s : Finset I} {π : Finset (Finset I)} (hπ : π ∈ blockColl s)
    {b₀ : Finset I} (hb₀ : b₀ ∈ π) (hab₀ : a ∈ b₀) : blockAt a π = b₀ := by
  obtain ⟨-, -, h3⟩ := mem_blockColl.mp hπ
  ext i
  unfold blockAt
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hi⟩
    obtain ⟨hc1, hac⟩ := Finset.mem_filter.mp hc
    have hcb : c = b₀ := by
      by_contra hne
      exact Finset.disjoint_left.mp (h3 c hc1 b₀ hb₀ hne) hac hab₀
    rw [← hcb]
    exact hi
  · intro hi
    exact ⟨b₀, Finset.mem_filter.mpr ⟨hb₀, hab₀⟩, hi⟩

/-- Removing `a` from a collection inside `s ∪ {a}` gives a collection inside `s`. -/
theorem blockRes_mem {a : I} {s : Finset I} {π : Finset (Finset I)}
    (hπ : π ∈ blockColl (insert a s)) : blockRes a π ∈ blockColl s := by
  obtain ⟨h1, -, h3⟩ := mem_blockColl.mp hπ
  rw [mem_blockColl]
  unfold blockRes
  refine ⟨fun c hc => ?_, fun c hc => (Finset.mem_filter.mp hc).2, fun c hc c' hc' hne => ?_⟩
  · obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    rw [← hbc]
    exact Finset.subset_insert_iff.mp (h1 b hb)
  · obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    obtain ⟨b', hb', hbc'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc').1
    have hbb : b ≠ b' := by
      intro h
      apply hne
      rw [← hbc, ← hbc', h]
    rw [← hbc, ← hbc']
    exact Finset.disjoint_of_subset_left (Finset.erase_subset a b)
      (Finset.disjoint_of_subset_right (Finset.erase_subset a b') (h3 b hb b' hb' hbb))

/-- Removing `a` after its insertion gives the collection back. -/
theorem blockRes_blockIns {a : I} {s : Finset I} (ha : a ∉ s) {π : Finset (Finset I)}
    (hπ : π ∈ blockColl s) {X : Finset I} (hX : X ∈ blockParts s π) :
    blockRes a (blockIns a π X) = π := by
  obtain ⟨h1, h2, -⟩ := mem_blockColl.mp hπ
  have haX : a ∉ X := fun h => ha (blockParts_subset hπ hX h)
  have hnot : ∀ b ∈ π, a ∉ b := fun b hb h => ha (h1 b hb h)
  ext c
  unfold blockRes blockIns
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨b, hb, hbc⟩, hc2⟩
    rw [← hbc] at hc2 ⊢
    rcases Finset.mem_insert.mp hb with hbX | hb1
    · rw [hbX, Finset.erase_insert haX] at hc2 ⊢
      exact blockParts_mem_of_two_le hX hc2
    · have hbπ := Finset.mem_of_mem_erase hb1
      rw [Finset.erase_eq_of_notMem (hnot b hbπ)]
      exact hbπ
  · intro hc
    refine ⟨?_, h2 c hc⟩
    by_cases hcX : c = X
    · refine ⟨insert a X, Finset.mem_insert_self _ _, ?_⟩
      rw [Finset.erase_insert haX, hcX]
    · refine ⟨c, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcX, hc⟩), ?_⟩
      exact Finset.erase_eq_of_notMem (hnot c hc)

/-- A collection inside `s ∪ {a}` with a block `b₀ ∋ a` is the insertion of `a` into the part
`b₀ ∖ {a}` of the collection with `a` removed. -/
theorem blockIns_blockRes {a : I} {s : Finset I} {π : Finset (Finset I)}
    (hπ : π ∈ blockColl (insert a s)) {b₀ : Finset I} (hb₀ : b₀ ∈ π) (hab₀ : a ∈ b₀) :
    b₀.erase a ∈ blockParts s (blockRes a π) ∧
      blockIns a (blockRes a π) (b₀.erase a) = π := by
  obtain ⟨h1, h2, h3⟩ := mem_blockColl.mp hπ
  have huniq : ∀ b ∈ π, b ≠ b₀ → a ∉ b := fun b hb hne hab =>
    Finset.disjoint_left.mp (h3 b hb b₀ hb₀ hne) hab hab₀
  have hcard : (b₀.erase a).card = b₀.card - 1 := Finset.card_erase_of_mem hab₀
  have hb₀2 := h2 b₀ hb₀
  have hres : ∀ c, c ∈ blockRes a π ↔ (∃ b ∈ π, b.erase a = c) ∧ 2 ≤ c.card := by
    intro c
    unfold blockRes
    rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rw [mem_blockParts]
    by_cases h2' : 2 ≤ (b₀.erase a).card
    · exact Or.inl ((hres _).mpr ⟨⟨b₀, hb₀, rfl⟩, h2'⟩)
    · right
      have h1' : (b₀.erase a).card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1'
      have hib₀ : i ∈ b₀.erase a := by
        rw [hi]
        exact Finset.mem_singleton_self i
      refine ⟨i, ⟨Finset.subset_insert_iff.mp (h1 b₀ hb₀) hib₀, ?_⟩, hi⟩
      intro c hc hic
      obtain ⟨⟨b, hb, hbc⟩, hc2⟩ := (hres c).mp hc
      rw [← hbc] at hic hc2
      have hbb : b = b₀ := by
        by_contra hne
        exact Finset.disjoint_left.mp (h3 b hb b₀ hb₀ hne) (Finset.mem_of_mem_erase hic)
          (Finset.mem_of_mem_erase hib₀)
      rw [hbb] at hc2
      exact h2' hc2
  · ext c
    unfold blockIns
    rw [Finset.mem_insert, Finset.mem_erase, hres, Finset.insert_erase hab₀]
    constructor
    · rintro (hcb | ⟨hcX, ⟨b, hb, hbc⟩, -⟩)
      · rw [hcb]
        exact hb₀
      · have hbb : b ≠ b₀ := by
          intro h
          apply hcX
          rw [← hbc, h]
        rw [← hbc, Finset.erase_eq_of_notMem (huniq b hb hbb)]
        exact hb
    · intro hc
      by_cases hcb : c = b₀
      · exact Or.inl hcb
      · right
        have hac : a ∉ c := huniq c hc hcb
        refine ⟨?_, ⟨c, hc, Finset.erase_eq_of_notMem hac⟩, h2 c hc⟩
        intro hcX
        have hc2 := h2 c hc
        have hcpos : 0 < c.card := by omega
        obtain ⟨j, hj⟩ := Finset.card_pos.mp hcpos
        have hjb₀ : j ∈ b₀ := by
          have hj' : j ∈ b₀.erase a := by
            rw [← hcX]
            exact hj
          exact Finset.mem_of_mem_erase hj'
        exact Finset.disjoint_left.mp (h3 c hc b₀ hb₀ hcb) hj hjb₀

/-- **The insertion step.** For a new address `a ∉ s`, a collection of blocks inside `s ∪ {a}`
either does not use `a`, and is a collection inside `s`; or it is obtained from a unique
collection `π` inside `s` and a unique part `X` of the partition of `s` belonging to `π`, by
letting `a` join `X`. -/
theorem sum_blockColl_insert {M : Type*} [AddCommMonoid M] {a : I} {s : Finset I} (ha : a ∉ s)
    (f : Finset (Finset I) → M) :
    ∑ π ∈ blockColl (insert a s), f π =
      ∑ π ∈ blockColl s, (f π + ∑ X ∈ blockParts s π, f (blockIns a π X)) := by
  have hsplit : ∑ π ∈ (blockColl (insert a s)).filter (fun π => ¬∃ b ∈ π, a ∈ b), f π +
      ∑ π ∈ (blockColl (insert a s)).filter (fun π => ∃ b ∈ π, a ∈ b), f π =
      ∑ π ∈ blockColl (insert a s), f π :=
    Finset.sum_filter_not_add_sum_filter (blockColl (insert a s)) (fun π => ∃ b ∈ π, a ∈ b) f
  rw [blockColl_insert_filter_not ha] at hsplit
  have hbij : ∑ p ∈ (blockColl s).sigma (blockParts s), f (blockIns a p.1 p.2) =
      ∑ π ∈ (blockColl (insert a s)).filter (fun π => ∃ b ∈ π, a ∈ b), f π := by
    refine Finset.sum_nbij'
      (fun p : (Σ _ : Finset (Finset I), Finset I) => blockIns a p.1 p.2)
      (fun π : Finset (Finset I) =>
        (⟨blockRes a π, (blockAt a π).erase a⟩ : Σ _ : Finset (Finset I), Finset I))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨π, X⟩ hp
      have hp1 : π ∈ blockColl s := (Finset.mem_sigma.mp hp).1
      have hp2 : X ∈ blockParts s π := (Finset.mem_sigma.mp hp).2
      have hmem : insert a X ∈ blockIns a π X := by
        unfold blockIns
        exact Finset.mem_insert_self _ _
      exact Finset.mem_filter.mpr
        ⟨blockIns_mem ha hp1 hp2, insert a X, hmem, Finset.mem_insert_self a X⟩
    · intro π hπ
      obtain ⟨hπ1, b₀, hb₀, hab₀⟩ := Finset.mem_filter.mp hπ
      refine Finset.mem_sigma.mpr ⟨blockRes_mem hπ1, ?_⟩
      show (blockAt a π).erase a ∈ blockParts s (blockRes a π)
      rw [blockAt_eq hπ1 hb₀ hab₀]
      exact (blockIns_blockRes hπ1 hb₀ hab₀).1
    · rintro ⟨π, X⟩ hp
      have hp1 : π ∈ blockColl s := (Finset.mem_sigma.mp hp).1
      have hp2 : X ∈ blockParts s π := (Finset.mem_sigma.mp hp).2
      have haX : a ∉ X := fun h => ha (blockParts_subset hp1 hp2 h)
      have hmem : insert a X ∈ blockIns a π X := by
        unfold blockIns
        exact Finset.mem_insert_self _ _
      have e1 : blockRes a (blockIns a π X) = π := blockRes_blockIns ha hp1 hp2
      have e2 : (blockAt a (blockIns a π X)).erase a = X := by
        rw [blockAt_eq (blockIns_mem ha hp1 hp2) hmem (Finset.mem_insert_self a X),
          Finset.erase_insert haX]
      show (⟨blockRes a (blockIns a π X), (blockAt a (blockIns a π X)).erase a⟩ :
        Σ _ : Finset (Finset I), Finset I) = ⟨π, X⟩
      rw [e1, e2]
    · intro π hπ
      obtain ⟨hπ1, b₀, hb₀, hab₀⟩ := Finset.mem_filter.mp hπ
      show blockIns a (blockRes a π) ((blockAt a π).erase a) = π
      rw [blockAt_eq hπ1 hb₀ hab₀]
      exact (blockIns_blockRes hπ1 hb₀ hab₀).2
    · intro p _
      rfl
  calc ∑ π ∈ blockColl (insert a s), f π
      = ∑ π ∈ blockColl s, f π +
          ∑ π ∈ (blockColl (insert a s)).filter (fun π => ∃ b ∈ π, a ∈ b), f π := hsplit.symm
    _ = ∑ π ∈ blockColl s, f π +
          ∑ p ∈ (blockColl s).sigma (blockParts s), f (blockIns a p.1 p.2) := by rw [hbij]
    _ = ∑ π ∈ blockColl s, f π +
          ∑ π ∈ blockColl s, ∑ X ∈ blockParts s π, f (blockIns a π X) :=
        congrArg (fun t => ∑ π ∈ blockColl s, f π + t)
          (Finset.sum_sigma (blockColl s) (blockParts s) fun p => f (blockIns a p.1 p.2))
    _ = ∑ π ∈ blockColl s, (f π + ∑ X ∈ blockParts s π, f (blockIns a π X)) :=
        Finset.sum_add_distrib.symm

/-! ### The effect of the insertion on `μ`, on the rank and on the constraint -/

/-- `μ` of the collection with `a` inserted into the part `X`: the factor
`(-1)^{|X|-1} (|X|-1)!` of `X` becomes `(-1)^{|X|} |X|!`. -/
theorem blockMu_blockIns {a : I} {s : Finset I} (ha : a ∉ s) {π : Finset (Finset I)}
    (hπ : π ∈ blockColl s) {X : Finset I} (hX : X ∈ blockParts s π) :
    blockMu (blockIns a π X) = -(X.card : ℤ) * blockMu π := by
  obtain ⟨h1, -, -⟩ := mem_blockColl.mp hπ
  have haX : a ∉ X := fun h => ha (blockParts_subset hπ hX h)
  have hXpos : 0 < X.card := blockParts_card_pos hπ hX
  have hnotin : insert a X ∉ π.erase X := fun h =>
    ha (h1 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a X))
  have hfac : (-1 : ℤ) ^ ((insert a X).card - 1) * (((insert a X).card - 1).factorial : ℤ) =
      -(X.card : ℤ) * ((-1) ^ (X.card - 1) * ((X.card - 1).factorial : ℤ)) := by
    obtain ⟨k, hk⟩ : ∃ k, X.card = k + 1 := ⟨X.card - 1, by omega⟩
    rw [Finset.card_insert_of_notMem haX, hk]
    have e1 : k + 1 + 1 - 1 = k + 1 := by omega
    have e2 : k + 1 - 1 = k := by omega
    rw [e1, e2, Nat.factorial_succ, pow_succ]
    push_cast
    ring
  have hrest : ((-1 : ℤ) ^ (X.card - 1) * ((X.card - 1).factorial : ℤ)) *
      ∏ b ∈ π.erase X, ((-1 : ℤ) ^ (b.card - 1) * ((b.card - 1).factorial : ℤ)) =
      blockMu π := by
    unfold blockMu
    rcases mem_blockParts.mp hX with h | ⟨i, hi, hXi⟩
    · exact Finset.mul_prod_erase π
        (fun b => (-1 : ℤ) ^ (b.card - 1) * ((b.card - 1).factorial : ℤ)) h
    · have hnot : X ∉ π := by
        intro h
        refine hi.2 X h ?_
        rw [hXi]
        exact Finset.mem_singleton_self i
      have hc1 : X.card = 1 := by
        rw [hXi]
        exact Finset.card_singleton i
      rw [Finset.erase_eq_of_notMem hnot, hc1]
      simp
  have hL : blockMu (blockIns a π X) =
      ((-1 : ℤ) ^ ((insert a X).card - 1) * (((insert a X).card - 1).factorial : ℤ)) *
        ∏ b ∈ π.erase X, ((-1 : ℤ) ^ (b.card - 1) * ((b.card - 1).factorial : ℤ)) := by
    unfold blockMu blockIns
    exact Finset.prod_insert hnotin
  rw [hL, hfac, mul_assoc, hrest]

/-- The rank of the collection with `a` inserted into a part is one more. -/
theorem blockRank_blockIns {a : I} {s : Finset I} (ha : a ∉ s) {π : Finset (Finset I)}
    (hπ : π ∈ blockColl s) {X : Finset I} (hX : X ∈ blockParts s π) :
    blockRank (blockIns a π X) = blockRank π + 1 := by
  obtain ⟨h1, -, -⟩ := mem_blockColl.mp hπ
  have haX : a ∉ X := fun h => ha (blockParts_subset hπ hX h)
  have hXpos : 0 < X.card := blockParts_card_pos hπ hX
  have hnotin : insert a X ∉ π.erase X := fun h =>
    ha (h1 _ (Finset.mem_of_mem_erase h) (Finset.mem_insert_self a X))
  have hL : blockRank (blockIns a π X) =
      ((insert a X).card - 1) + ∑ b ∈ π.erase X, (b.card - 1) := by
    unfold blockRank blockIns
    exact Finset.sum_insert hnotin
  have hrest : (X.card - 1) + ∑ b ∈ π.erase X, (b.card - 1) = blockRank π := by
    unfold blockRank
    rcases mem_blockParts.mp hX with h | ⟨i, hi, hXi⟩
    · exact Finset.add_sum_erase π (fun b => b.card - 1) h
    · have hnot : X ∉ π := by
        intro h
        refine hi.2 X h ?_
        rw [hXi]
        exact Finset.mem_singleton_self i
      have hc1 : X.card = 1 := by
        rw [hXi]
        exact Finset.card_singleton i
      rw [Finset.erase_eq_of_notMem hnot, hc1]
      simp
  have hc : (insert a X).card = X.card + 1 := Finset.card_insert_of_notMem haX
  rw [hL, hc, ← hrest]
  omega

/-- The constraint `𝒞` of the collection with `a` inserted into `X`: the constraint of `π`, and
`a` is performed with the same value as all addresses of `X`. -/
theorem blockConstraint_blockIns {Z : Type} (birth : I → Option Z) (a : I)
    (π : Finset (Finset I)) (X : Finset I) :
    BlockConstraint birth (blockIns a π X) ↔
      BlockConstraint birth π ∧ ∃ z, birth a = some z ∧ ∀ i ∈ X, birth i = some z := by
  unfold BlockConstraint blockIns
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h (insert a X) (Finset.mem_insert_self _ _)
    refine ⟨fun b hb => ?_, z, hz a (Finset.mem_insert_self a X),
      fun i hi => hz i (Finset.mem_insert_of_mem hi)⟩
    by_cases hbX : b = X
    · refine ⟨z, fun i hi => hz i (Finset.mem_insert_of_mem ?_)⟩
      rw [← hbX]
      exact hi
    · exact h b (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbX, hb⟩))
  · rintro ⟨h, z, hza, hzX⟩ b hb
    rcases Finset.mem_insert.mp hb with hbX | hb1
    · refine ⟨z, fun i hi => ?_⟩
      rw [hbX] at hi
      rcases Finset.mem_insert.mp hi with hia | hi1
      · rw [hia]
        exact hza
      · exact hzX i hi1
    · exact h b (Finset.mem_of_mem_erase hb1)

end BlockInsertion

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

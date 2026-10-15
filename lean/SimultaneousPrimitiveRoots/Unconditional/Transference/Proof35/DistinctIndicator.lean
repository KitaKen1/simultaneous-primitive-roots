module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BlockInsertion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (eq:distinct-indicator): the indicator of distinct births as a sum over collections of blocks

Source: `verification/stage7-sources/S-02.tex`, lines 1070–1093 (`[S-02:1070–1093]`).

`distinctIndicatorExpansion : DistinctIndicatorExpansion` is proved here: for an assignment
`birth : I → Option ℕ` on a finite set of addresses,
`∑_π μ(π) 1_{𝒞_π} = 1_{distinct performed birth values}`,
the sum being over the collections `π` of pairwise disjoint blocks of size at least two,
`μ(π) = ∏_{B' ∈ π} (-1)^{|B'|-1} (|B'|-1)!`.

The paper's argument: "interpret a block of size `h` as a cycle on its `h` addresses: there are
`(h-1)!` such cycles, each with sign `(-1)^{h-1}`. The right side is the sum of signs of
permutations of the performed addresses which preserve their numerical prime values. … The sign sum
is one for a singleton class and zero for any class of size at least two."

The proof here is the same computation, organised as an induction on the set `s` of addresses,
with the sum restricted to the collections inside `s` (`blockColl s`): by the insertion step
`sum_blockColl_insert` of `BlockInsertion.lean` (a new address `a` is a fixed point, or it is
inserted into the cycle of one of the old addresses, which multiplies `μ` by `-1` for every old
address of that cycle),

`F(s ∪ {a}) = (1 - #{i ∈ s : i is performed with the value of a}) · F(s)`

(`sum_blockColl_birth_insert`). If the births of `s` are distinct, at most one address of `s` has
the value of `a`, and the factor is `1` or `0` according as there is none or one
(`sum_blockColl_birth`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section DistinctIndicator

variable {I : Type}

/-- The performed births at the addresses of `s` have pairwise distinct values. -/
def BirthsDistinctOn (birth : I → Option ℕ) (s : Finset I) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, ∀ z, birth i = some z → birth j = some z → i = j

/-- The addresses `a` and `i` are both performed, with the same value. -/
def BirthCollides (birth : I → Option ℕ) (a i : I) : Prop :=
  ∃ z, birth a = some z ∧ birth i = some z

variable [DecidableEq I]

open _root_.Classical in
/-- The insertion step for one collection `π` inside `s`: the terms of `π` and of the collections
obtained from `π` by letting the new address `a` join a part add up to
`(1 - #{i ∈ s : i collides with a})` times the term of `π`. -/
theorem blockMu_step (birth : I → Option ℕ) {a : I} {s : Finset I} (ha : a ∉ s)
    {π : Finset (Finset I)} (hπ : π ∈ blockColl s) :
    blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0) +
        ∑ X ∈ blockParts s π, blockMu (blockIns a π X) *
          (if BlockConstraint birth (blockIns a π X) then (1 : ℤ) else 0) =
      (1 - ∑ i ∈ s, (if BirthCollides birth a i then (1 : ℤ) else 0)) *
        (blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0)) := by
  by_cases hC : BlockConstraint birth π
  · have hX : ∀ X ∈ blockParts s π,
        blockMu (blockIns a π X) *
            (if BlockConstraint birth (blockIns a π X) then (1 : ℤ) else 0) =
          -blockMu π * ∑ i ∈ X, (if BirthCollides birth a i then (1 : ℤ) else 0) := by
      intro X hX
      -- the births are constant on the part `X`
      obtain ⟨w, hw⟩ : ∃ w : Option ℕ, ∀ i ∈ X, birth i = w := by
        rcases mem_blockParts.mp hX with h | ⟨i, -, hXi⟩
        · obtain ⟨z, hz⟩ := hC X h
          exact ⟨some z, hz⟩
        · refine ⟨birth i, fun j hj => ?_⟩
          rw [hXi] at hj
          rw [Finset.mem_singleton.mp hj]
      rw [blockMu_blockIns ha hπ hX]
      by_cases hQ : ∃ z, birth a = some z ∧ w = some z
      · obtain ⟨z, hza, hwz⟩ := hQ
        have h1 : BlockConstraint birth (blockIns a π X) :=
          (blockConstraint_blockIns birth a π X).mpr
            ⟨hC, z, hza, fun i hi => (hw i hi).trans hwz⟩
        have h2 : ∀ i ∈ X, (if BirthCollides birth a i then (1 : ℤ) else 0) = 1 := by
          intro i hi
          have h : BirthCollides birth a i := ⟨z, hza, (hw i hi).trans hwz⟩
          exact if_pos h
        rw [if_pos h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
        ring
      · have h1 : ¬BlockConstraint birth (blockIns a π X) := by
          intro h
          obtain ⟨-, z, hza, hzX⟩ := (blockConstraint_blockIns birth a π X).mp h
          obtain ⟨j, hj⟩ := Finset.card_pos.mp (blockParts_card_pos hπ hX)
          exact hQ ⟨z, hza, (hw j hj).symm.trans (hzX j hj)⟩
        have h2 : ∀ i ∈ X, (if BirthCollides birth a i then (1 : ℤ) else 0) = 0 := by
          intro i hi
          refine if_neg ?_
          rintro ⟨z, hza, hiz⟩
          exact hQ ⟨z, hza, (hw i hi).symm.trans hiz⟩
        rw [if_neg h1, Finset.sum_congr rfl h2, Finset.sum_const_zero]
        ring
    rw [if_pos hC, Finset.sum_congr rfl hX, ← Finset.mul_sum, sum_blockParts hπ]
    ring
  · have hX : ∀ X ∈ blockParts s π,
        blockMu (blockIns a π X) *
            (if BlockConstraint birth (blockIns a π X) then (1 : ℤ) else 0) = 0 := by
      intro X _
      have h1 : ¬BlockConstraint birth (blockIns a π X) := fun h =>
        hC ((blockConstraint_blockIns birth a π X).mp h).1
      rw [if_neg h1, mul_zero]
    rw [if_neg hC, Finset.sum_congr rfl hX, Finset.sum_const_zero]
    ring

open _root_.Classical in
/-- **The recursion of the signed sum**: a new address `a` multiplies the sum over the collections
inside `s` by `1 - #{i ∈ s : i is performed with the value of a}`. -/
theorem sum_blockColl_birth_insert (birth : I → Option ℕ) {a : I} {s : Finset I} (ha : a ∉ s) :
    ∑ π ∈ blockColl (insert a s),
        blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0) =
      (1 - ∑ i ∈ s, (if BirthCollides birth a i then (1 : ℤ) else 0)) *
        ∑ π ∈ blockColl s, blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0) := by
  rw [sum_blockColl_insert ha, Finset.mul_sum]
  exact Finset.sum_congr rfl fun π hπ => blockMu_step birth ha hπ

open _root_.Classical in
/-- **(eq:distinct-indicator) for the addresses of a set `s`**: the signed sum over the
collections of blocks inside `s` is the indicator that the performed births of `s` are distinct. -/
theorem sum_blockColl_birth (birth : I → Option ℕ) (s : Finset I) :
    ∑ π ∈ blockColl s, blockMu π * (if BlockConstraint birth π then (1 : ℤ) else 0) =
      if BirthsDistinctOn birth s then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : BlockConstraint birth (∅ : Finset (Finset I)) :=
      fun b hb => absurd hb (Finset.notMem_empty b)
    have h1 : BirthsDistinctOn birth (∅ : Finset I) :=
      fun i hi => absurd hi (Finset.notMem_empty i)
    have hmu : blockMu (∅ : Finset (Finset I)) = 1 := by
      unfold blockMu
      exact Finset.prod_empty
    rw [blockColl_empty, Finset.sum_singleton, if_pos h0, if_pos h1, hmu, mul_one]
  | insert a s ha ih =>
    rw [sum_blockColl_birth_insert birth ha, ih]
    by_cases hD : BirthsDistinctOn birth s
    · rw [if_pos hD, mul_one]
      by_cases hD' : BirthsDistinctOn birth (insert a s)
      · -- no address of `s` has the value of `a`
        have h0 : ∀ i ∈ s, (if BirthCollides birth a i then (1 : ℤ) else 0) = 0 := by
          intro i hi
          refine if_neg ?_
          rintro ⟨z, hza, hiz⟩
          have hia : i = a :=
            hD' i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) z hiz hza
          apply ha
          rw [← hia]
          exact hi
        rw [if_pos hD', Finset.sum_congr rfl h0, Finset.sum_const_zero, sub_zero]
      · -- exactly one address of `s` has the value of `a`
        have hex : ∃ j ∈ s, BirthCollides birth a j := by
          by_contra hne
          apply hD'
          intro i hi j hj z hiz hjz
          rcases Finset.mem_insert.mp hi with hia | hi'
          · rcases Finset.mem_insert.mp hj with hja | hj'
            · rw [hia, hja]
            · rw [hia] at hiz
              exact (hne ⟨j, hj', z, hiz, hjz⟩).elim
          · rcases Finset.mem_insert.mp hj with hja | hj'
            · rw [hja] at hjz
              exact (hne ⟨i, hi', z, hjz, hiz⟩).elim
            · exact hD i hi' j hj' z hiz hjz
        obtain ⟨j, hj, z, hza, hjz⟩ := hex
        have hgj : (if BirthCollides birth a j then (1 : ℤ) else 0) = 1 := by
          have h : BirthCollides birth a j := ⟨z, hza, hjz⟩
          exact if_pos h
        have hrest : ∀ i ∈ s.erase j,
            (if BirthCollides birth a i then (1 : ℤ) else 0) = 0 := by
          intro i hi
          refine if_neg ?_
          rintro ⟨z', hza', hiz'⟩
          have hzz : z' = z := Option.some.inj (hza'.symm.trans hza)
          rw [hzz] at hiz'
          exact Finset.ne_of_mem_erase hi
            (hD i (Finset.mem_of_mem_erase hi) j hj z hiz' hjz)
        have hsum : ∑ i ∈ s, (if BirthCollides birth a i then (1 : ℤ) else 0) = 1 := by
          have e2 : ∑ i ∈ s.erase j, (if BirthCollides birth a i then (1 : ℤ) else 0) = 0 :=
            (Finset.sum_congr rfl hrest).trans Finset.sum_const_zero
          have e3 : (if BirthCollides birth a j then (1 : ℤ) else 0) +
              ∑ i ∈ s.erase j, (if BirthCollides birth a i then (1 : ℤ) else 0) =
              ∑ i ∈ s, (if BirthCollides birth a i then (1 : ℤ) else 0) :=
            Finset.add_sum_erase s (fun i => if BirthCollides birth a i then (1 : ℤ) else 0) hj
          rw [← e3, hgj, e2, add_zero]
        rw [if_neg hD', hsum, sub_self]
    · have hD' : ¬BirthsDistinctOn birth (insert a s) := fun h =>
        hD fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
      rw [if_neg hD, if_neg hD', mul_zero]

end DistinctIndicator

open _root_.Classical in
/-- **(eq:distinct-indicator)** [S-02:1080–1093]: "for a fixed realized path,
`1_{distinct performed birth values} = ∑_π μ(π) 1_{𝒞_π}`": for every assignment
`birth : I → Option ℕ` on a finite set `I` of addresses, the signed sum over the collections of
pairwise disjoint blocks of size at least two of the indicators of the block constraints is the
indicator that the performed births are pairwise distinct. -/
theorem distinctIndicatorExpansion : DistinctIndicatorExpansion := by
  intro I _ birth
  have h := sum_blockColl_birth birth (Finset.univ : Finset I)
  rw [blockColl_univ] at h
  have hiff : BirthsDistinctOn birth (Finset.univ : Finset I) ↔
      Graph.PerformedBirthsDistinct birth := by
    constructor
    · intro hd i j z hi hj
      exact hd i (Finset.mem_univ i) j (Finset.mem_univ j) z hi hj
    · intro hd i _ j _ z hi hj
      exact hd i j z hi hj
  refine Eq.trans (Finset.sum_congr rfl fun π _ => ?_) (h.trans ?_)
  · split_ifs <;> rfl
  · by_cases hd : Graph.PerformedBirthsDistinct birth
    · rw [if_pos hd, if_pos (hiff.mpr hd)]
    · rw [if_neg hd, if_neg fun h' => hd (hiff.mp h')]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostAbsoluteProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The absolute edge operation: one coefficient

Source: `verification/stage7-sources/S-02.tex`, lines 477–514 and 766–783
(`[S-02:0477–0514, 0767–0786]`).

Preparations for [S] Lemma 3.8 (`MemoryAbsolute`). This file collects what the row and the column
bound of the absolute edge both need about one coefficient `edgeCoef D θ i s c`.

* Counting in lists: `l38_card_filter_eq_countP`, `l38_countP_finRange`, `l38_countP_le_add`,
  `l38_filterMap_inj`; the slots (`l38_slotList_nodup`, `l38_length_filter_slotList`,
  `l38_card_unshared`: there are `t_g = ℓ + |C_g|` unshared slots).
* Memories as lists: `l38_filterMap_memAt_perm`, `l38_memZeroCount_eq`.
* `edgeAbsNewList` — the new memory of one big group as a function of the data of that group
  (`edgeNewList_eq_abs`); `edgeAbsElig`, `edgeAbsEligCount` — the old pending particles whose
  translated residue is zero, and their number `Z'` of (eq:promotion-count).
  `edgeAbsNewList_length_le` (`j' ≤ j + b`) and `edgeAbsEligCount_le`
  (`Z' ≤ #{zeros after the edge} + a`: "the remaining output damping").
* `EdgeAbsCond`, `edgeAbsReal`, `edgeCoef_of_cond`, `norm_edgeCoef_le` — the coefficient vanishes
  unless `EdgeAbsCond` holds, and then its modulus is at most the real prefactor times `sup |K_ν|`.
* `l38_smallDamping_le_one`, `l38_smallDamping_eq_prod` — the small endpoint factor
  `q^{(ω - M|𝒮|)/2}` is at most one at a small state, and it is a product over the small groups.
* `schurWeight_edgeTgt_le`, `rho_pow_memZeros_edgeTgt_le` — the Schur weight and the output
  damping of the target, as products over the big groups.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Counting in lists -/

/-- The number of the indices of a tuple at which a property holds is the count of the property
in the list of the tuple, for an arbitrary decidability instance on the indices. -/
theorem l38_card_filter_eq_countP {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Prop)
    [hp : DecidablePred p] {hd : DecidablePred fun i => p (f i)} :
    (@Finset.filter (Fin n) (fun i => p (f i)) hd Finset.univ).card =
      (List.ofFn f).countP (fun a => decide (p a)) := by
  have e : hd = fun i => hp (f i) := Subsingleton.elim _ _
  subst e
  have h := Multiset.countP_map f (Finset.univ : Finset (Fin n)).val p
  rw [Fin.univ_val_map, Multiset.coe_countP] at h
  exact h.symm

/-- The count of a property in the list of all indices is the number of the indices with the
property. -/
theorem l38_countP_finRange {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (List.finRange n).countP (fun j => decide (p j)) = (Finset.univ.filter p).card := by
  have h := l38_card_filter_eq_countP (id : Fin n → Fin n) p (hd := fun i => inferInstance)
  rw [List.ofFn_id] at h
  exact h.symm

/-- If `p` implies `q` or `r` on a list, the count of `p` is at most the sum of the counts of `q`
and of `r`. -/
theorem l38_countP_le_add {α : Type*} (p q r : α → Bool) (l : List α)
    (h : ∀ a ∈ l, p a = true → q a = true ∨ r a = true) :
    l.countP p ≤ l.countP q + l.countP r := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a t ih =>
    have ht : ∀ b ∈ t, p b = true → q b = true ∨ r b = true := fun b hb =>
      h b (List.mem_cons_of_mem a hb)
    have ha : p a = true → q a = true ∨ r a = true := h a List.mem_cons_self
    have hA : (if p a = true then 1 else 0) ≤
        (if q a = true then 1 else 0) + (if r a = true then 1 else 0) := by
      by_cases hp : p a = true
      · rcases ha hp with hq | hr
        · rw [if_pos hp, if_pos hq]
          exact Nat.le_add_right _ _
        · rw [if_pos hp, if_pos hr]
          exact Nat.le_add_left _ _
      · rw [if_neg hp]
        exact Nat.zero_le _
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    calc List.countP p t + (if p a = true then 1 else 0)
        ≤ (List.countP q t + List.countP r t) +
            ((if q a = true then 1 else 0) + (if r a = true then 1 else 0)) :=
          Nat.add_le_add (ih ht) hA
      _ = List.countP q t + (if q a = true then 1 else 0) +
            (List.countP r t + (if r a = true then 1 else 0)) := Nat.add_add_add_comm _ _ _ _

/-- Two families of optional values with the same pattern of missing values and the same list of
present values on a list of indices agree on that list. -/
theorem l38_filterMap_inj {α β : Type*} (f f' : α → Option β) (l : List α)
    (hpat : ∀ a ∈ l, (f a = none ↔ f' a = none)) (h : l.filterMap f = l.filterMap f') :
    ∀ a ∈ l, f a = f' a := by
  induction l with
  | nil =>
    intro a ha
    exact absurd ha List.not_mem_nil
  | cons x t ih =>
    have hpt : ∀ a ∈ t, (f a = none ↔ f' a = none) := fun a ha =>
      hpat a (List.mem_cons_of_mem x ha)
    have hpx := hpat x List.mem_cons_self
    obtain ⟨o, ho⟩ : ∃ o, o = f x := ⟨_, rfl⟩
    obtain ⟨o', ho'⟩ : ∃ o', o' = f' x := ⟨_, rfl⟩
    cases o with
    | none =>
      have hfx : f x = none := ho.symm
      have hfx' : f' x = none := hpx.mp hfx
      rw [List.filterMap_cons_none hfx, List.filterMap_cons_none hfx'] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [hfx, hfx']
      · exact ih hpt h a ha'
    | some b =>
      have hfx : f x = some b := ho.symm
      cases o' with
      | none =>
        have hfx' : f' x = none := ho'.symm
        have hcon : f x = none := hpx.mpr hfx'
        rw [hfx] at hcon
        exact absurd hcon (Option.some_ne_none b)
      | some b' =>
        have hfx' : f' x = some b' := ho'.symm
        rw [List.filterMap_cons_some hfx, List.filterMap_cons_some hfx'] at h
        obtain ⟨hb, htail⟩ := List.cons.inj h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha'
        · rw [hfx, hfx', hb]
        · exact ih hpt htail a ha'

/-! ### The slots -/

/-- The slots in their canonical order are listed without repetition. -/
theorem l38_slotList_nodup (J ℓ : ℕ) : (slotList J ℓ).Nodup := by
  unfold slotList
  refine List.Nodup.append ((List.nodup_finRange J).map Sum.inl_injective)
    ((List.nodup_finRange ℓ).map Sum.inr_injective) (List.disjoint_left.mpr fun sl h1 h2 => ?_)
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp h1
  obtain ⟨j, _, hj⟩ := List.mem_map.mp h2
  exact Sum.inr_ne_inl hj

/-- Every slot occurs in the canonical list of the slots. -/
theorem l38_mem_slotList {J ℓ : ℕ} (sl : Slot J ℓ) : sl ∈ slotList J ℓ := by
  unfold slotList
  rw [List.mem_append]
  rcases sl with i | j
  · exact Or.inl (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

/-- The slots of a set, in their canonical order, are as many as the set has elements. -/
theorem l38_length_filter_slotList {J ℓ : ℕ} (st : Finset (Slot J ℓ)) :
    ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).length = st.card := by
  have hnd : ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).Nodup :=
    (l38_slotList_nodup J ℓ).filter _
  have htf : ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).toFinset = st := by
    ext sl
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨l38_mem_slotList sl, decide_eq_true h⟩⟩
  rw [← List.toFinset_card_of_nodup hnd, htf]

/-- **There are `t_g = ℓ + |C_g|` unshared slots** [S-02:0056]. -/
theorem l38_card_unshared {J ℓ : ℕ} (Cg : Finset (Fin J))
    {hd : DecidablePred fun sl : Slot J ℓ => Unshared Cg sl} :
    (@Finset.filter _ (fun sl : Slot J ℓ => Unshared Cg sl) hd Finset.univ).card =
      ℓ + Cg.card := by
  have e : @Finset.filter _ (fun sl : Slot J ℓ => Unshared Cg sl) hd Finset.univ =
      Cg.disjSum (Finset.univ : Finset (Fin ℓ)) := by
    ext sl
    rw [Finset.mem_filter]
    rcases sl with i | j
    · rw [Finset.inl_mem_disjSum]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
    · rw [Finset.inr_mem_disjSum]
      exact ⟨fun _ => Finset.mem_univ _, fun _ => ⟨Finset.mem_univ _, trivial⟩⟩
  rw [e, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin, Nat.add_comm]

/-- The number of promoted indices is at most the number of promoting slots. -/
theorem l38_card_promoted_le {J ℓ Bc : ℕ} (pm : Slot J ℓ → Option (Fin Bc))
    {hd : DecidablePred fun sl : Slot J ℓ => pm sl ≠ none} :
    (Finset.univ.filter fun j : Fin Bc => ∃ sl, pm sl = some j).card ≤
      (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card := by
  have h1 : ∀ j : Fin Bc, (if ∃ sl, pm sl = some j then 1 else 0) ≤
      ∑ sl : Slot J ℓ, (if pm sl = some j then 1 else 0) := by
    intro j
    by_cases h : ∃ sl, pm sl = some j
    · rw [if_pos h]
      obtain ⟨sl₀, h₀⟩ := h
      calc (1 : ℕ) = (if pm sl₀ = some j then 1 else 0) := (if_pos h₀).symm
        _ ≤ ∑ sl : Slot J ℓ, (if pm sl = some j then 1 else 0) :=
            Finset.single_le_sum (f := fun sl : Slot J ℓ => if pm sl = some j then 1 else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ sl₀)
    · rw [if_neg h]
      exact Nat.zero_le _
  have h2 : ∀ sl : Slot J ℓ, ∑ j : Fin Bc, (if pm sl = some j then 1 else 0) ≤
      (if pm sl ≠ none then 1 else 0) := by
    intro sl
    obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
    cases o with
    | none =>
      have hz : ∑ j : Fin Bc, (if pm sl = some j then (1 : ℕ) else 0) = 0 :=
        Finset.sum_eq_zero fun j _ =>
          if_neg (fun h : pm sl = some j => Option.some_ne_none j (h.symm.trans ho))
      rw [hz]
      exact Nat.zero_le _
    | some j₀ =>
      have hne : pm sl ≠ none := fun h => Option.some_ne_none j₀ (ho.symm.trans h)
      rw [if_pos hne]
      exact ((Finset.sum_eq_single_of_mem
        (f := fun j : Fin Bc => if pm sl = some j then (1 : ℕ) else 0) j₀ (Finset.mem_univ _)
        (fun j _ hj => if_neg
          (fun h : pm sl = some j => hj (Option.some.inj (h.symm.trans ho))))).trans
          (if_pos ho)).le
  rw [Finset.card_filter, Finset.card_filter]
  calc ∑ j : Fin Bc, (if ∃ sl, pm sl = some j then 1 else 0)
      ≤ ∑ j : Fin Bc, ∑ sl : Slot J ℓ, (if pm sl = some j then 1 else 0) :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = ∑ sl : Slot J ℓ, ∑ j : Fin Bc, (if pm sl = some j then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ sl : Slot J ℓ, (if pm sl ≠ none then 1 else 0) :=
        Finset.sum_le_sum fun sl _ => h2 sl

/-! ### Memories as lists -/

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-- The particles of a memory, read through `memAt`, are the particles of the memory. -/
theorem l38_filterMap_memAt_perm (z : Mem 𝒢 Bc g) :
    ((List.finRange Bc).filterMap (memAt z)).Perm (List.ofFn z.2) := by
  obtain ⟨⟨n, hn⟩, x⟩ := z
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  have h := ghostSurvivors_lift_perm hn hnB x (∅ : Finset (Fin n))
  have e1 : ghostSurvivors (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
        ((∅ : Finset (Fin n)).map (Fin.castLEEmb hnB)) =
      (List.finRange Bc).filterMap (memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)) := by
    unfold ghostSurvivors
    refine congrArg (fun φ => (List.finRange Bc).filterMap φ) (funext fun i => ?_)
    refine if_neg ?_
    rw [Finset.map_empty]
    exact Finset.notMem_empty i
  have e2 : ghostSurvList x (∅ : Finset (Fin n)) = List.ofFn x := by
    unfold ghostSurvList
    rw [List.ofFn_eq_map]
    refine congrArg (fun l => l.map x) (List.filter_eq_self.mpr fun i _ => ?_)
    exact decide_eq_true (Finset.notMem_empty i)
  rw [e1, e2] at h
  exact h

/-- The number of the indices of a memory is its size. -/
theorem l38_countP_isSome_memAt (z : Mem 𝒢 Bc g) :
    (List.finRange Bc).countP (fun j => (memAt z j).isSome) = z.1.val := by
  have h := List.length_filterMap_eq_countP (f := memAt z) (l := List.finRange Bc)
  rw [← h, (l38_filterMap_memAt_perm z).length_eq, List.length_ofFn]

/-- A memory is determined by its particles at all indices. -/
theorem l38_mem_ext_memAt (z z' : Mem 𝒢 Bc g) (h : ∀ j, memAt z j = memAt z' j) : z = z' := by
  have hl : (List.finRange Bc).filterMap (memAt z) = (List.finRange Bc).filterMap (memAt z') :=
    congrArg (fun φ => (List.finRange Bc).filterMap φ) (funext h)
  have hp' : ((List.finRange Bc).filterMap (memAt z)).Perm (List.ofFn z'.2) := by
    rw [hl]
    exact l38_filterMap_memAt_perm z'
  have hp : (List.ofFn z.2).Perm (List.ofFn z'.2) := (l38_filterMap_memAt_perm z).symm.trans hp'
  obtain ⟨⟨n, hn⟩, x⟩ := z
  obtain ⟨⟨n', hn'⟩, x'⟩ := z'
  have hnn : n = n' := by
    have h1 := hp.length_eq
    rw [List.length_ofFn, List.length_ofFn] at h1
    exact h1
  subst hnn
  have hx : x = x' := by
    funext k
    have hk : k.val < Bc := lt_of_lt_of_le k.isLt (Nat.le_of_lt_succ hn)
    have h1 := h ⟨k.val, hk⟩
    have h2 : memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) ⟨k.val, hk⟩ = some (x k) := by
      unfold memAt
      exact dif_pos k.isLt
    have h3 : memAt (⟨⟨n, hn'⟩, x'⟩ : Mem 𝒢 Bc g) ⟨k.val, hk⟩ = some (x' k) := by
      unfold memAt
      exact dif_pos k.isLt
    rw [h2, h3] at h1
    exact Option.some.inj h1
  subst hx
  rfl

/-- **The number of pending zeros of a memory, as a count in the list of its particles.** -/
theorem l38_memZeroCount_eq (z : Mem 𝒢 Bc g) :
    memZeroCount z = (List.ofFn z.2).countP (fun pr => decide (pr.2 = 0)) := by
  unfold memZeroCount Graph.ghostZeroCount
  exact l38_card_filter_eq_countP z.2 (fun pr : Particle 𝒢 g => pr.2 = 0)

/-- The number of pending zeros of the memory of a list. -/
theorem l38_memZeroCount_memOfList {l : List (Particle 𝒢 g)} (h : l.length ≤ Bc) :
    memZeroCount (memOfList (Bc := Bc) l) = l.countP (fun pr => decide (pr.2 = 0)) := by
  rw [l38_memZeroCount_eq, ofFn_memOfList h]

/-! ### The new memory of one big group -/

/-- **The new memory of one big group after an edge**, as a list and as a function of the data of
that group: the step `Δ`, the old memory `z`, the source labels `xg`, the stored slots `st` and
the promotions `pm` (`edgeNewList`; steps 2 and 3 of [S-02:0487–0502]). -/
def edgeAbsNewList {J ℓ : ℕ} (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) : List (Particle 𝒢 g) :=
  ((List.finRange Bc).filterMap fun j =>
      if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)) ++
    ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).map fun sl =>
      shiftParticle Δ ⟨xg sl, 0⟩

/-- **The old pending particle with index `j` has translated residue zero** [S-02:0494–0497]:
the particles which may be promoted. -/
def edgeAbsElig (Δ : ℤ) (z : Mem 𝒢 Bc g) (j : Fin Bc) : Prop :=
  ∃ pr : Particle 𝒢 g, memAt z j = some pr ∧ (shiftParticle Δ pr).2 = 0

open _root_.Classical in
/-- **`Z'`**, the number of old pending particles with zero translated residue
(eq:promotion-count) [S-02:0768–0776]. -/
def edgeAbsEligCount (Δ : ℤ) (z : Mem 𝒢 Bc g) : ℕ :=
  (Finset.univ.filter fun j : Fin Bc => edgeAbsElig Δ z j).card

/-- `j' ≤ j + b`: the new memory has at most the old size plus the number of stores. -/
theorem edgeAbsNewList_length_le {J ℓ : ℕ} (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) :
    (edgeAbsNewList Δ z xg st pm).length ≤ z.1.val + st.card := by
  unfold edgeAbsNewList
  rw [List.length_append, List.length_map, l38_length_filter_slotList,
    List.length_filterMap_eq_countP]
  refine Nat.add_le_add_right ?_ _
  refine (List.countP_mono_left fun j _ hj => ?_).trans (l38_countP_isSome_memAt z).le
  have hj' : (if ∃ sl, pm sl = some j then none
      else (memAt z j).map (shiftParticle Δ)).isSome = true := hj
  show (memAt z j).isSome = true
  by_cases hc : ∃ sl, pm sl = some j
  · rw [if_pos hc] at hj'
    exact absurd hj' Bool.false_ne_true
  · rw [if_neg hc, Option.isSome_map] at hj'
    exact hj'

open _root_.Classical in
/-- **`Z' ≤ #{zeros of the new memory} + a`** [S-02:0768–0776]: the old pending particles with
zero translated residue are promoted or remain pending zeros ("their ordered promotions and the
remaining output damping"). -/
theorem edgeAbsEligCount_le {J ℓ : ℕ} (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) {hd : DecidablePred fun sl : Slot J ℓ => pm sl ≠ none} :
    edgeAbsEligCount Δ z ≤
      (edgeAbsNewList Δ z xg st pm).countP (fun pr => decide (pr.2 = 0)) +
        (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card := by
  have h1 : edgeAbsEligCount Δ z =
      (List.finRange Bc).countP (fun j => decide (edgeAbsElig Δ z j)) := by
    unfold edgeAbsEligCount
    exact (l38_countP_finRange (fun j => edgeAbsElig Δ z j)).symm
  have h2 : (List.finRange Bc).countP (fun j => decide (∃ sl, pm sl = some j)) ≤
      (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card := by
    rw [l38_countP_finRange (fun j : Fin Bc => ∃ sl, pm sl = some j)]
    exact l38_card_promoted_le pm
  have h3 : ((List.finRange Bc).filterMap fun j =>
        if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)).countP
          (fun pr => decide (pr.2 = 0)) ≤
      (edgeAbsNewList Δ z xg st pm).countP (fun pr => decide (pr.2 = 0)) := by
    unfold edgeAbsNewList
    rw [List.countP_append]
    exact Nat.le_add_right _ _
  have h4 : (List.finRange Bc).countP (fun j => decide (edgeAbsElig Δ z j)) ≤
      ((List.finRange Bc).filterMap fun j =>
        if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)).countP
          (fun pr => decide (pr.2 = 0)) +
        (List.finRange Bc).countP (fun j => decide (∃ sl, pm sl = some j)) := by
    rw [List.countP_filterMap]
    refine l38_countP_le_add _ _ _ _ fun j _ hj => ?_
    have he : edgeAbsElig Δ z j := of_decide_eq_true hj
    by_cases hc : ∃ sl, pm sl = some j
    · exact Or.inr (decide_eq_true hc)
    · refine Or.inl ?_
      obtain ⟨pr, hpr, h0⟩ := he
      show (((if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)).map
        fun pr' : Particle 𝒢 g => decide (pr'.2 = 0)).getD false) = true
      rw [if_neg hc, hpr]
      show decide ((shiftParticle Δ pr).2 = 0) = true
      exact decide_eq_true h0
  calc edgeAbsEligCount Δ z
      = (List.finRange Bc).countP (fun j => decide (edgeAbsElig Δ z j)) := h1
    _ ≤ ((List.finRange Bc).filterMap fun j =>
          if ∃ sl, pm sl = some j then none else (memAt z j).map (shiftParticle Δ)).countP
            (fun pr => decide (pr.2 = 0)) +
          (List.finRange Bc).countP (fun j => decide (∃ sl, pm sl = some j)) := h4
    _ ≤ (edgeAbsNewList Δ z xg st pm).countP (fun pr => decide (pr.2 = 0)) +
          (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) hd Finset.univ).card :=
        Nat.add_le_add h3 h2

end OneGroup

/-! ### Scalars -/

/-- `ρ^n ≤ ρ^Z ρ^{-a}` when `Z ≤ n + a` and `0 < ρ ≤ 1`. -/
theorem l38_pow_le {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {n a Z : ℕ} (h : Z ≤ n + a) :
    ρ ^ n ≤ ρ ^ Z * ρ⁻¹ ^ a := by
  have e : ρ ^ n = ρ ^ (n + a) * ρ⁻¹ ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ h0.ne', one_pow, mul_one]
  rw [e]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0.le h1 h)
    (pow_nonneg (inv_nonneg.mpr h0.le) _)

/-! ### The small endpoint factors -/

section Small

variable {S B : Type} [Fintype S] {𝒢 : GroupFamily S B} {J ℓ : ℕ}

theorem l38_smallDamping_pos {q : ℝ} (hq : 0 < q) (y : ResVec (smallPrimes 𝒢)) :
    0 < smallDamping 𝒢 J ℓ q y := by
  unfold smallDamping
  exact Real.rpow_pos_of_pos hq _

/-- "The source damping is at most one" [S-02:0150–0151], for the small groups: at a small state
every small group has at least `M` zero coordinates. -/
theorem l38_smallDamping_le_one {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    {y : ResVec (smallPrimes 𝒢)} {xs : LabelList 𝒢.small J ℓ} (h : IsSmallState 𝒢 y xs) :
    smallDamping 𝒢 J ℓ q y ≤ 1 := by
  have hS : Fintype.card S * (J + ℓ) ≤
      ∑ g : S, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) := by
    calc Fintype.card S * (J + ℓ) = ∑ _g : S, (J + ℓ) := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ g : S, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) :=
          Finset.sum_le_sum fun g _ =>
            Schur.slots_le_countHits (hit := fun p => (resModel (smallPrimes 𝒢)).hit p y)
              (xs g) (h.1 g) (h.2 g)
  have hnat : (J + ℓ) * Fintype.card S ≤
      ∑ g : S, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) := by
    rw [Nat.mul_comm]
    exact hS
  have hreal : ((J + ℓ : ℕ) : ℝ) * (Fintype.card S : ℝ) ≤
      ((∑ g : S, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) : ℕ) :
        ℝ) := by
    exact_mod_cast hnat
  unfold smallDamping
  exact Real.rpow_le_one hq.le hq1 (div_nonneg (sub_nonneg.mpr hreal) zero_le_two)

/-- The small endpoint factor is the product over the small groups of `q^{(ω_g - M)/2}`. -/
theorem l38_smallDamping_eq_prod {q : ℝ} (hq : 0 < q) (y : ResVec (smallPrimes 𝒢)) :
    smallDamping 𝒢 J ℓ q y =
      ∏ g : S, q ^ ((((countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) : ℕ) :
        ℝ) - ((J + ℓ : ℕ) : ℝ)) / 2) := by
  have hexp : (((∑ g : S, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y)
        (𝒢.small g) : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card S : ℝ)) / 2 =
      ∑ g : S, (((countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) : ℕ) :
        ℝ) - ((J + ℓ : ℕ) : ℝ)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_sum, mul_comm (Fintype.card S : ℝ)]
  unfold smallDamping
  rw [hexp, Real.rpow_sum_of_pos hq]

end Small

/-! ### One coefficient -/

section Edge

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

omit [DecidableEq S] [DecidableEq B] in
/-- `edgeNewList` is `edgeAbsNewList` for the data of the group. -/
theorem edgeNewList_eq_abs (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (g : B) :
    edgeNewList D i s c g =
      edgeAbsNewList (edgeStep D i s c) (s.mem g) (s.xb g) (c.store g) (c.promo g) := rfl

/-- **The conditions under which the coefficient of the row transition of an edge does not
vanish** [S-02:0480–0514] (the condition of `edgeCoef`). -/
def EdgeAbsCond (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) : Prop :=
  memTotal s ≤ Bc ∧ (∑ g, (edgeNewList D i s c g).length) ≤ Bc ∧
    IsSmallState 𝒢 s.y s.xs ∧
    IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) c.xsT ∧
    SharedSmall s.xs c.xsT ∧ SharedBig (D.fam c.ν).C s.xb c.xbT ∧
    AuxAvoids (D.fam c.ν).C c.r ((s.xs, s.xb) : Lists 𝒢 J ℓ) ∧
    AuxAvoids (D.fam c.ν).C c.r ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) ∧
    StoreValid D s c ∧ PromoValid D i s c

open _root_.Classical in
/-- **The real prefactor of the coefficient of an edge** [S-02:0480–0514]: the probability of the
free labels, the two factors `ρ^{#zeros}`, `V_g^{-1}` per promotion, `μ̃_g` of the fresh labels,
the small normalization and the two small endpoint factors. -/
def edgeAbsReal (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) : ℝ :=
  auxWeight 𝒢.big (D.fam c.ν).C c.r *
    D.ρ ^ memZeros s *
    (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
    (∏ g, ∏ sl : Slot J ℓ, if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) *
    D.ρ ^ memZeros (edgeTgt D i s c) *
    ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
      (smallDamping 𝒢 J ℓ D.q s.y *
        smallDamping 𝒢 J ℓ D.q
          ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y)))

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The coefficient where its conditions hold. -/
theorem edgeCoef_of_cond (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (h : EdgeAbsCond D i s c) :
    edgeCoef D θ i s c =
      ((edgeAbsReal D i s c : ℝ) : ℂ) *
        (edgeMultiplier D i s c * expUnit (θ * (edgeStep D i s c : ℝ))) := by
  unfold edgeCoef edgeAbsReal
  exact if_pos h

omit [DecidableEq S] [DecidableEq B] in
/-- The coefficient vanishes where its conditions fail. -/
theorem edgeCoef_of_not_cond (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (h : ¬EdgeAbsCond D i s c) : edgeCoef D θ i s c = 0 := by
  unfold edgeCoef
  exact if_neg h

omit [DecidableEq S] in
/-- The oriented multiplier `K_ν D^{iζ}` (or its conjugate) has modulus at most `sup |K_ν|`. -/
theorem norm_edgeMultiplier_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) :
    ‖edgeMultiplier D i s c‖ ≤ ((D.fam c.ν).supNorm : ℝ) := by
  have h1 : ∀ p p' : LabelList 𝒢.big J ℓ,
      ‖(D.fam c.ν).K p p' c.r * ((edgeDil D s c : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)‖ ≤
        ((D.fam c.ν).supNorm : ℝ) := by
    intro p p'
    rw [norm_mul]
    calc ‖(D.fam c.ν).K p p' c.r‖ * ‖((edgeDil D s c : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)‖
        ≤ ((D.fam c.ν).supNorm : ℝ) * 1 :=
          mul_le_mul ((D.fam c.ν).norm_K_le p p' c.r)
            (Schur.norm_natCast_cpow_mul_I_le_one _ D.ζ) (norm_nonneg _) (NNReal.coe_nonneg _)
      _ = ((D.fam c.ν).supNorm : ℝ) := mul_one _
  unfold edgeMultiplier
  split_ifs
  · exact h1 _ _
  · rw [RCLike.norm_conj]
    exact h1 _ _

omit [DecidableEq S] in
/-- **The modulus of a coefficient** is at most its real prefactor times `sup |K_ν|`
("the coefficient is bounded by its supremum", [S-02:1125–1126]). -/
theorem norm_edgeCoef_le (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (h : EdgeAbsCond D i s c) (hR : 0 ≤ edgeAbsReal D i s c) :
    ‖edgeCoef D θ i s c‖ ≤ edgeAbsReal D i s c * ((D.fam c.ν).supNorm : ℝ) := by
  rw [edgeCoef_of_cond D θ i s c h, norm_mul, Complex.norm_of_nonneg hR, norm_mul, norm_expUnit,
    mul_one]
  exact mul_le_mul_of_nonneg_left (norm_edgeMultiplier_le D i s c) hR

omit [DecidableEq S] [DecidableEq B] in
/-- A nonvanishing coefficient leads to new memories of size at most the cutoff. -/
theorem edgeNewList_length_le_of_sum (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ Bc) (g : B) :
    (edgeNewList D i s c g).length ≤ Bc :=
  (Finset.single_le_sum (f := fun g => (edgeNewList D i s c g).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans h2

omit [DecidableEq S] [DecidableEq B] in
/-- **The Schur weight of the target**: `v^{j'_tot} ≤ v^{j_tot} ∏_g v^{b_g}` for `v ≥ 1`
("the Schur weight contributes `v^{b_g - a_g}`", [S-02:0778]; the gain `v^{-a_g}` is not
used). -/
theorem schurWeight_edgeTgt_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) {v : ℝ} (hv : 1 ≤ v)
    (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ Bc) :
    schurWeight v (edgeTgt D i s c) ≤ schurWeight v s * ∏ g, v ^ (c.store g).card := by
  have h1 : memTotal (edgeTgt D i s c) = ∑ g, (edgeNewList D i s c g).length := by
    unfold memTotal
    exact Finset.sum_congr rfl fun g _ =>
      memOfList_size (edgeNewList_length_le_of_sum D i s c h2 g)
  have h3 : (∑ g, (edgeNewList D i s c g).length) ≤ memTotal s + ∑ g, (c.store g).card := by
    unfold memTotal
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun g _ => ?_
    rw [edgeNewList_eq_abs]
    exact edgeAbsNewList_length_le _ _ _ _ _
  unfold schurWeight
  rw [h1, Finset.prod_pow_eq_pow_sum, ← pow_add]
  exact pow_le_pow_right₀ hv h3

omit [DecidableEq S] [DecidableEq B] in
/-- **The output damping**: `ρ^{#zeros after the edge} ≤ ∏_g ρ^{Z'_g} ρ^{-a_g}`
(eq:promotion-count) [S-02:0768–0778]; "damping of stored particles can be discarded for this
upper bound". -/
theorem rho_pow_memZeros_edgeTgt_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ Bc) :
    ρ ^ memZeros (edgeTgt D i s c) ≤
      ∏ g, (ρ ^ edgeAbsEligCount (edgeStep D i s c) (s.mem g) * ρ⁻¹ ^ promoCount c g) := by
  have h1 : ρ ^ memZeros (edgeTgt D i s c) =
      ∏ g, ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeNewList D i s c g)) :=
    (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun g => memZeroCount (memOfList (Bc := Bc) (edgeNewList D i s c g))) ρ).symm
  rw [h1]
  refine Finset.prod_le_prod (fun g _ => pow_nonneg hρ0.le _) fun g _ => ?_
  refine l38_pow_le hρ0 hρ1 ?_
  rw [l38_memZeroCount_memOfList (edgeNewList_length_le_of_sum D i s c h2 g), edgeNewList_eq_abs]
  unfold promoCount
  exact edgeAbsEligCount_le _ _ _ _ _

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

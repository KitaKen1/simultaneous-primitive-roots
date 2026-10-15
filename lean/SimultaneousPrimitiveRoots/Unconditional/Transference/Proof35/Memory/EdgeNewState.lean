module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeGroupValid
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One big group after an edge: every prime still occurs at most once

Source: `verification/stage7-sources/S-02.tex`, lines 569–581 (`[S-02:0569–0581]`): "Immediate
promotion of a newly stored particle is impossible. A numerical prime occupies at most one active
slot or pending particle, because it has only one birth."

Tools for the proof of (M3) `EdgeStepFactor`, for one big group in which every prime occurs at
most once (`EdgeGroupHyp`) and an admissible local choice with new fresh births:

* `edg_newList_nodup` — the primes of the new memory (the old particles which are not promoted,
  and the stored labels) are pairwise distinct;
* `edg_newList_mem_U` — they were born;
* `edg_new_facts` — no target label is the prime of a particle of the new memory, and every target
  label was born or is a fresh birth;
* `edg_new_consistent` — the same facts for a memory whose particles are the new list.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- The number of the elements with a property does not depend on the decidability instance. -/
theorem edg_card_filter_inst {ι : Type*} [Fintype ι] (P : ι → Prop) (i1 i2 : DecidablePred P) :
    (@Finset.filter ι P i1 Finset.univ).card = (@Finset.filter ι P i2 Finset.univ).card := by
  have h : i1 = i2 := Subsingleton.elim _ _
  subst h
  rfl

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-- **The primes of the new memory of a group are pairwise distinct**: the primes of the old
particles which are kept are distinct, the stored labels are distinct, and a pending prime is not
active. -/
theorem edg_newList_nodup {n : ℕ} (hn : n < Bc + 1) (zf : Fin n → Particle 𝒢 g) (Δ : ℤ)
    (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (hx : Function.Injective x)
    (hz : Function.Injective fun j : Fin n => (zf j).1) (hne : ∀ sl (j : Fin n), x sl ≠ (zf j).1)
    (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc)) :
    ((edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm).map fun w => w.1).Nodup := by
  have hkept : ∀ (j : Fin Bc) (b : {p : ℕ // p ∈ 𝒢.big g}),
      ((if ∃ sl, pm sl = some j then none
        else (memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j).map (shiftParticle Δ)).map
          fun w : Particle 𝒢 g => w.1) = some b →
        ∃ hlt : j.val < n, (zf ⟨j.val, hlt⟩).1 = b := by
    intro j b h
    obtain ⟨w, hw, hwb⟩ := Option.map_eq_some_iff.mp h
    by_cases hc : ∃ sl, pm sl = some j
    · rw [if_pos hc] at hw
      cases hw
    · rw [if_neg hc] at hw
      obtain ⟨w₀, hw₀, hsh⟩ := Option.map_eq_some_iff.mp hw
      obtain ⟨hlt, hzw⟩ := (edg_memAt_eq_some hn zf j w₀).mp hw₀
      refine ⟨hlt, ?_⟩
      rw [hzw, ← hwb, ← hsh]
      rfl
  unfold edgeAbsNewList
  rw [List.map_append]
  refine List.Nodup.append ?_ ?_ ?_
  · rw [List.map_filterMap]
    refine List.Nodup.filterMap (fun j j' b hb hb' => ?_) (List.nodup_finRange Bc)
    obtain ⟨hlt, h1⟩ := hkept j b hb
    obtain ⟨hlt', h1'⟩ := hkept j' b hb'
    have h2 : (⟨j.val, hlt⟩ : Fin n) = ⟨j'.val, hlt'⟩ := hz (h1.trans h1'.symm)
    exact Fin.ext (congrArg (fun q : Fin n => q.val) h2)
  · rw [List.map_map]
    exact List.Nodup.map hx ((l38_slotList_nodup J ℓ).filter _)
  · refine List.disjoint_left.mpr fun a ha hb => ?_
    rw [List.map_filterMap] at ha
    obtain ⟨j, -, hj⟩ := List.mem_filterMap.mp ha
    obtain ⟨hlt, h1⟩ := hkept j a hj
    rw [List.map_map] at hb
    obtain ⟨sl, -, hsl⟩ := List.mem_map.mp hb
    have h2 : x sl = a := hsl
    exact hne sl ⟨j.val, hlt⟩ (h2.trans h1.symm)

section Facts

variable {x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}} {C : Finset (Fin J)} {n : ℕ}
  {zf : Fin n → Particle 𝒢 g} {U : Finset ℕ} {Δ : ℤ} {Dil : ℕ}

/-- The primes of the new memory were born. -/
theorem edg_newList_mem_U (H : EdgeGroupHyp x y C zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (Δ : ℤ) (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc)) :
    ∀ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, (w.1 : ℕ) ∈ U := by
  intro w hw
  rcases (edg_exists_newList hn hnB zf Δ x st pm w.1).mp ⟨w, hw, rfl⟩ with
    ⟨j, -, hp⟩ | ⟨sl, -, hp⟩
  · rw [← hp]
    exact H.hzU j
  · rw [← hp]
    exact H.hxU sl

/-- **After an edge with admissible stores and promotions and new fresh births**: no target label
is the prime of a particle of the new memory, and every target label was born or is a fresh
birth. -/
theorem edg_new_facts (H : EdgeGroupHyp x y C zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    {st : Finset (Slot J ℓ)} {pm : Slot J ℓ → Option (Fin Bc)} (hnew : EdgeNewG y C U pm)
    (hstore : EdgeStoreG x C Dil st)
    (hpromo : EdgePromoG y C Δ Dil (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) pm) :
    (∀ sl, ∀ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, y sl ≠ w.1) ∧
      ∀ sl, (y sl : ℕ) ∈ U ∪ edgeFreshSet y C pm := by
  have hk := edg_slot_kind hn hnB hnew hpromo
  refine ⟨fun sl w hw heq => ?_, fun sl => ?_⟩
  · have hex : ∃ w' ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, w'.1 = y sl :=
      ⟨w, hw, heq.symm⟩
    rcases (edg_exists_newList hn hnB zf Δ x st pm (y sl)).mp hex with
      ⟨j, hj, hp⟩ | ⟨sl', hsl', hp⟩
    · rcases hk sl with ⟨j₀, hj₀, rfl⟩ | ⟨-, j₁, hpm, hyj, -, -⟩ | ⟨-, hnU⟩
      · exact H.hne (Sum.inl j₀) j ((H.hSh j₀ hj₀).symm.trans hp.symm)
      · have hjj : j = j₁ := H.hz (hp.trans hyj)
        rw [hjj] at hj
        exact hj ⟨sl, hpm⟩
      · have hU' : (y sl : ℕ) ∈ U := by
          rw [← hp]
          exact H.hzU j
        exact hnU hU'
    · rcases hk sl with ⟨j₀, hj₀, rfl⟩ | ⟨-, j₁, -, hyj, -, -⟩ | ⟨-, hnU⟩
      · have h1 : sl' = Sum.inl j₀ := H.hx (hp.trans (H.hSh j₀ hj₀))
        have h2 := (hstore sl' hsl').1
        rw [h1] at h2
        exact hj₀ h2
      · exact H.hne sl' j₁ (hp.trans hyj)
      · have hU' : (y sl : ℕ) ∈ U := by
          rw [← hp]
          exact H.hxU sl'
        exact hnU hU'
  · rcases hk sl with ⟨j₀, hj₀, rfl⟩ | ⟨-, j₁, -, hyj, -, -⟩ | ⟨hf, -⟩
    · rw [H.hSh j₀ hj₀]
      exact Finset.mem_union_left _ (H.hxU _)
    · rw [hyj]
      exact Finset.mem_union_left _ (H.hzU j₁)
    · exact Finset.mem_union_right _ ((mem_edgeFreshSet y C pm _).mpr ⟨sl, hf, rfl⟩)

end Facts

/-- **After an edge every prime of the group still occurs at most once** [S-02:0577–0578]: for an
admissible local choice with new fresh births and a memory `m` whose particles are the new list,
the target list is injective, the primes of the particles of `m` are pairwise distinct, none of
them is a target label, every target label was born or is a fresh birth, and the primes of `m`
were born. -/
theorem edg_new_consistent {x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}} {C : Finset (Fin J)}
    (z : Mem 𝒢 Bc g) {U : Finset ℕ} {Δ : ℤ} {Dil : ℕ} (H : EdgeGroupHyp x y C z.2 U)
    {st : Finset (Slot J ℓ)} {pm : Slot J ℓ → Option (Fin Bc)} (hnew : EdgeNewG y C U pm)
    (hstore : EdgeStoreG x C Dil st) (hpromo : EdgePromoG y C Δ Dil z pm) (m : Mem 𝒢 Bc g)
    (hm : List.ofFn m.2 = edgeAbsNewList Δ z x st pm) :
    Function.Injective y ∧ (Function.Injective fun j : Fin m.1.val => (m.2 j).1) ∧
      (∀ sl (j : Fin m.1.val), y sl ≠ (m.2 j).1) ∧
      (∀ sl, (y sl : ℕ) ∈ U ∪ edgeFreshSet y C pm) ∧
      ∀ j : Fin m.1.val, ((m.2 j).1 : ℕ) ∈ U := by
  obtain ⟨⟨n, hn⟩, zf⟩ := z
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  have H' : EdgeGroupHyp x y C zf U := H
  have hm' : List.ofFn m.2 = edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm := hm
  have hmem : ∀ j : Fin m.1.val,
      m.2 j ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm := fun j => by
    rw [← hm']
    exact (List.mem_ofFn' m.2 (m.2 j)).mpr (Set.mem_range_self j)
  have hf := edg_new_facts H' hn hnB hnew hstore hpromo
  refine ⟨(edg_good_of_valid H' hn hnB hnew hpromo).1, ?_, fun sl j => hf.1 sl _ (hmem j), hf.2,
    fun j => edg_newList_mem_U H' hn hnB Δ st pm _ (hmem j)⟩
  have hnd := edg_newList_nodup hn zf Δ x H'.hx H'.hz H'.hne st pm
  rw [← hm'] at hnd
  have e : (List.ofFn m.2).map (fun w : Particle 𝒢 g => w.1) =
      List.ofFn fun j : Fin m.1.val => (m.2 j).1 := List.map_ofFn
  rw [e] at hnd
  exact List.nodup_ofFn.mp hnd

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

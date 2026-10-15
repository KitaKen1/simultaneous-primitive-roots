module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgePrimeFactor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One big group at an edge: the admissible stores and promotions

Source: `verification/stage7-sources/S-02.tex`, lines 487–503 and 569–581
(`[S-02:0487–0503, 0569–0581]`).

Tools for the proof of (M3) `EdgeStepFactor`, for one big group `g` with source list `x`, target
list `y`, set `C = C_g`, old memory `z` and the set `U` of the primes born so far.

* `EdgeStoreG`, `EdgePromoG`, `EdgeFreshG`, `EdgeNewG`, `edgeFreshSet` — the conditions
  `StoreValid`, `PromoValid` and "the fresh births are new" for the local choice of one group (the
  stored slots and the promotions), and the set of its fresh labels.
* `edgeTG` — the term of a local choice of one group: the indicator of these conditions, the
  factors `ρ^{#zeros}` before and after, `V_g^{-1}` per promotion, `μ̃_g` of the fresh labels, and
  the factor `PrimeVals.evalL` of the group at the new state.
* `EdgeGroupHyp` — every prime of the group occurs at most once (in the source state), and the
  shared labels are copied.
* `EdgeGood` — the target list is injective and the label of every unshared target slot is the
  prime of a pending particle which may be promoted, or was not born.
* `edg_good_of_valid` — an admissible local choice exists only if `EdgeGood` holds;
  `edgPromo`, `edg_promo_unique`, `edgPromo_valid` — then the promotions are determined: "the index
  of the unique pending particle with the label of the target slot".
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-! ### The local conditions -/

/-- A slot is unshared or one of the shared slots `Sum.inl j`, `j ∉ C`. -/
theorem edg_unshared_or (C : Finset (Fin J)) (sl : Slot J ℓ) :
    Unshared C sl ∨ ∃ j : Fin J, j ∉ C ∧ sl = Sum.inl j := by
  rcases sl with j | k
  · by_cases hj : j ∈ C
    · exact Or.inl hj
    · exact Or.inr ⟨j, hj, rfl⟩
  · exact Or.inl trivial

/-- **The stores of one group are admissible** (`StoreValid`): the stored slots are unshared and
their labels do not divide `D`. -/
def EdgeStoreG (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (Dil : ℕ)
    (st : Finset (Slot J ℓ)) : Prop :=
  ∀ sl ∈ st, Unshared C sl ∧ ¬((x sl : ℕ) ∣ Dil)

/-- **The promotions of one group are admissible** (`PromoValid`). -/
def EdgePromoG (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (Δ : ℤ) (Dil : ℕ)
    (z : Mem 𝒢 Bc g) (pm : Slot J ℓ → Option (Fin Bc)) : Prop :=
  ∀ (sl : Slot J ℓ) (j : Fin Bc), pm sl = some j →
    Unshared C sl ∧ (∀ sl', pm sl' = some j → sl' = sl) ∧
      ∃ w : Particle 𝒢 g, memAt z j = some w ∧ (shiftParticle Δ w).2 = 0 ∧
        ¬((w.1 : ℕ) ∣ Dil) ∧ y sl = w.1

/-- A fresh target slot of one group: unshared and not a promotion. -/
def EdgeFreshG (C : Finset (Fin J)) (pm : Slot J ℓ → Option (Fin Bc)) (sl : Slot J ℓ) : Prop :=
  Unshared C sl ∧ pm sl = none

/-- **The fresh births of one group are new**: pairwise distinct and not born. -/
def EdgeNewG (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (U : Finset ℕ)
    (pm : Slot J ℓ → Option (Fin Bc)) : Prop :=
  (∀ sl sl', EdgeFreshG C pm sl → EdgeFreshG C pm sl' → y sl = y sl' → sl = sl') ∧
    ∀ sl, EdgeFreshG C pm sl → (y sl : ℕ) ∉ U

open _root_.Classical in
/-- The set of the fresh labels of one group. -/
def edgeFreshSet (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J))
    (pm : Slot J ℓ → Option (Fin Bc)) : Finset ℕ :=
  (Finset.univ.filter fun sl => EdgeFreshG C pm sl).image fun sl => (y sl : ℕ)

open _root_.Classical in
theorem mem_edgeFreshSet (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J))
    (pm : Slot J ℓ → Option (Fin Bc)) (z : ℕ) :
    z ∈ edgeFreshSet y C pm ↔ ∃ sl, EdgeFreshG C pm sl ∧ (y sl : ℕ) = z := by
  unfold edgeFreshSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨sl, hsl, h⟩
    rw [Finset.mem_filter] at hsl
    exact ⟨sl, hsl.2, h⟩
  · rintro ⟨sl, hf, h⟩
    refine ⟨sl, ?_, h⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hf⟩

open _root_.Classical in
/-- **The term of a local choice of one big group** in the sum over the stores and promotions of
an edge: zero unless the fresh births are new and the stores and promotions are admissible;
otherwise `ρ^{#zeros}` of the old memory, `V_g^{-1}` per promotion, `μ̃_g(p)` for every fresh
label, `ρ^{#zeros}` of the new memory, and the factor of the group in the product of the values
`v` at the new state. -/
def edgeTG (ρ V : ℝ) (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v : PrimeVals 𝒢)
    (x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (Δ : ℤ) (Dil : ℕ)
    (z : Mem 𝒢 Bc g) (U : Finset ℕ)
    (c : Finset (Slot J ℓ) × (Slot J ℓ → Option (Fin Bc))) : ℝ :=
  if EdgeNewG y C U c.2 ∧ EdgeStoreG x C Dil c.1 ∧ EdgePromoG y C Δ Dil z c.2 then
    ρ ^ memZeroCount z * (V ^ (Finset.univ.filter fun sl => c.2 sl ≠ none).card)⁻¹ *
        (∏ sl : Slot J ℓ, if EdgeFreshG C c.2 sl then μ (y sl) else 1) *
        ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeAbsNewList Δ z x c.1 c.2)) *
      v.evalL g y (edgeAbsNewList Δ z x c.1 c.2) (U ∪ edgeFreshSet y C c.2)
  else 0

/-- **Every prime of the group occurs at most once in the source state**, and the shared labels
are copied: the source list is injective, the pending particles have distinct primes which are
not active, every prime which is present was born, and the target list has the shared labels of
the source list. -/
structure EdgeGroupHyp (x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) {n : ℕ}
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) : Prop where
  hx : Function.Injective x
  hz : Function.Injective fun j : Fin n => (zf j).1
  hne : ∀ sl (j : Fin n), x sl ≠ (zf j).1
  hzU : ∀ j : Fin n, ((zf j).1 : ℕ) ∈ U
  hxU : ∀ sl, (x sl : ℕ) ∈ U
  hSh : ∀ j : Fin J, j ∉ C → y (Sum.inl j) = x (Sum.inl j)

/-- **The target list is compatible with the source state**: it is injective, and the label of
every unshared target slot is the prime of a pending particle which may be promoted (translated
residue zero, `p ∤ D`), or a prime which was not born. -/
def EdgeGood (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (Δ : ℤ) (Dil : ℕ)
    {n : ℕ} (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) : Prop :=
  Function.Injective y ∧ ∀ sl, Unshared C sl →
    (∃ j : Fin n, (zf j).1 = y sl ∧ (shiftParticle Δ (zf j)).2 = 0 ∧
      ¬(((zf j).1 : ℕ) ∣ Dil)) ∨ (y sl : ℕ) ∉ U

/-! ### An admissible local choice forces `EdgeGood` -/

section Valid

variable {x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}} {C : Finset (Fin J)} {n : ℕ}
  {zf : Fin n → Particle 𝒢 g} {U : Finset ℕ} {Δ : ℤ} {Dil : ℕ}
  {pm : Slot J ℓ → Option (Fin Bc)}

/-- **The three kinds of target slots** for admissible promotions with new fresh births: shared;
promoted, with the prime of a pending particle which may be promoted; fresh, with a prime which
was not born. -/
theorem edg_slot_kind (hn : n < Bc + 1) (hnB : n ≤ Bc) (hnew : EdgeNewG y C U pm)
    (hpromo : EdgePromoG y C Δ Dil (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) pm) (sl : Slot J ℓ) :
    (∃ j : Fin J, j ∉ C ∧ sl = Sum.inl j) ∨
      (Unshared C sl ∧ ∃ j : Fin n, pm sl = some (Fin.castLE hnB j) ∧ y sl = (zf j).1 ∧
        (shiftParticle Δ (zf j)).2 = 0 ∧ ¬(((zf j).1 : ℕ) ∣ Dil)) ∨
      (EdgeFreshG C pm sl ∧ (y sl : ℕ) ∉ U) := by
  rcases edg_unshared_or C sl with hu | hs
  · obtain ⟨o, ho⟩ : ∃ o, pm sl = o := ⟨_, rfl⟩
    cases o with
    | none => exact Or.inr (Or.inr ⟨⟨hu, ho⟩, hnew.2 sl ⟨hu, ho⟩⟩)
    | some j' =>
      obtain ⟨-, -, w, hmem, hsh, hdv, hy⟩ := hpromo sl j' ho
      obtain ⟨hlt, hw⟩ := (edg_memAt_eq_some hn zf j' w).mp hmem
      have hcast : Fin.castLE hnB (⟨j'.val, hlt⟩ : Fin n) = j' := Fin.ext rfl
      refine Or.inr (Or.inl ⟨hu, ⟨j'.val, hlt⟩, ?_, ?_, ?_, ?_⟩)
      · rw [hcast]
        exact ho
      · rw [hw]
        exact hy
      · rw [hw]
        exact hsh
      · rw [hw]
        exact hdv
  · exact Or.inl hs

/-- **An admissible local choice exists only if the target list is compatible with the source
state.** -/
theorem edg_good_of_valid (H : EdgeGroupHyp x y C zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (hnew : EdgeNewG y C U pm)
    (hpromo : EdgePromoG y C Δ Dil (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) pm) :
    EdgeGood y C Δ Dil zf U := by
  have hk := edg_slot_kind hn hnB hnew hpromo
  refine ⟨fun sl sl' hy => ?_, fun sl hu => ?_⟩
  · rcases hk sl with ⟨j, hj, rfl⟩ | ⟨hu, j, hpm, hyj, -, -⟩ | ⟨hf, hnU⟩
    · rcases hk sl' with ⟨j', hj', rfl⟩ | ⟨hu', j', hpm', hyj', -, -⟩ | ⟨hf', hnU'⟩
      · exact H.hx (((H.hSh j hj).symm.trans hy).trans (H.hSh j' hj'))
      · exact absurd (((H.hSh j hj).symm.trans hy).trans hyj') (H.hne _ j')
      · have hU' : (y sl' : ℕ) ∈ U := by
          rw [← hy, H.hSh j hj]
          exact H.hxU _
        exact absurd hU' hnU'
    · rcases hk sl' with ⟨j', hj', rfl⟩ | ⟨hu', j', hpm', hyj', -, -⟩ | ⟨hf', hnU'⟩
      · exact absurd (((H.hSh j' hj').symm.trans hy.symm).trans hyj) (H.hne _ j)
      · have hjj : j = j' := H.hz (hyj.symm.trans (hy.trans hyj'))
        rw [← hjj] at hpm'
        exact ((hpromo sl _ hpm).2.1 sl' hpm').symm
      · have hU' : (y sl' : ℕ) ∈ U := by
          rw [← hy, hyj]
          exact H.hzU j
        exact absurd hU' hnU'
    · rcases hk sl' with ⟨j', hj', rfl⟩ | ⟨hu', j', hpm', hyj', -, -⟩ | ⟨hf', hnU'⟩
      · have hU' : (y sl : ℕ) ∈ U := by
          rw [hy, H.hSh j' hj']
          exact H.hxU _
        exact absurd hU' hnU
      · have hU' : (y sl : ℕ) ∈ U := by
          rw [hy, hyj']
          exact H.hzU j'
        exact absurd hU' hnU
      · exact hnew.1 sl sl' hf hf' hy
  · rcases hk sl with ⟨j, hj, rfl⟩ | ⟨-, j, -, hyj, hsh, hdv⟩ | ⟨-, hnU⟩
    · exact absurd hu hj
    · exact Or.inl ⟨j, hyj.symm, hsh, hdv⟩
    · exact Or.inr hnU

end Valid

/-! ### The promotions are determined by the target labels -/

open _root_.Classical in
/-- **The promotions which the target labels determine**: an unshared target slot whose label is
the prime of a pending particle receives that particle. -/
def edgPromo {n : ℕ} (hnB : n ≤ Bc) (C : Finset (Fin J))
    (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (zf : Fin n → Particle 𝒢 g) (sl : Slot J ℓ) :
    Option (Fin Bc) :=
  if h : Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl then
    some (Fin.castLE hnB (_root_.Classical.choose h.2))
  else none

section Promo

variable {n : ℕ} (hnB : n ≤ Bc) (C : Finset (Fin J)) (y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
  (zf : Fin n → Particle 𝒢 g)

theorem edgPromo_some (hz : Function.Injective fun j : Fin n => (zf j).1) (sl : Slot J ℓ)
    (j : Fin n) (hu : Unshared C sl) (hj : (zf j).1 = y sl) :
    edgPromo hnB C y zf sl = some (Fin.castLE hnB j) := by
  have h : Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl := ⟨hu, j, hj⟩
  have hc : _root_.Classical.choose h.2 = j :=
    hz ((_root_.Classical.choose_spec h.2).trans hj.symm)
  unfold edgPromo
  rw [dif_pos h, hc]

theorem edgPromo_none (sl : Slot J ℓ)
    (h : ¬(Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl)) :
    edgPromo hnB C y zf sl = none := by
  unfold edgPromo
  exact dif_neg h

theorem edgPromo_eq_some_iff (hz : Function.Injective fun j : Fin n => (zf j).1)
    (sl : Slot J ℓ) (j' : Fin Bc) :
    edgPromo hnB C y zf sl = some j' ↔
      Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl ∧ j' = Fin.castLE hnB j := by
  constructor
  · intro h
    by_cases hc : Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl
    · obtain ⟨hu, j, hj⟩ := hc
      rw [edgPromo_some hnB C y zf hz sl j hu hj] at h
      exact ⟨hu, j, hj, (Option.some.inj h).symm⟩
    · rw [edgPromo_none hnB C y zf sl hc] at h
      cases h
  · rintro ⟨hu, j, hj, rfl⟩
    exact edgPromo_some hnB C y zf hz sl j hu hj

theorem edgPromo_ne_none_iff (hz : Function.Injective fun j : Fin n => (zf j).1)
    (sl : Slot J ℓ) :
    edgPromo hnB C y zf sl ≠ none ↔ Unshared C sl ∧ ∃ j : Fin n, (zf j).1 = y sl := by
  constructor
  · intro h
    by_contra hc
    exact h (edgPromo_none hnB C y zf sl hc)
  · rintro ⟨hu, j, hj⟩
    rw [edgPromo_some hnB C y zf hz sl j hu hj]
    exact Option.some_ne_none _

theorem edgPromo_fresh_iff (hz : Function.Injective fun j : Fin n => (zf j).1)
    (sl : Slot J ℓ) :
    EdgeFreshG C (edgPromo hnB C y zf) sl ↔ Unshared C sl ∧ ¬∃ j : Fin n, (zf j).1 = y sl := by
  constructor
  · rintro ⟨hu, hnone⟩
    refine ⟨hu, ?_⟩
    rintro ⟨j, hj⟩
    exact Option.some_ne_none _ ((edgPromo_some hnB C y zf hz sl j hu hj).symm.trans hnone)
  · rintro ⟨hu, hno⟩
    exact ⟨hu, edgPromo_none hnB C y zf sl fun h => hno h.2⟩

/-- The old particle with index `j` is promoted iff its prime is the label of an unshared target
slot. -/
theorem edgPromo_exists_iff (hz : Function.Injective fun j : Fin n => (zf j).1) (j : Fin n) :
    (∃ sl, edgPromo hnB C y zf sl = some (Fin.castLE hnB j)) ↔
      ∃ sl, Unshared C sl ∧ y sl = (zf j).1 := by
  constructor
  · rintro ⟨sl, h⟩
    obtain ⟨hu, j₂, hj₂, hcast⟩ := (edgPromo_eq_some_iff hnB C y zf hz sl _).mp h
    have hjj : j = j₂ := Fin.castLE_injective hnB hcast
    rw [← hjj] at hj₂
    exact ⟨sl, hu, hj₂.symm⟩
  · rintro ⟨sl, hu, hy⟩
    exact ⟨sl, edgPromo_some hnB C y zf hz sl j hu hy.symm⟩

end Promo

section Unique

variable {x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}} {C : Finset (Fin J)} {n : ℕ}
  {zf : Fin n → Particle 𝒢 g} {U : Finset ℕ} {Δ : ℤ} {Dil : ℕ}

/-- **Admissible promotions with new fresh births are the promotions which the target labels
determine**: "the index of the unique pending particle with the label of the target slot". -/
theorem edg_promo_unique (H : EdgeGroupHyp x y C zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    {pm : Slot J ℓ → Option (Fin Bc)} (hnew : EdgeNewG y C U pm)
    (hpromo : EdgePromoG y C Δ Dil (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) pm) :
    pm = edgPromo hnB C y zf := by
  funext sl
  rcases edg_slot_kind hn hnB hnew hpromo sl with
    ⟨j, hj, rfl⟩ | ⟨hu, j, hpm, hyj, -, -⟩ | ⟨hf, hnU⟩
  · have h1 : pm (Sum.inl j) = none := by
      obtain ⟨o, ho⟩ : ∃ o, pm (Sum.inl j) = o := ⟨_, rfl⟩
      cases o with
      | none => exact ho
      | some j' => exact absurd (hpromo _ j' ho).1 hj
    rw [h1]
    exact (edgPromo_none hnB C y zf (Sum.inl j) fun h => hj h.1).symm
  · rw [hpm]
    exact (edgPromo_some hnB C y zf H.hz sl j hu hyj.symm).symm
  · rw [hf.2]
    refine (edgPromo_none hnB C y zf sl fun h => ?_).symm
    obtain ⟨j, hj⟩ := h.2
    have hU' : (y sl : ℕ) ∈ U := by
      rw [← hj]
      exact H.hzU j
    exact hnU hU'

/-- **If the target list is compatible with the source state, the promotions which the target
labels determine are admissible and their fresh births are new.** -/
theorem edgPromo_valid (H : EdgeGroupHyp x y C zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (hgood : EdgeGood y C Δ Dil zf U) :
    EdgeNewG y C U (edgPromo hnB C y zf) ∧
      EdgePromoG y C Δ Dil (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) (edgPromo hnB C y zf) := by
  refine ⟨⟨fun sl sl' _ _ hy => hgood.1 hy, fun sl hf => ?_⟩, fun sl j' hpm => ?_⟩
  · rcases hgood.2 sl hf.1 with ⟨j, hj, -, -⟩ | hnU
    · exact absurd ((edgPromo_some hnB C y zf H.hz sl j hf.1 hj).symm.trans hf.2)
        (Option.some_ne_none _)
    · exact hnU
  · obtain ⟨hu, j, hj, rfl⟩ := (edgPromo_eq_some_iff hnB C y zf H.hz sl j').mp hpm
    have hprom : (shiftParticle Δ (zf j)).2 = 0 ∧ ¬(((zf j).1 : ℕ) ∣ Dil) := by
      rcases hgood.2 sl hu with ⟨j₃, hj₃, hsh, hdv⟩ | hnU
      · have hjj : j₃ = j := H.hz (hj₃.trans hj.symm)
        rw [hjj] at hsh hdv
        exact ⟨hsh, hdv⟩
      · have hU' : (y sl : ℕ) ∈ U := by
          rw [← hj]
          exact H.hzU j
        exact absurd hU' hnU
    refine ⟨hu, fun sl' hpm' => ?_, zf j, edg_memAt_castLE hn hnB zf j, hprom.1, hprom.2,
      hj.symm⟩
    obtain ⟨-, j₂, hj₂, hcast⟩ := (edgPromo_eq_some_iff hnB C y zf H.hz sl' _).mp hpm'
    have hjj : j = j₂ := Fin.castLE_injective hnB hcast
    rw [← hjj] at hj₂
    exact hgood.1 (hj₂.symm.trans hj)

end Unique

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

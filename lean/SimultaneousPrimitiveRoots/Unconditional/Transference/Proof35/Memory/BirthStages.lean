module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.HistorySkeleton
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The distinct-birth rule, operation by operation

Source: `verification/stage7-sources/S-02.tex`, lines 516–521 (`[S-02:0516–0521]`): "all prime
values assigned at different births are distinct. Births comprise initial active slots, fresh
active target slots, and ghost births. This is a global rule, even if two births occur far apart."

The birth addresses are ordered by the operation to which they belong (`birthStage`): the initial
list, then `G_0, ℰ_0, G_1, …, ℰ_{N-1}, G_N`. The global rule holds if and only if the births of
every operation are distinct and differ from all the births of the earlier operations
(`distinct_iff_staged`). For the history of a skeleton and a decoration this is

* the initial labels are pairwise distinct;
* the births of `G_i` are new with respect to `Skel.bornAt d i` (`NewBirths`);
* the fresh births of `ℰ_i` are new with respect to `Skel.bornAt d i` and the births of `G_i`

(`Skel.distinct_iff_newBirths`), where `Skel.bornAt d i` is the set of the values born before the
visit `i` (`Skel.mem_bornAt`). These are the conditions of the recursion `Skel.fut`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Sets of births and stages -/

theorem mem_birthSet {ι : Type} [Fintype ι] (β : ι → Option ℕ) (z : ℕ) :
    z ∈ birthSet β ↔ ∃ a, β a = some z := by
  unfold birthSet
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, _, ha⟩
    refine ⟨a, ?_⟩
    cases hβ : β a with
    | none =>
      rw [hβ] at ha
      exact absurd ha (Finset.notMem_empty z)
    | some w =>
      rw [hβ] at ha
      rw [Finset.mem_singleton.mp ha]
  · rintro ⟨a, ha⟩
    refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [ha]
    exact Finset.mem_singleton_self z

/-- **The distinct-birth rule by stages**: if the addresses are ordered by a stage `τ`, the
performed births are pairwise distinct if and only if every performed birth differs from the other
births of its stage and from all births of the earlier stages. -/
theorem distinct_iff_staged {A : Type} (β : A → Option ℕ) (τ : A → ℕ) :
    Graph.PerformedBirthsDistinct β ↔
      ∀ a z, β a = some z →
        (∀ b, τ b = τ a → β b = some z → b = a) ∧ ∀ b, τ b < τ a → β b ≠ some z := by
  constructor
  · intro h a z ha
    refine ⟨fun b _ hb => h b a z hb ha, fun b hlt hb => ?_⟩
    have hba : b = a := h b a z hb ha
    rw [hba] at hlt
    exact Nat.lt_irrefl _ hlt
  · intro h a b z ha hb
    rcases Nat.lt_trichotomy (τ a) (τ b) with hlt | heq | hgt
    · exact absurd ha ((h b z hb).2 a hlt)
    · exact (h b z hb).1 a heq ha
    · exact absurd hb ((h a z ha).2 b hgt)

/-- **The stage of a birth address**: `0` for the initial slots, `2i + 1` for the ghost births of
the visit `i`, `2i + 2` for the fresh births of the edge `i` (the order of the operations
`G_0, ℰ_0, G_1, …`). -/
def birthStage (B : Type) (J ℓ Bc n : ℕ) : BirthAddr B J ℓ Bc n → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl a) => 2 * a.1.val + 2
  | Sum.inr (Sum.inr a) => 2 * a.1.val + 1

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N] {D : MemData 𝒢 J ℓ N} {Bc : ℕ}

/-! ### The primes born before a visit -/

/-- **The set of the values born before the visit `i`** (before the visit operation `G_i`) in the
histories with skeleton `sk` and decoration `d`: the initial labels, and the births of the
operations `G_0, ℰ_0, …, G_{i-1}, ℰ_{i-1}`. -/
def Skel.bornAt (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) : ℕ → Finset ℕ
  | 0 => Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)
  | i + 1 =>
    if hi : i < D.n then
      sk.bornAt d i ∪ birthSet (ghostAddrBirth (d.ghost (Fin.castSucc ⟨i, hi⟩))) ∪
        birthSet (edgeAddrBirth (sk.edgeChoice ⟨i, hi⟩ (d.store ⟨i, hi⟩) (d.promo ⟨i, hi⟩)))
    else sk.bornAt d i

omit [Fintype S] [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem Skel.bornAt_succ (sk : Skel D) (d : Deco 𝒢 J ℓ Bc D.n) (i : ℕ) (hi : i < D.n) :
    sk.bornAt d (i + 1) =
      sk.bornAt d i ∪ birthSet (ghostAddrBirth (d.ghost (Fin.castSucc ⟨i, hi⟩))) ∪
        birthSet (edgeAddrBirth (sk.edgeChoice ⟨i, hi⟩ (d.store ⟨i, hi⟩) (d.promo ⟨i, hi⟩))) := by
  rw [Skel.bornAt]
  exact dif_pos hi

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **A value is born before the visit `i` if and only if it is the birth of an address of stage
smaller than `2i + 1`.** -/
theorem Skel.mem_bornAt (sk : Skel D) (y : ResVec (smallPrimes 𝒢)) (d : Deco 𝒢 J ℓ Bc D.n) :
    ∀ i : ℕ, i ≤ D.n → ∀ z : ℕ, z ∈ sk.bornAt d i ↔
      ∃ b : BirthAddr B J ℓ Bc D.n,
        birthStage B J ℓ Bc D.n b < 2 * i + 1 ∧ (sk.hist y d).birth b = some z := by
  intro i
  induction i with
  | zero =>
    intro _ z
    rw [Skel.bornAt, Finset.mem_image]
    constructor
    · rintro ⟨a, _, ha⟩
      exact ⟨Sum.inl a, Nat.zero_lt_one, congrArg some ha⟩
    · rintro ⟨b, hst, hb⟩
      rcases b with a | ⟨k, g, sl⟩ | ⟨k, g, j⟩
      · exact ⟨a, Finset.mem_univ a, Option.some.inj hb⟩
      · have hst' : 2 * k.val + 2 < 2 * 0 + 1 := hst
        omega
      · have hst' : 2 * k.val + 1 < 2 * 0 + 1 := hst
        omega
  | succ i ih =>
    intro hi z
    have hi' : i < D.n := hi
    have ih' := ih (Nat.le_of_lt hi') z
    rw [sk.bornAt_succ d i hi', Finset.mem_union, Finset.mem_union, mem_birthSet, mem_birthSet]
    constructor
    · rintro ((h1 | ⟨a, ha⟩) | ⟨a, ha⟩)
      · obtain ⟨b, hst, hb⟩ := ih'.mp h1
        exact ⟨b, by omega, hb⟩
      · refine ⟨Sum.inr (Sum.inr (Fin.castSucc ⟨i, hi'⟩, a.1, a.2)), ?_, ha⟩
        show 2 * i + 1 < 2 * (i + 1) + 1
        omega
      · refine ⟨Sum.inr (Sum.inl (⟨i, hi'⟩, a.1, a.2)), ?_, ha⟩
        show 2 * i + 2 < 2 * (i + 1) + 1
        omega
    · rintro ⟨b, hst, hb⟩
      rcases b with a | ⟨k, g, sl⟩ | ⟨k, g, j⟩
      · exact Or.inl (Or.inl (ih'.mpr ⟨Sum.inl a, Nat.succ_pos _, hb⟩))
      · have hst' : 2 * k.val + 2 < 2 * (i + 1) + 1 := hst
        by_cases hk : k.val < i
        · refine Or.inl (Or.inl (ih'.mpr ⟨Sum.inr (Sum.inl (k, g, sl)), ?_, hb⟩))
          show 2 * k.val + 2 < 2 * i + 1
          omega
        · have hk' : k = ⟨i, hi'⟩ := Fin.ext (show k.val = i by omega)
          subst hk'
          exact Or.inr ⟨(g, sl), hb⟩
      · have hst' : 2 * k.val + 1 < 2 * (i + 1) + 1 := hst
        by_cases hk : k.val < i
        · refine Or.inl (Or.inl (ih'.mpr ⟨Sum.inr (Sum.inr (k, g, j)), ?_, hb⟩))
          show 2 * k.val + 1 < 2 * i + 1
          omega
        · have hk' : k = Fin.castSucc ⟨i, hi'⟩ := Fin.ext (show k.val = i by omega)
          subst hk'
          exact Or.inl (Or.inr ⟨(g, j), hb⟩)

/-! ### The global rule and the rule of each operation -/

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **The distinct-birth rule of a history is the conjunction of the rules of its operations**
[S-02:0516–0521]: the initial labels are pairwise distinct; the births of every visit operation
`G_i` are new with respect to the values born before the visit `i`; the fresh births of every
edge `ℰ_i` are new with respect to those values and the births of `G_i`. -/
theorem Skel.distinct_iff_newBirths (sk : Skel D) (y : ResVec (smallPrimes 𝒢))
    (d : Deco 𝒢 J ℓ Bc D.n) :
    Graph.PerformedBirthsDistinct (sk.hist y d).birth ↔
      Function.Injective (fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) ∧
        (∀ i : Fin (D.n + 1), NewBirths (ghostAddrBirth (d.ghost i)) (sk.bornAt d i.val)) ∧
        ∀ i : Fin D.n, NewBirths (edgeAddrBirth (sk.edgeChoice i (d.store i) (d.promo i)))
          (sk.bornAt d i.val ∪ birthSet (ghostAddrBirth (d.ghost i.castSucc))) := by
  rw [distinct_iff_staged _ (birthStage B J ℓ Bc D.n)]
  constructor
  · intro h
    refine ⟨fun a₁ a₂ h12 => ?_, fun i => ⟨fun a a' z ha ha' => ?_, fun a z ha hz => ?_⟩,
      fun i => ⟨fun a a' z ha ha' => ?_, fun a z ha hz => ?_⟩⟩
    · -- the initial labels
      have h1 := (h (Sum.inl a₂) (sk.xb₀ a₂.1 a₂.2 : ℕ) rfl).1 (Sum.inl a₁) rfl
        (congrArg some h12)
      exact Sum.inl.inj h1
    · -- the births of `G_i` are distinct
      have h1 := (h (Sum.inr (Sum.inr (i, a'.1, a'.2))) z ha').1
        (Sum.inr (Sum.inr (i, a.1, a.2))) rfl ha
      have h2 : (i, a.1, a.2) = (i, a'.1, a'.2) := Sum.inr.inj (Sum.inr.inj h1)
      exact Prod.ext (congrArg (fun t => t.2.1) h2) (congrArg (fun t => t.2.2) h2)
    · -- the births of `G_i` were not born before
      obtain ⟨b, hst, hb⟩ := (sk.mem_bornAt y d i.val (Nat.le_of_lt_succ i.isLt) z).mp hz
      exact (h (Sum.inr (Sum.inr (i, a.1, a.2))) z ha).2 b hst hb
    · -- the fresh births of `ℰ_i` are distinct
      have h1 := (h (Sum.inr (Sum.inl (i, a'.1, a'.2))) z ha').1
        (Sum.inr (Sum.inl (i, a.1, a.2))) rfl ha
      have h2 : (i, a.1, a.2) = (i, a'.1, a'.2) := Sum.inl.inj (Sum.inr.inj h1)
      exact Prod.ext (congrArg (fun t => t.2.1) h2) (congrArg (fun t => t.2.2) h2)
    · -- the fresh births of `ℰ_i` were not born before
      rcases Finset.mem_union.mp hz with hz1 | hz2
      · obtain ⟨b, hst, hb⟩ := (sk.mem_bornAt y d i.val (Nat.le_of_lt i.isLt) z).mp hz1
        refine (h (Sum.inr (Sum.inl (i, a.1, a.2))) z ha).2 b ?_ hb
        show birthStage B J ℓ Bc D.n b < 2 * i.val + 2
        omega
      · obtain ⟨a', ha'⟩ := (mem_birthSet _ z).mp hz2
        refine (h (Sum.inr (Sum.inl (i, a.1, a.2))) z ha).2
          (Sum.inr (Sum.inr (i.castSucc, a'.1, a'.2))) ?_ ha'
        show 2 * i.val + 1 < 2 * i.val + 2
        omega
  · rintro ⟨hinj, hG, hE⟩ a z ha
    rcases a with a | ⟨i, g, sl⟩ | ⟨i, g, j⟩
    · -- an initial slot
      refine ⟨fun b hst hb => ?_, fun b hst _ => absurd hst (Nat.not_lt_zero _)⟩
      rcases b with b | ⟨k, g', sl'⟩ | ⟨k, g', j'⟩
      · have h1 : (sk.xb₀ b.1 b.2 : ℕ) = (sk.xb₀ a.1 a.2 : ℕ) :=
          (Option.some.inj hb).trans (Option.some.inj ha).symm
        exact congrArg Sum.inl (hinj h1)
      · have hst' : 2 * k.val + 2 = 0 := hst
        omega
      · have hst' : 2 * k.val + 1 = 0 := hst
        omega
    · -- a fresh birth of the edge `i`
      refine ⟨fun b hst hb => ?_, fun b hst hb => ?_⟩
      · rcases b with b | ⟨k, g', sl'⟩ | ⟨k, g', j'⟩
        · have hst' : 0 = 2 * i.val + 2 := hst
          omega
        · have hst' : 2 * k.val + 2 = 2 * i.val + 2 := hst
          have hk : k = i := Fin.ext (by omega)
          rw [hk] at hb
          have h1 : ((g', sl') : B × Slot J ℓ) = (g, sl) := (hE i).1 (g', sl') (g, sl) z hb ha
          rw [hk, (Prod.mk.inj h1).1, (Prod.mk.inj h1).2]
        · have hst' : 2 * k.val + 1 = 2 * i.val + 2 := hst
          omega
      · have hst' : birthStage B J ℓ Bc D.n b < 2 * i.val + 2 := hst
        refine (hE i).2 (g, sl) z ha (Finset.mem_union.mpr ?_)
        by_cases hlt : birthStage B J ℓ Bc D.n b < 2 * i.val + 1
        · exact Or.inl ((sk.mem_bornAt y d i.val (Nat.le_of_lt i.isLt) z).mpr ⟨b, hlt, hb⟩)
        · refine Or.inr ((mem_birthSet _ z).mpr ?_)
          rcases b with b | ⟨k, g', sl'⟩ | ⟨k, g', j'⟩
          · have h0 : (0 : ℕ) < 2 * i.val + 1 := Nat.succ_pos _
            exact absurd h0 hlt
          · have h1 : 2 * k.val + 2 < 2 * i.val + 2 := hst'
            have h2 : ¬2 * k.val + 2 < 2 * i.val + 1 := hlt
            omega
          · have h1 : 2 * k.val + 1 < 2 * i.val + 2 := hst'
            have h2 : ¬2 * k.val + 1 < 2 * i.val + 1 := hlt
            have hk : k = i.castSucc := Fin.ext (show k.val = i.val by omega)
            subst hk
            exact ⟨(g', j'), hb⟩
    · -- a ghost birth of the visit `i`
      refine ⟨fun b hst hb => ?_, fun b hst hb => ?_⟩
      · rcases b with b | ⟨k, g', sl'⟩ | ⟨k, g', j'⟩
        · have hst' : 0 = 2 * i.val + 1 := hst
          omega
        · have hst' : 2 * k.val + 2 = 2 * i.val + 1 := hst
          omega
        · have hst' : 2 * k.val + 1 = 2 * i.val + 1 := hst
          have hk : k = i := Fin.ext (by omega)
          rw [hk] at hb
          have h1 : ((g', j') : B × Fin Bc) = (g, j) := (hG i).1 (g', j') (g, j) z hb ha
          rw [hk, (Prod.mk.inj h1).1, (Prod.mk.inj h1).2]
      · exact (hG i).2 (g, j) z ha
          ((sk.mem_bornAt y d i.val (Nat.le_of_lt_succ i.isLt) z).mpr ⟨b, hst, hb⟩)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

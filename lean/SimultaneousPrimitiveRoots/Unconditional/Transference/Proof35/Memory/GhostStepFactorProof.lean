module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostGroupSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (M2) A visit operation acts prime by prime

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 and 569–581
(`[S-02:0456–0475, 0569–0581]`), (eq:ghost-row).

`ghostStepFactor` proves the statement `GhostStepFactor` of `Memory/Statements.lean`: on a state in
which every big prime occurs at most once, the sum over the choices of the visit operation `G_i`
with new births, of the coefficient times the product of the values `v` at the new state, is the
product of the values `ghostStepVals D i v` at the old state.

The proof:

* `PrimeVals.eval_eq_prod_evalL` — the product of the values is a product over the big groups;
* `ghStep_newBirths_iff` — for pairwise disjoint big groups, the births of a choice are new if and
  only if the batch of every group consists of pairwise distinct primes which were not born;
* `ghostChoiceTerm_eq` — the term of a choice is the product over the groups of the terms `ghostT`
  of its local choices: the truncations are not active (the pending primes and the new primes of
  a group are distinct primes of the group, and `Bc ≥ #{big primes}`), and the new state is again
  a state in which every big prime occurs at most once;
* `ghostChoice_sum` — the sum over the choices is the product over the groups of the sums over the
  local choices (`Fintype.prod_sum`), which are computed in `GhostGroupSum.lean` (`ghostT_sum`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### The product of the values, group by group -/

/-- **The product of the values of the big primes is a product over the big groups** of the
factors `PrimeVals.evalL`. -/
theorem PrimeVals.eval_eq_prod_evalL [Fintype B] (v : PrimeVals 𝒢) (xb : LabelList 𝒢.big J ℓ)
    (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) :
    v.eval xb mem U = ∏ g, v.evalL g (xb g) (List.ofFn (mem g).2) U := by
  have hR : ∏ g, v.evalL g (xb g) (List.ofFn (mem g).2) U =
      (∏ g, ∏ sl : Slot J ℓ, v.act g (xb g sl)) *
          (∏ g, ((List.ofFn (mem g).2).map (v.pend g)).prod) *
        ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, v.thirdL g (xb g) (List.ofFn (mem g).2) U p := by
    unfold PrimeVals.evalL
    exact Eq.trans Finset.prod_mul_distrib
      (congrArg (fun t : ℝ => t * ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g},
        v.thirdL g (xb g) (List.ofFn (mem g).2) U p) Finset.prod_mul_distrib)
  refine Eq.trans ?_ hR.symm
  unfold PrimeVals.eval
  refine congrArg₂ (fun a b : ℝ => a * b) (congrArg₂ (fun a b : ℝ => a * b) rfl ?_) ?_
  · exact Finset.prod_congr rfl fun g _ => (ghStep_prod_map_ofFn (mem g).2 (v.pend g)).symm
  · refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun p _ => ?_
    unfold PrimeVals.thirdL
    exact bigRes_ite_congr Iff.rfl
      (bigRes_ite_congr (or_congr Iff.rfl (ghStep_exists_ofFn (mem g).2 p).symm) rfl rfl) rfl

/-! ### The births of a choice -/

/-- A ghost birth at an address: the entry of the batch of the group at the index of the
address. -/
theorem ghStep_addrBirth_eq_some (c : GhostChoice 𝒢 Bc) (a : B × Fin Bc) (z : ℕ) :
    ghostAddrBirth c a = some z ↔
      ∃ hj : a.2.val < (c a.1).2.1.val,
        (((c a.1).2.2 ⟨a.2.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big a.1}) : ℕ) = z := by
  constructor
  · intro h
    by_cases hj : a.2.val < (c a.1).2.1.val
    · have h1 : ghostAddrBirth c a =
          some (((c a.1).2.2 ⟨a.2.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big a.1}) : ℕ) := by
        unfold ghostAddrBirth
        exact dif_pos hj
      exact ⟨hj, Option.some.inj (h1.symm.trans h)⟩
    · have h1 : ghostAddrBirth c a = none := by
        unfold ghostAddrBirth
        exact dif_neg hj
      rw [h1] at h
      cases h
  · rintro ⟨hj, hz⟩
    have h1 : ghostAddrBirth c a =
        some (((c a.1).2.2 ⟨a.2.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big a.1}) : ℕ) := by
      unfold ghostAddrBirth
      exact dif_pos hj
    rw [h1, hz]

/-- The set of the values of an assignment of births to addresses. -/
theorem ghStep_mem_birthSet {ι : Type} [Fintype ι] (β : ι → Option ℕ) (z : ℕ) :
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

/-- The primes of the batch of a group are births of the choice. -/
theorem batchSet_subset_birthSet [Fintype B] (c : GhostChoice 𝒢 Bc) (g : B) {z : ℕ}
    (hz : z ∈ batchSet (c g).2) : z ∈ birthSet (ghostAddrBirth c) := by
  obtain ⟨j, hj⟩ := (mem_batchSet (c g).2 z).mp hz
  have hlt : j.val < Bc := Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ (c g).2.1.isLt)
  exact (ghStep_mem_birthSet _ z).mpr
    ⟨(g, ⟨j.val, hlt⟩), (ghStep_addrBirth_eq_some c (g, ⟨j.val, hlt⟩) z).mpr ⟨j.isLt, hj⟩⟩

/-- For pairwise disjoint big groups, a birth of the choice which is a prime of the group `g` is
a prime of the batch of `g`. -/
theorem mem_batchSet_of_mem_birthSet [Fintype B]
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (c : GhostChoice 𝒢 Bc) (g : B)
    {z : ℕ} (hzg : z ∈ 𝒢.big g) (hz : z ∈ birthSet (ghostAddrBirth c)) :
    z ∈ batchSet (c g).2 := by
  obtain ⟨a, ha⟩ := (ghStep_mem_birthSet _ z).mp hz
  obtain ⟨hj, hzz⟩ := (ghStep_addrBirth_eq_some c a z).mp ha
  have hmem : z ∈ 𝒢.big a.1 := by
    rw [← hzz]
    exact ((c a.1).2.2 ⟨a.2.val, hj⟩).2
  have hga : a.1 = g := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj a.1 g hne) hmem hzg
  subst hga
  exact (mem_batchSet (c a.1).2 z).mpr ⟨⟨a.2.val, hj⟩, hzz⟩

/-- The births of a choice are big primes. -/
theorem ghStep_birthSet_subset [Fintype B] (c : GhostChoice 𝒢 Bc) :
    birthSet (ghostAddrBirth c) ⊆ bigPrimes 𝒢 := by
  intro z hz
  obtain ⟨a, ha⟩ := (ghStep_mem_birthSet _ z).mp hz
  obtain ⟨hj, hzz⟩ := (ghStep_addrBirth_eq_some c a z).mp ha
  rw [← hzz]
  exact mem_bigPrimes.mpr ⟨a.1, ((c a.1).2.2 ⟨a.2.val, hj⟩).2⟩

/-- **The births of a choice are new, group by group**: for pairwise disjoint big groups, the
performed births of a choice are pairwise distinct and were not born if and only if the batch of
every group consists of pairwise distinct primes which were not born. -/
theorem ghStep_newBirths_iff (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (c : GhostChoice 𝒢 Bc) (U : Finset ℕ) :
    NewBirths (ghostAddrBirth c) U ↔ ∀ g, BatchNew U (c g).2 := by
  constructor
  · rintro ⟨hd, hU⟩ g
    have hlt : ∀ j : Fin (c g).2.1.val, j.val < Bc := fun j =>
      Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ (c g).2.1.isLt)
    have hb : ∀ j : Fin (c g).2.1.val, ghostAddrBirth c (g, ⟨j.val, hlt j⟩) =
        some (((c g).2.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) := fun j =>
      (ghStep_addrBirth_eq_some c (g, ⟨j.val, hlt j⟩) _).mpr ⟨j.isLt, rfl⟩
    refine ⟨fun j k hjk => ?_, fun j => hU _ _ (hb j)⟩
    have hk : ghostAddrBirth c (g, ⟨k.val, hlt k⟩) =
        some (((c g).2.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) :=
      (hb k).trans (congrArg (fun q : {p : ℕ // p ∈ 𝒢.big g} => some (q : ℕ)) hjk.symm)
    have h1 : ((g, ⟨j.val, hlt j⟩) : B × Fin Bc) = (g, ⟨k.val, hlt k⟩) :=
      hd _ _ _ (hb j) hk
    exact Fin.ext (congrArg (fun a : B × Fin Bc => a.2.val) h1)
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨g, k⟩ ⟨g', k'⟩ z ha ha'
      obtain ⟨hj, hz⟩ : ∃ hj : k.val < (c g).2.1.val,
          (((c g).2.2 ⟨k.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) = z :=
        (ghStep_addrBirth_eq_some c (g, k) z).mp ha
      obtain ⟨hj', hz'⟩ : ∃ hj : k'.val < (c g').2.1.val,
          (((c g').2.2 ⟨k'.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big g'}) : ℕ) = z :=
        (ghStep_addrBirth_eq_some c (g', k') z).mp ha'
      have hmem : z ∈ 𝒢.big g := by
        rw [← hz]
        exact ((c g).2.2 ⟨k.val, hj⟩).2
      have hmem' : z ∈ 𝒢.big g' := by
        rw [← hz']
        exact ((c g').2.2 ⟨k'.val, hj'⟩).2
      have hg : g = g' := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj g g' hne) hmem hmem'
      subst hg
      have h2 : (⟨k.val, hj⟩ : Fin (c g).2.1.val) = ⟨k'.val, hj'⟩ :=
        (h g).1 (Subtype.ext (hz.trans hz'.symm))
      have h3 : k.val = k'.val := congrArg (fun q : Fin (c g).2.1.val => q.val) h2
      exact congrArg (Prod.mk g) (Fin.ext h3)
    · intro a z ha
      obtain ⟨hj, hz⟩ := (ghStep_addrBirth_eq_some c a z).mp ha
      rw [← hz]
      exact (h a.1).2 ⟨a.2.val, hj⟩

/-! ### The truncations are not active -/

/-- A big group is a set of big primes. -/
theorem ghStep_card_big_le [Fintype B] (𝒢 : GroupFamily S B) (g : B) :
    (𝒢.big g).card ≤ (bigPrimes 𝒢).card :=
  Finset.card_le_card fun _ hp => mem_bigPrimes.mpr ⟨g, hp⟩

/-- The number of the big primes, for pairwise disjoint big groups. -/
theorem ghStep_sum_card_big [Fintype B]
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) :
    ∑ g, (𝒢.big g).card = (bigPrimes 𝒢).card := by
  have h : (Finset.univ.biUnion 𝒢.big).card = ∑ g, (𝒢.big g).card :=
    Finset.card_biUnion fun g _ g' _ hne => hdisj g g' hne
  exact h.symm

/-- The new memory of a visit operation with new births, for a local choice of a group in which
every prime occurs at most once (`ghostNew_facts`, for the pair of the terminated set and the
batch). -/
theorem ghostNew_facts' {g : B} (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ)
    (z : Mem 𝒢 Bc g) (cg : Finset (Fin Bc) × Batch 𝒢 Bc g)
    (hinj : Function.Injective fun j : Fin z.1.val => (z.2 j).1)
    (hne : ∀ sl (j : Fin z.1.val), xbg sl ≠ (z.2 j).1)
    (hU : ∀ j : Fin z.1.val, ((z.2 j).1 : ℕ) ∈ U) (hxU : ∀ sl, (xbg sl : ℕ) ∈ U)
    (hcard : (𝒢.big g).card ≤ Bc) (hv : GhostValid z cg.1) (hgood : BatchNew U cg.2) :
    ghostNewSize z cg ≤ (𝒢.big g).card ∧ z.1.val ≤ (𝒢.big g).card ∧
      (Function.Injective fun j : Fin (ghostNewMem z cg).1.val => ((ghostNewMem z cg).2 j).1) ∧
      (∀ sl (j : Fin (ghostNewMem z cg).1.val), xbg sl ≠ ((ghostNewMem z cg).2 j).1) ∧
      ∀ j : Fin (ghostNewMem z cg).1.val,
        (((ghostNewMem z cg).2 j).1 : ℕ) ∈ U ∪ batchSet cg.2 := by
  obtain ⟨A, β⟩ := cg
  exact ghostNew_facts xbg U z A β hinj hne hU hxU hcard hv hgood

/-- The coefficient of a visit operation when the truncations are not active. -/
theorem ghStep_ghostCoef_eq_prod [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc)
    (h1 : memTotal s ≤ Bc) (h2 : (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc) :
    ghostCoef D i s c = ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) := by
  unfold ghostCoef
  exact if_pos ⟨h1, h2⟩

/-- The coefficient of a visit operation vanishes if in one group the terminated set is not a set
of pending zeros. -/
theorem ghStep_ghostCoef_eq_zero [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) (g : B)
    (h : ¬GhostValid (s.mem g) (c g).1) : ghostCoef D i s c = 0 := by
  have h0 : ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) = 0 := by
    unfold ghostCoefG
    exact if_neg h
  unfold ghostCoef
  by_cases hcut : memTotal s ≤ Bc ∧ (∑ g', ghostNewSize (s.mem g') (c g')) ≤ Bc
  · exact Eq.trans (if_pos hcut) (Finset.prod_eq_zero (Finset.mem_univ g) h0)
  · exact if_neg hcut

/-! ### The term of a choice -/

open _root_.Classical in
/-- **The term of a choice in the sum over the choices of a visit operation with new births**
(`Skel.ghostSum`), for a memory state `s`: zero unless the births of the choice are new; otherwise
the coefficient of the choice times the value of `Ψ` at the new memories and the enlarged set of
the primes born so far. -/
def ghostChoiceTerm [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (U : Finset ℕ) (c : GhostChoice 𝒢 Bc) : ℝ :=
  if NewBirths (ghostAddrBirth c) U then
    ghostCoef D i s c *
      Ψ (fun g => ghostNewMem (s.mem g) (c g)) (U ∪ birthSet (ghostAddrBirth c))
  else 0

/-- **The term of a choice is a product over the big groups** [S-02:0569–0581]: on a state in
which every big prime occurs at most once, for pairwise disjoint big groups and a cutoff
`Bc ≥ #{big primes}`, if `Ψ` is the product of the values `v` on such states, the term of a
choice is the product over the big groups of the terms `ghostT` of its local choices. -/
theorem ghostChoiceTerm_eq [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (hBc : (bigPrimes 𝒢).card ≤ Bc)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (v : PrimeVals 𝒢)
    (hΨ : ∀ mem U, MemConsistent s.xb mem U → Ψ mem U = v.eval s.xb mem U)
    (U : Finset ℕ) (hc : MemConsistent s.xb s.mem U) (c : GhostChoice 𝒢 Bc) :
    ghostChoiceTerm D i s Ψ U c = ∏ g, ghostT D i v g (s.xb g) (s.mem g) U (c g) := by
  obtain ⟨hxinj, hminj, hne, hxU, hmU, hUbig⟩ := hc
  by_cases hnew : NewBirths (ghostAddrBirth c) U
  · have eC : ghostChoiceTerm D i s Ψ U c =
        ghostCoef D i s c *
          Ψ (fun g => ghostNewMem (s.mem g) (c g)) (U ∪ birthSet (ghostAddrBirth c)) := by
      unfold ghostChoiceTerm
      exact if_pos hnew
    rw [eC]
    have hgood : ∀ g, BatchNew U (c g).2 := (ghStep_newBirths_iff hdisj c U).mp hnew
    have hT : ∀ g, ghostT D i v g (s.xb g) (s.mem g) U (c g) =
        ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) *
          v.evalL g (s.xb g) (List.ofFn (ghostNewMem (s.mem g) (c g)).2)
            (U ∪ batchSet (c g).2) := by
      intro g
      unfold ghostT
      exact if_pos (hgood g)
    by_cases hval : ∀ g, GhostValid (s.mem g) (c g).1
    · -- the truncations are not active
      have hcardg : ∀ g, (𝒢.big g).card ≤ Bc := fun g => (ghStep_card_big_le 𝒢 g).trans hBc
      have hf := fun g => ghostNew_facts' (s.xb g) U (s.mem g) (c g) (hminj g) (hne g) (hmU g)
        (hxU g) (hcardg g) (hval g) (hgood g)
      have hsum : ∑ g, (𝒢.big g).card ≤ Bc := (ghStep_sum_card_big hdisj).le.trans hBc
      have h1 : memTotal s ≤ Bc := by
        unfold memTotal
        exact (Finset.sum_le_sum fun g _ => (hf g).2.1).trans hsum
      have h2 : (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc :=
        (Finset.sum_le_sum fun g _ => (hf g).1).trans hsum
      -- in the new state every big prime occurs at most once
      have hcons : MemConsistent s.xb (fun g => ghostNewMem (s.mem g) (c g))
          (U ∪ birthSet (ghostAddrBirth c)) :=
        ⟨hxinj, fun g => (hf g).2.2.1, fun g => (hf g).2.2.2.1,
          fun g sl => Finset.mem_union_left _ (hxU g sl),
          fun g j => (Finset.mem_union.mp ((hf g).2.2.2.2 j)).elim
            (fun h => Finset.mem_union_left _ h)
            (fun h => Finset.mem_union_right _ (batchSet_subset_birthSet c g h)),
          Finset.union_subset hUbig (ghStep_birthSet_subset c)⟩
      -- the primes of a group born so far
      have hU' : ∀ g (p : {p : ℕ // p ∈ 𝒢.big g}),
          (p : ℕ) ∈ U ∪ birthSet (ghostAddrBirth c) ↔ (p : ℕ) ∈ U ∪ batchSet (c g).2 := by
        intro g p
        rw [Finset.mem_union, Finset.mem_union]
        exact or_congr Iff.rfl
          ⟨fun h => mem_batchSet_of_mem_birthSet hdisj c g p.2 h,
            fun h => batchSet_subset_birthSet c g h⟩
      rw [ghStep_ghostCoef_eq_prod D i s c h1 h2, hΨ _ _ hcons, PrimeVals.eval_eq_prod_evalL,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [hT g]
      exact congrArg (fun t => ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) * t)
        (v.evalL_congr_U g (s.xb g) _ (hU' g))
    · obtain ⟨g, hg⟩ : ∃ g, ¬GhostValid (s.mem g) (c g).1 := not_forall.mp hval
      rw [ghStep_ghostCoef_eq_zero D i s c g hg, zero_mul]
      exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ g)
        (ghostT_eq_zero_of_not_valid D i v g (s.xb g) (s.mem g) U (c g) hg))
  · have eC : ghostChoiceTerm D i s Ψ U c = 0 := by
      unfold ghostChoiceTerm
      exact if_neg hnew
    rw [eC]
    obtain ⟨g, hg⟩ : ∃ g, ¬BatchNew U (c g).2 :=
      not_forall.mp fun h => hnew ((ghStep_newBirths_iff hdisj c U).mpr h)
    have h0 : ghostT D i v g (s.xb g) (s.mem g) U (c g) = 0 := by
      unfold ghostT
      exact if_neg hg
    exact Eq.symm (Finset.prod_eq_zero (Finset.mem_univ g) h0)

/-- **The sum over the choices of a visit operation with new births** [S-02:0456–0475,
0569–0581], for a memory state `s` in which every big prime occurs at most once: it is the
product of the values `ghostStepVals D i v`. -/
theorem ghostChoice_sum [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (hBc : (bigPrimes 𝒢).card ≤ Bc)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (v : PrimeVals 𝒢)
    (hΨ : ∀ mem U, MemConsistent s.xb mem U → Ψ mem U = v.eval s.xb mem U)
    (U : Finset ℕ) (hc : MemConsistent s.xb s.mem U) :
    ∑ c : GhostChoice 𝒢 Bc, ghostChoiceTerm D i s Ψ U c =
      (ghostStepVals D i v).eval s.xb s.mem U := by
  have hcardg : ∀ g, (𝒢.big g).card ≤ Bc := fun g => (ghStep_card_big_le 𝒢 g).trans hBc
  -- the term of a choice is a product over the groups
  refine Eq.trans (Finset.sum_congr rfl fun c _ =>
    ghostChoiceTerm_eq D i s hdisj hBc Ψ v hΨ U hc c) ?_
  -- the sum over the choices is the product of the sums over the local choices
  refine Eq.trans (Fintype.prod_sum fun (g : B) (cg : Finset (Fin Bc) × Batch 𝒢 Bc g) =>
    ghostT D i v g (s.xb g) (s.mem g) U cg).symm ?_
  rw [PrimeVals.eval_eq_prod_evalL]
  exact Finset.prod_congr rfl fun g _ =>
    ghostT_sum D i v g (s.xb g) (s.mem g) U (hc.2.1 g) (hc.2.2.1 g) (hc.2.2.2.2.1 g) (hcardg g)

/-! ### (M2) -/

/-- **(M2) A visit operation acts prime by prime** (eq:ghost-row) [S-02:0456–0475, 0569–0581]:
the statement `GhostStepFactor` of `Memory/Statements.lean`. -/
theorem ghostStepFactor : GhostStepFactor := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc sk hdisj hBc i _ Ψ v hΨ mem U hc
  have h := ghostChoice_sum D i (sk.mstate i mem) hdisj hBc Ψ v hΨ U hc
  refine Eq.trans ?_ h
  unfold Skel.ghostSum
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold ghostChoiceTerm
  exact bigRes_ite_congr Iff.rfl rfl rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

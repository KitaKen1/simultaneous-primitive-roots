module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeGroupSum
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeNewState
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostStepFactorProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (M3) An edge operation acts prime by prime: `EdgeStepFactor`

Source: `verification/stage7-sources/S-02.tex`, lines 477–514 and 569–581
(`[S-02:0477–0514, 0569–0581]`).

`edgeStepFactor : EdgeStepFactor` is proved here, by the scheme of (M2)
(`Memory/GhostStepFactorProof.lean`):

* `Skel.edgeChoiceTerm_eq` — on a state in which every big prime occurs at most once, the term of
  a choice (stores and promotions of all big groups) is the product over the big groups of the
  terms `Skel.edgeT` of its local choices: the fresh births are new group by group
  (`Skel.edge_newBirths_iff`), the truncations are not active (`edg_size_le`), the conditions
  `StoreValid`, `PromoValid` and the coefficient are products over the groups, and in the new
  state every big prime still occurs at most once (`edg_new_consistent`), so that `Ψ` is the
  product of the values there.
* `edg_sum_pairs` — the sum over the stores and the promotions of all groups of a product over the
  groups is the product of the sums over the local choices.
* `Skel.edgeT_sum` (`Memory/EdgeGroupSum.lean`) — the one-group theorem.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- **The sum over two families of local choices of a product over the groups** is the product of
the sums over the pairs of local choices. -/
theorem edg_sum_pairs {B : Type} [Fintype B] [DecidableEq B] {α β : B → Type}
    [∀ g, Fintype (α g)] [∀ g, Fintype (β g)] (F : (g : B) → α g × β g → ℝ) :
    ∑ a : (g : B) → α g, ∑ b : (g : B) → β g, ∏ g, F g (a g, b g) =
      ∏ g, ∑ c : α g × β g, F g c := by
  have h1 := (Fintype.sum_prod_type
    (f := fun p : ((g : B) → α g) × ((g : B) → β g) => ∏ g, F g (p.1 g, p.2 g))).symm
  have h2 := Equiv.sum_comp (Equiv.arrowProdEquivProdArrow B α β)
    (fun p : ((g : B) → α g) × ((g : B) → β g) => ∏ g, F g (p.1 g, p.2 g))
  have h3 := Fintype.prod_sum (fun (g : B) (c : α g × β g) => F g c)
  exact (h1.trans h2.symm).trans h3.symm

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### The fresh births of a choice -/

/-- A fresh birth at an address: the label of a fresh target slot. -/
theorem edg_addrBirth_eq_some [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) (a : B × Slot J ℓ) (z : ℕ) :
    edgeAddrBirth c a = some z ↔ Fresh c a.1 a.2 ∧ (c.xbT a.1 a.2 : ℕ) = z := by
  constructor
  · intro h
    by_cases hf : Fresh c a.1 a.2
    · have h1 : edgeAddrBirth c a = some (c.xbT a.1 a.2 : ℕ) := by
        unfold edgeAddrBirth edgeBirths
        exact if_pos hf
      exact ⟨hf, Option.some.inj (h1.symm.trans h)⟩
    · have h1 : edgeAddrBirth c a = none := by
        unfold edgeAddrBirth edgeBirths
        exact if_neg hf
      rw [h1] at h
      cases h
  · rintro ⟨hf, hz⟩
    have h1 : edgeAddrBirth c a = some (c.xbT a.1 a.2 : ℕ) := by
      unfold edgeAddrBirth edgeBirths
      exact if_pos hf
    rw [h1, hz]

section Births

variable [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {D : MemData 𝒢 J ℓ N}

/-- **The fresh births of a choice are new, group by group**: for pairwise disjoint big groups,
the fresh births of an edge are pairwise distinct and were not born if and only if this holds in
every group. -/
theorem Skel.edge_newBirths_iff (sk : Skel D)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (i : Fin D.n)
    (st : (g : B) → Finset (Slot J ℓ)) (pr : (g : B) → Slot J ℓ → Option (Fin Bc))
    (U : Finset ℕ) :
    NewBirths (edgeAddrBirth (sk.edgeChoice i st pr)) U ↔
      ∀ g, EdgeNewG ((sk.tgt i).2 g) (sk.Cset i g) U (pr g) := by
  constructor
  · rintro ⟨hd, hU⟩ g
    have hb : ∀ sl, EdgeFreshG (sk.Cset i g) (pr g) sl →
        edgeAddrBirth (sk.edgeChoice i st pr) (g, sl) =
          some (((sk.tgt i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) := fun sl hf =>
      (edg_addrBirth_eq_some _ (g, sl) _).mpr ⟨hf, rfl⟩
    refine ⟨fun sl sl' hf hf' hy => ?_, fun sl hf => hU _ _ (hb sl hf)⟩
    have hk : edgeAddrBirth (sk.edgeChoice i st pr) (g, sl') =
        some (((sk.tgt i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) := by
      rw [hy]
      exact hb sl' hf'
    have h1 : ((g, sl) : B × Slot J ℓ) = (g, sl') := hd _ _ _ (hb sl hf) hk
    exact (Prod.mk.inj h1).2
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨g, sl⟩ ⟨g', sl'⟩ z ha ha'
      obtain ⟨hf, hz⟩ := (edg_addrBirth_eq_some _ (g, sl) z).mp ha
      obtain ⟨hf', hz'⟩ := (edg_addrBirth_eq_some _ (g', sl') z).mp ha'
      have hz1 : (((sk.tgt i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) = z := hz
      have hz2 : (((sk.tgt i).2 g' sl' : {p : ℕ // p ∈ 𝒢.big g'}) : ℕ) = z := hz'
      have hmem : z ∈ 𝒢.big g := by
        rw [← hz1]
        exact ((sk.tgt i).2 g sl).2
      have hmem' : z ∈ 𝒢.big g' := by
        rw [← hz2]
        exact ((sk.tgt i).2 g' sl').2
      have hg : g = g' := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj g g' hne) hmem hmem'
      subst hg
      have h2 : sl = sl' := (h g).1 sl sl' hf hf' (Subtype.ext (hz1.trans hz2.symm))
      rw [h2]
    · intro a z ha
      obtain ⟨hf, hz⟩ := (edg_addrBirth_eq_some _ a z).mp ha
      have hz1 : (((sk.tgt i).2 a.1 a.2 : {p : ℕ // p ∈ 𝒢.big a.1}) : ℕ) = z := hz
      rw [← hz1]
      exact (h a.1).2 a.2 hf

/-- For pairwise disjoint big groups, the fresh births of an edge which are primes of the group
`g` are the fresh labels of `g`. -/
theorem Skel.edge_mem_birthSet_iff (sk : Skel D)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (i : Fin D.n)
    (st : (g : B) → Finset (Slot J ℓ)) (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (p : ℕ) ∈ birthSet (edgeAddrBirth (sk.edgeChoice i st pr)) ↔
      (p : ℕ) ∈ edgeFreshSet ((sk.tgt i).2 g) (sk.Cset i g) (pr g) := by
  rw [ghStep_mem_birthSet, mem_edgeFreshSet]
  constructor
  · rintro ⟨⟨g', sl⟩, ha⟩
    obtain ⟨hf, hz⟩ := (edg_addrBirth_eq_some _ (g', sl) _).mp ha
    have hz1 : (((sk.tgt i).2 g' sl : {p : ℕ // p ∈ 𝒢.big g'}) : ℕ) = (p : ℕ) := hz
    have hg : g' = g := by
      by_contra hne
      have hmem : (p : ℕ) ∈ 𝒢.big g' := by
        rw [← hz1]
        exact ((sk.tgt i).2 g' sl).2
      exact Finset.disjoint_left.mp (hdisj g' g hne) hmem p.2
    subst hg
    exact ⟨sl, hf, hz1⟩
  · rintro ⟨sl, hf, hz⟩
    exact ⟨(g, sl), (edg_addrBirth_eq_some _ (g, sl) _).mpr ⟨hf, hz⟩⟩

/-- The fresh births of an edge are big primes. -/
theorem Skel.edge_birthSet_subset (sk : Skel D) (i : Fin D.n)
    (st : (g : B) → Finset (Slot J ℓ)) (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) :
    birthSet (edgeAddrBirth (sk.edgeChoice i st pr)) ⊆ bigPrimes 𝒢 := by
  intro z hz
  obtain ⟨a, ha⟩ := (ghStep_mem_birthSet _ z).mp hz
  obtain ⟨-, hzz⟩ := (edg_addrBirth_eq_some _ a z).mp ha
  rw [← hzz]
  exact mem_bigPrimes.mpr ⟨a.1, ((sk.edgeChoice i st pr).xbT a.1 a.2).2⟩

/-! ### The coefficient -/

omit [DecidableEq S] [DecidableEq B] in
/-- The memory part of the coefficient of an edge where its conditions hold. -/
theorem edgeMemCoef_of_valid (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc)
    (h : memTotal s ≤ Bc ∧ (∑ g, (edgeNewList D i s c g).length) ≤ Bc ∧
      StoreValid D s c ∧ PromoValid D i s c) :
    ∃ i2 : ∀ (g : B) (sl : Slot J ℓ), Decidable (Fresh c g sl),
      edgeMemCoef D i s c =
        D.ρ ^ memZeros s *
            (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
            (∏ g, ∏ sl : Slot J ℓ,
              @ite ℝ (Fresh c g sl) (i2 g sl) (tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl)) 1) *
          D.ρ ^ memZeros (edgeTgt D i s c) :=
  ⟨_, if_pos h⟩

/-- The source state of the edge `i`: the lists of the skeleton at the visit `i`, permuted by the
source permutation, and the memories `mem`. -/
abbrev Skel.edgeSrcState (sk : Skel D) (i : Fin D.n) (mem : (g : B) → Mem 𝒢 Bc g) :
    MState 𝒢 J ℓ Bc :=
  (sk.mstate i.val mem).permLists (sk.edge i).1

/-! ### The term of a choice -/

open _root_.Classical in
/-- **The term of a choice in the sum over the stores and promotions of an edge**
(`Skel.edgeSum`): zero unless the fresh births are new; otherwise the memory part of the
coefficient times the value of `Ψ` at the new memories and the enlarged set of born primes. -/
def Skel.edgeChoiceTerm (sk : Skel D) (i : Fin D.n)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ)
    (st : (g : B) → Finset (Slot J ℓ)) (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) : ℝ :=
  if NewBirths (edgeAddrBirth (sk.edgeChoice i st pr)) U then
    edgeMemCoef D i.val (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) *
      Ψ (fun g => memOfList (edgeNewList D i.val (sk.edgeSrcState i mem)
          (sk.edgeChoice i st pr) g))
        (U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr)))
  else 0

/-- **The term of a choice is a product over the big groups** [S-02:0569–0581]: on a state in
which every big prime occurs at most once, for pairwise disjoint big groups, a cutoff
`Bc ≥ #{big primes}` and an edge whose shared big labels are copied, if `Ψ` is the product of the
values `v` on such states at the next visit, the term of a choice is the product over the big
groups of the terms `Skel.edgeT` of its local choices. -/
theorem Skel.edgeChoiceTerm_eq (sk : Skel D) (i : Fin D.n)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (hBc : (bigPrimes 𝒢).card ≤ Bc)
    (hSh : SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (v : PrimeVals 𝒢)
    (hΨ : ∀ mem U, MemConsistent (sk.lists (i.val + 1)).2 mem U →
      Ψ mem U = v.eval (sk.lists (i.val + 1)).2 mem U)
    (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) (hc : MemConsistent (sk.lists i.val).2 mem U)
    (st : (g : B) → Finset (Slot J ℓ)) (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) :
    sk.edgeChoiceTerm i Ψ mem U st pr = ∏ g, sk.edgeT i v g (mem g) U (st g, pr g) := by
  obtain ⟨hxinj, hminj, hne, hxU, hmU, hUbig⟩ := hc
  have H : ∀ g, EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) (mem g).2 U :=
    fun g => ⟨(sk.src_injective_iff i g).mpr (hxinj g), hminj g,
      fun sl j => hne g ((sk.edge i).1.2 g sl) j, hmU g,
      fun sl => hxU g ((sk.edge i).1.2 g sl), fun j hj => hSh g j hj⟩
  have hcardg : ∀ g, (𝒢.big g).card ≤ Bc := fun g => (ghStep_card_big_le 𝒢 g).trans hBc
  have hsum : ∑ g, (𝒢.big g).card ≤ Bc := (ghStep_sum_card_big hdisj).le.trans hBc
  have hsize : ∀ g, (mem g).1.val + (J + ℓ) ≤ (𝒢.big g).card := fun g =>
    edg_size_le (mem g).2 ((sk.src i).2 g) (H g).hx (H g).hz (H g).hne
  have hlen : ∀ g, (edgeNewList D i.val (sk.edgeSrcState i mem)
      (sk.edgeChoice i st pr) g).length ≤ (𝒢.big g).card := by
    intro g
    have h1 : (edgeNewList D i.val (sk.edgeSrcState i mem)
        (sk.edgeChoice i st pr) g).length ≤ (mem g).1.val + (st g).card :=
      edgeAbsNewList_length_le (sk.step i) (mem g) ((sk.src i).2 g) (st g) (pr g)
    have h3 : (st g).card ≤ J + ℓ := by
      rw [← card_slot J ℓ]
      exact Finset.card_le_univ (st g)
    have h2 := hsize g
    omega
  have h1 : memTotal (sk.edgeSrcState i mem) ≤ Bc := by
    have h : memTotal (sk.edgeSrcState i mem) = ∑ g, (mem g).1.val := rfl
    rw [h]
    exact (Finset.sum_le_sum fun g _ => (Nat.le_add_right _ _).trans (hsize g)).trans hsum
  have h2 : (∑ g, (edgeNewList D i.val (sk.edgeSrcState i mem)
      (sk.edgeChoice i st pr) g).length) ≤ Bc :=
    (Finset.sum_le_sum fun g _ => hlen g).trans hsum
  by_cases hnew : NewBirths (edgeAddrBirth (sk.edgeChoice i st pr)) U
  · have eC : sk.edgeChoiceTerm i Ψ mem U st pr =
        edgeMemCoef D i.val (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) *
          Ψ (fun g => memOfList (edgeNewList D i.val (sk.edgeSrcState i mem)
              (sk.edgeChoice i st pr) g))
            (U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr))) := by
      unfold Skel.edgeChoiceTerm
      exact if_pos hnew
    rw [eC]
    have hN : ∀ g, EdgeNewG ((sk.tgt i).2 g) (sk.Cset i g) U (pr g) :=
      (sk.edge_newBirths_iff hdisj i st pr U).mp hnew
    by_cases hval : (∀ g, EdgeStoreG ((sk.src i).2 g) (sk.Cset i g) (sk.dilAt i) (st g)) ∧
        ∀ g, EdgePromoG ((sk.tgt i).2 g) (sk.Cset i g) (sk.step i) (sk.dilAt i) (mem g) (pr g)
    · -- the truncations are not active and the stores and promotions are admissible
      have hSV : StoreValid D (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) := hval.1
      have hPV : PromoValid D i.val (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) := hval.2
      obtain ⟨i2, hcoef⟩ := edgeMemCoef_of_valid D i.val (sk.edgeSrcState i mem)
        (sk.edgeChoice i st pr) ⟨h1, h2, hSV, hPV⟩
      have hlenBc : ∀ g, (edgeNewList D i.val (sk.edgeSrcState i mem)
          (sk.edgeChoice i st pr) g).length ≤ Bc := fun g => (hlen g).trans (hcardg g)
      -- in the new state every big prime occurs at most once
      have hf := fun g => edg_new_consistent (mem g) (H g) (hN g) (hval.1 g) (hval.2 g)
        (memOfList (Bc := Bc) (edgeNewList D i.val (sk.edgeSrcState i mem)
          (sk.edgeChoice i st pr) g)) (ofFn_memOfList (hlenBc g))
      have hlst : ∀ g sl, (sk.lists (i.val + 1)).2 g sl =
          (sk.tgt i).2 g ((sk.edge i).2.2.2 g sl) := by
        intro g sl
        rw [sk.lists_succ i.val i.isLt]
        rfl
      have hU' : ∀ g (p : {p : ℕ // p ∈ 𝒢.big g}),
          (p : ℕ) ∈ U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr)) ↔
            (p : ℕ) ∈ U ∪ edgeFreshSet ((sk.tgt i).2 g) (sk.Cset i g) (pr g) := by
        intro g p
        rw [Finset.mem_union, Finset.mem_union]
        exact or_congr Iff.rfl (sk.edge_mem_birthSet_iff hdisj i st pr g p)
      have hcons : MemConsistent (sk.lists (i.val + 1)).2
          (fun g => memOfList (Bc := Bc) (edgeNewList D i.val (sk.edgeSrcState i mem)
            (sk.edgeChoice i st pr) g))
          (U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr))) := by
        refine ⟨fun g => (sk.tgt_injective_iff i g).mp (hf g).1, fun g => (hf g).2.1,
          fun g sl j => ?_, fun g sl => ?_,
          fun g j => Finset.mem_union_left _ ((hf g).2.2.2.2 j),
          Finset.union_subset hUbig (sk.edge_birthSet_subset i st pr)⟩
        · rw [hlst g sl]
          exact (hf g).2.2.1 _ j
        · rw [hlst g sl]
          exact (hU' g _).mpr ((hf g).2.2.2.1 _)
      rw [hcoef, hΨ _ _ hcons, PrimeVals.eval_eq_prod_evalL,
        show D.ρ ^ memZeros (sk.edgeSrcState i mem) = ∏ g, D.ρ ^ memZeroCount (mem g) from
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => memZeroCount (mem g)) D.ρ).symm,
        show D.ρ ^ memZeros (edgeTgt D i.val (sk.edgeSrcState i mem) (sk.edgeChoice i st pr)) =
            ∏ g, D.ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeNewList D i.val
              (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) g)) from
          (Finset.prod_pow_eq_pow_sum Finset.univ _ D.ρ).symm,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      obtain ⟨j1, j2, hT⟩ := edgeTG_of_valid D.ρ (Graph.primeGroupReciprocalMass (𝒢.big g))
        (fun p => tiltLaw (𝒢.big g) D.q D.n p) v ((sk.src i).2 g) ((sk.tgt i).2 g)
        (sk.Cset i g) (sk.step i) (sk.dilAt i) (mem g) U (st g) (pr g)
        ⟨hN g, hval.1 g, hval.2 g⟩
      have e2 : (Graph.primeGroupReciprocalMass (𝒢.big g) ^
            promoCount (sk.edgeChoice i st pr) g)⁻¹ =
          (Graph.primeGroupReciprocalMass (𝒢.big g) ^
            (@Finset.filter _ (fun sl : Slot J ℓ => pr g sl ≠ none) j1 Finset.univ).card)⁻¹ := by
        unfold promoCount
        exact congrArg (fun k : ℕ => (Graph.primeGroupReciprocalMass (𝒢.big g) ^ k)⁻¹)
          (edg_card_filter_inst _ _ _)
      have e3 : (∏ sl : Slot J ℓ, @ite ℝ (Fresh (sk.edgeChoice i st pr) g sl) (i2 g sl)
            (tiltLaw (𝒢.big g) D.q D.n ((sk.edgeChoice i st pr).xbT g sl)) 1) =
          ∏ sl : Slot J ℓ, @ite ℝ (EdgeFreshG (sk.Cset i g) (pr g) sl) (j2 sl)
            (tiltLaw (𝒢.big g) D.q D.n ((sk.tgt i).2 g sl)) 1 :=
        Finset.prod_congr rfl fun sl _ => bigRes_ite_congr Iff.rfl rfl rfl
      have e4 : D.ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeNewList D i.val
            (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) g)) =
          D.ρ ^ memZeroCount (memOfList (Bc := Bc)
            (edgeAbsNewList (sk.step i) (mem g) ((sk.src i).2 g) (st g) (pr g))) := rfl
      have e5 : v.evalL g ((sk.lists (i.val + 1)).2 g)
            (List.ofFn (memOfList (Bc := Bc) (edgeNewList D i.val (sk.edgeSrcState i mem)
              (sk.edgeChoice i st pr) g)).2)
            (U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr))) =
          v.evalL g ((sk.tgt i).2 g)
            (edgeAbsNewList (sk.step i) (mem g) ((sk.src i).2 g) (st g) (pr g))
            (U ∪ edgeFreshSet ((sk.tgt i).2 g) (sk.Cset i g) (pr g)) := by
        have hfun : (sk.lists (i.val + 1)).2 g =
            fun sl => (sk.tgt i).2 g ((sk.edge i).2.2.2 g sl) := funext fun sl => hlst g sl
        rw [hfun, ofFn_memOfList (hlenBc g)]
        exact (v.evalL_comp_perm g ((sk.tgt i).2 g) ((sk.edge i).2.2.2 g) _ _).trans
          (v.evalL_congr_U g _ _ (hU' g))
      unfold Skel.edgeT
      rw [hT, e2, e3, e4, e5]
    · -- stores or promotions which are not admissible
      have h0 : edgeMemCoef D i.val (sk.edgeSrcState i mem) (sk.edgeChoice i st pr) = 0 := by
        unfold edgeMemCoef
        exact if_neg fun h => hval ⟨h.2.2.1, h.2.2.2⟩
      rw [h0, zero_mul]
      rcases not_and_or.mp hval with h | h
      · obtain ⟨g, hg⟩ := not_forall.mp h
        refine (Finset.prod_eq_zero (Finset.mem_univ g) ?_).symm
        unfold Skel.edgeT edgeTG
        exact if_neg fun h' => hg h'.2.1
      · obtain ⟨g, hg⟩ := not_forall.mp h
        refine (Finset.prod_eq_zero (Finset.mem_univ g) ?_).symm
        unfold Skel.edgeT edgeTG
        exact if_neg fun h' => hg h'.2.2
  · have eC : sk.edgeChoiceTerm i Ψ mem U st pr = 0 := by
      unfold Skel.edgeChoiceTerm
      exact if_neg hnew
    rw [eC]
    obtain ⟨g, hg⟩ : ∃ g, ¬EdgeNewG ((sk.tgt i).2 g) (sk.Cset i g) U (pr g) :=
      not_forall.mp fun h => hnew ((sk.edge_newBirths_iff hdisj i st pr U).mpr h)
    refine (Finset.prod_eq_zero (Finset.mem_univ g) ?_).symm
    unfold Skel.edgeT edgeTG
    exact if_neg fun h' => hg h'.1

end Births

/-! ### (M3) -/

/-- **(M3) An edge operation acts prime by prime** [S-02:0477–0514, 0569–0581]: the statement
`EdgeStepFactor` of `Memory/Statements.lean`. -/
theorem edgeStepFactor : EdgeStepFactor := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc sk hdisj hBc i hSh Ψ v hΨ mem U hc
  have hcardg : ∀ g, (𝒢.big g).card ≤ Bc := fun g => (ghStep_card_big_le 𝒢 g).trans hBc
  have hL : sk.edgeSum Bc i Ψ mem U =
      ∑ st : (g : B) → Finset (Slot J ℓ), ∑ pr : (g : B) → Slot J ℓ → Option (Fin Bc),
        sk.edgeChoiceTerm i Ψ mem U st pr := by
    unfold Skel.edgeSum Skel.edgeChoiceTerm
    exact Finset.sum_congr rfl fun st _ => Finset.sum_congr rfl fun pr _ =>
      bigRes_ite_congr Iff.rfl rfl rfl
  rw [hL]
  refine (Finset.sum_congr rfl fun st _ => Finset.sum_congr rfl fun pr _ =>
    sk.edgeChoiceTerm_eq i hdisj hBc hSh Ψ v hΨ mem U hc st pr).trans ?_
  refine (edg_sum_pairs fun (g : B) (c : Finset (Slot J ℓ) × (Slot J ℓ → Option (Fin Bc))) =>
    sk.edgeT i v g (mem g) U c).trans ?_
  rw [PrimeVals.eval_eq_prod_evalL]
  refine Finset.prod_congr rfl fun g _ => ?_
  obtain ⟨hxinj, hminj, hne, hxU, hmU, -⟩ := hc
  exact (sk.edgeT_sum i v g (mem g) U hSh ((sk.src_injective_iff i g).mpr (hxinj g)) (hminj g)
    (fun sl j => hne g ((sk.edge i).1.2 g sl) j) (hmU g)
    (fun sl => hxU g ((sk.edge i).1.2 g sl)) (hcardg g)).trans
    (PrimeVals.evalL_comp_perm (sk.edgeStepVals i v) g ((sk.lists i.val).2 g)
      ((sk.edge i).1.2 g) _ _)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

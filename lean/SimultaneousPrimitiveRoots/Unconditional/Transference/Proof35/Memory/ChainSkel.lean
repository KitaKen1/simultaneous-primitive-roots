module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainTail
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The physical compatibility of a prime with an edge of a skeleton

Source: `verification/stage7-sources/S-02.tex`, lines 375–383 (`[S-02:0375–0383]`):

"For large `x` every group prime exceeds `|k|`. Hence if a prime is active at both ends of an
edge, then it divides `kD`, hence `D`. Since `D` consists only of shared labels and banned
auxiliary labels, it must be a prescribed shared label. Conversely, a prime at an unshared entry
or exit cannot divide `D`."

Tools for the proof of (M4) `ChainLifespan`, for a big prime `p` of the group `g` and an edge `i`
of a skeleton with `BigValid`, under `RawHyp`:

* `Skel.mem_activeVisits_iff` — `p` is active at a visit iff it is a label of the list of `g`;
* `Skel.exists_src_iff`, `Skel.exists_tgt_iff`, `Skel.src_injective_iff`,
  `Skel.tgt_injective_iff` — the source and target lists of an edge are permutations of the lists
  at its two visits;
* `Skel.entryCount_ne_zero_iff`, `Skel.one_lt_entryCount`, `Skel.entryCount_le_one`;
* `Skel.exists_tgt_iff_shared_or_entry` — a target label is a shared source label or sits in an
  unshared target slot;
* `Skel.dvd_dilAt_of_shared`, `Skel.of_dvd_dilAt`, `Skel.not_dvd_dilAt`, `Skel.stepRes_eq_zero_iff`
  — the prime factors of `D_i`, and `σ_i k D_i ≡ 0 (p) ⟺ p ∣ D_i`;
* `Skel.edgeFacts` — the three facts which the backward induction uses.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

/-! ### Active visits and lists -/

omit [Fintype S] in
/-- For pairwise disjoint big groups, a prime of the group `g` is active at the visit `i ≤ N` if
and only if it is a label of the big list of `g` at that visit. -/
theorem Skel.mem_activeVisits_iff (sk : Skel D)
    (hdis : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (i : ℕ) (hi : i ≤ D.n) :
    i ∈ sk.activeVisits p ↔ ∃ sl, (sk.lists i).2 g sl = p := by
  rw [sk.mem_activeVisits]
  constructor
  · rintro ⟨-, g', sl, h⟩
    have hg : g' = g := by
      by_contra hne
      have hp' : (p : ℕ) ∈ 𝒢.big g' := by
        rw [← h]
        exact ((sk.lists i).2 g' sl).2
      exact Finset.disjoint_left.mp (hdis g' g hne) hp' p.2
    subst hg
    exact ⟨sl, Subtype.ext h⟩
  · rintro ⟨sl, h⟩
    exact ⟨Nat.lt_succ_of_le hi, g, sl, congrArg Subtype.val h⟩

omit [Fintype S] [Fintype B] in
/-- The source list of an edge has the labels of the list at its first visit. -/
theorem Skel.exists_src_iff (sk : Skel D) (i : Fin D.n) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (∃ sl, (sk.src i).2 g sl = p) ↔ ∃ sl, (sk.lists i.val).2 g sl = p := by
  constructor
  · rintro ⟨sl, h⟩
    exact ⟨(sk.edge i).1.2 g sl, h⟩
  · rintro ⟨sl, h⟩
    refine ⟨((sk.edge i).1.2 g).symm sl, ?_⟩
    show (sk.lists i.val).2 g ((sk.edge i).1.2 g (((sk.edge i).1.2 g).symm sl)) = p
    rw [Equiv.apply_symm_apply]
    exact h

omit [Fintype S] [Fintype B] in
/-- The target list of an edge has the labels of the list at its second visit. -/
theorem Skel.exists_tgt_iff (sk : Skel D) (i : Fin D.n) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (∃ sl, (sk.tgt i).2 g sl = p) ↔ ∃ sl, (sk.lists (i.val + 1)).2 g sl = p := by
  have hl : sk.lists (i.val + 1) = permuteLists (sk.edge i).2.2 (sk.tgt i) :=
    sk.lists_succ i.val i.isLt
  rw [hl]
  constructor
  · rintro ⟨sl, h⟩
    refine ⟨((sk.edge i).2.2.2 g).symm sl, ?_⟩
    show (sk.tgt i).2 g ((sk.edge i).2.2.2 g (((sk.edge i).2.2.2 g).symm sl)) = p
    rw [Equiv.apply_symm_apply]
    exact h
  · rintro ⟨sl, h⟩
    exact ⟨(sk.edge i).2.2.2 g sl, h⟩

omit [Fintype S] [Fintype B] in
theorem Skel.src_injective_iff (sk : Skel D) (i : Fin D.n) (g : B) :
    Function.Injective ((sk.src i).2 g) ↔ Function.Injective ((sk.lists i.val).2 g) :=
  Equiv.injective_comp ((sk.edge i).1.2 g) ((sk.lists i.val).2 g)

omit [Fintype S] [Fintype B] in
theorem Skel.tgt_injective_iff (sk : Skel D) (i : Fin D.n) (g : B) :
    Function.Injective ((sk.tgt i).2 g) ↔ Function.Injective ((sk.lists (i.val + 1)).2 g) := by
  have hl : sk.lists (i.val + 1) = permuteLists (sk.edge i).2.2 (sk.tgt i) :=
    sk.lists_succ i.val i.isLt
  rw [hl]
  exact (Equiv.injective_comp ((sk.edge i).2.2.2 g) ((sk.tgt i).2 g)).symm

/-! ### The number of entries -/

omit [Fintype S] [Fintype B] in
open _root_.Classical in
theorem Skel.entryCount_ne_zero_iff (sk : Skel D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    sk.entryCount i g p ≠ 0 ↔ ∃ sl, Unshared (sk.Cset i g) sl ∧ (sk.tgt i).2 g sl = p := by
  unfold Skel.entryCount
  rw [Finset.card_ne_zero]
  constructor
  · rintro ⟨sl, hsl⟩
    rw [Finset.mem_filter] at hsl
    exact ⟨sl, hsl.2⟩
  · rintro ⟨sl, h⟩
    refine ⟨sl, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩

omit [Fintype S] [Fintype B] in
open _root_.Classical in
/-- Two different unshared target slots with the label `p`. -/
theorem Skel.one_lt_entryCount (sk : Skel D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) {sl sl' : Slot J ℓ} (hne : sl ≠ sl')
    (h : Unshared (sk.Cset i g) sl ∧ (sk.tgt i).2 g sl = p)
    (h' : Unshared (sk.Cset i g) sl' ∧ (sk.tgt i).2 g sl' = p) :
    1 < sk.entryCount i g p := by
  unfold Skel.entryCount
  rw [Finset.one_lt_card]
  refine ⟨sl, ?_, sl', ?_, hne⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h'⟩

omit [Fintype S] [Fintype B] in
open _root_.Classical in
theorem Skel.entryCount_le_one (sk : Skel D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (hinj : Function.Injective ((sk.tgt i).2 g)) :
    sk.entryCount i g p ≤ 1 := by
  unfold Skel.entryCount
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact hinj (ha.2.2.trans hb.2.2.symm)

omit [Fintype S] [Fintype B] in
/-- A label of the target list is a shared label of the source list or sits in an unshared target
slot. -/
theorem Skel.exists_tgt_iff_shared_or_entry (sk : Skel D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (hSh : SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2) :
    (∃ sl, (sk.tgt i).2 g sl = p) ↔
      (∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) ∨
        sk.entryCount i g p ≠ 0 := by
  rw [sk.entryCount_ne_zero_iff i g p]
  constructor
  · rintro ⟨sl, h⟩
    rcases sl with j | k
    · by_cases hj : j ∈ sk.Cset i g
      · exact Or.inr ⟨Sum.inl j, hj, h⟩
      · exact Or.inl ⟨j, hj, (hSh g j hj).symm.trans h⟩
    · exact Or.inr ⟨Sum.inr k, trivial, h⟩
  · rintro (⟨j, hj, h⟩ | ⟨sl, -, h⟩)
    · exact ⟨Sum.inl j, (hSh g j hj).trans h⟩
    · exact ⟨sl, h⟩

/-! ### The prime factors of the dilation -/

/-- A shared big source label divides `D_i`. -/
theorem Skel.dvd_dilAt_of_shared (sk : Skel D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g})
    (hS : ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) :
    (p : ℕ) ∣ sk.dilAt i := by
  obtain ⟨j, hj, hp⟩ := hS
  unfold Skel.dilAt dil bigDil
  refine dvd_mul_of_dvd_right ?_ _
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ g))
  refine Dvd.dvd.mul_right ?_ _
  refine Dvd.dvd.trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  exact dvd_of_eq ((congrArg Subtype.val hp).symm.trans (if_neg hj).symm)

/-- A prime which divides `D_i` is a shared small label, a shared big label or an auxiliary free
label of the edge `i`. -/
theorem Skel.of_dvd_dilAt (sk : Skel D) (hR : RawHyp D) (i : Fin D.n) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ sk.dilAt i) :
    (∃ (g' : S) (j : Fin J), ((sk.src i).1 g' (Sum.inl j) : ℕ) = p) ∨
      (∃ (g' : B) (j : Fin J), j ∉ sk.Cset i g' ∧ ((sk.src i).2 g' (Sum.inl j) : ℕ) = p) ∨
        ∃ (g' : B) (j : {j : Fin J // j ∈ sk.Cset i g'}), (sk.aux i g' j : ℕ) = p := by
  have hpp : _root_.Prime p := hp.prime
  unfold Skel.dilAt dil at hdvd
  rcases hpp.dvd_mul.mp hdvd with h | h
  · unfold smallDil at h
    obtain ⟨g', -, h1⟩ := hpp.exists_mem_finset_dvd h
    obtain ⟨j, -, h2⟩ := hpp.exists_mem_finset_dvd h1
    exact Or.inl ⟨g', j, ((Nat.prime_dvd_prime_iff_eq hp
      (hR.prime_small g' _ ((sk.src i).1 g' (Sum.inl j)).2)).mp h2).symm⟩
  · unfold bigDil at h
    obtain ⟨g', -, h1⟩ := hpp.exists_mem_finset_dvd h
    rcases hpp.dvd_mul.mp h1 with h2 | h2
    · obtain ⟨j, -, h3⟩ := hpp.exists_mem_finset_dvd h2
      by_cases hj : j ∈ sk.Cset i g'
      · have h4 : p ∣ 1 := h3.trans (dvd_of_eq (if_pos hj))
        exact absurd (Nat.dvd_one.mp h4) hp.one_lt.ne'
      · have h4 : p ∣ ((sk.src i).2 g' (Sum.inl j) : ℕ) :=
          h3.trans (dvd_of_eq (if_neg hj))
        exact Or.inr (Or.inl ⟨g', j, hj, ((Nat.prime_dvd_prime_iff_eq hp
          (hR.prime_big g' _ ((sk.src i).2 g' (Sum.inl j)).2)).mp h4).symm⟩)
    · obtain ⟨j, -, h3⟩ := hpp.exists_mem_finset_dvd h2
      exact Or.inr (Or.inr ⟨g', j, ((Nat.prime_dvd_prime_iff_eq hp
        (hR.prime_big g' _ (sk.aux i g' j).2)).mp h3).symm⟩)

/-- "A prime at an unshared entry or exit cannot divide `D`": a big prime which is a label of the
source or of the target list, but not a shared source label, does not divide `D_i`. -/
theorem Skel.not_dvd_dilAt (sk : Skel D) (hR : RawHyp D) (hVal : sk.BigValid) (i : Fin D.n)
    (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (hpres : (∃ sl, (sk.src i).2 g sl = p) ∨ ∃ sl, (sk.tgt i).2 g sl = p) :
    ¬((p : ℕ) ∣ sk.dilAt i) := by
  intro hdvd
  rcases sk.of_dvd_dilAt hR i (hR.prime_big g p p.2) hdvd with
    ⟨g', j, h⟩ | ⟨g', j, hj, h⟩ | ⟨g', j, h⟩
  · have hmem : (p : ℕ) ∈ 𝒢.small g' := by
      rw [← h]
      exact ((sk.src i).1 g' (Sum.inl j)).2
    exact Finset.disjoint_left.mp (hR.disjoint_small_big g' g) hmem p.2
  · have hg : g' = g := by
      by_contra hne
      have hmem : (p : ℕ) ∈ 𝒢.big g' := by
        rw [← h]
        exact ((sk.src i).2 g' (Sum.inl j)).2
      exact Finset.disjoint_left.mp (hR.disjoint_big g' g hne) hmem p.2
    subst hg
    exact hS ⟨j, hj, Subtype.ext h⟩
  · rcases hpres with ⟨sl, hsl⟩ | ⟨sl, hsl⟩
    · exact ((hVal i).2.1 g' j).2 g sl ((congrArg Subtype.val hsl).trans h.symm)
    · exact ((hVal i).2.2 g' j).2 g sl ((congrArg Subtype.val hsl).trans h.symm)

/-- `σ_i k D_i ≡ 0 (p)` if and only if `p ∣ D_i`, for a big prime `p` (prime, `p ∤ k`). -/
theorem Skel.stepRes_eq_zero_iff (sk : Skel D) (hR : RawHyp D) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    ((sk.step i : ℤ) : Res p.1) = 0 ↔ (p : ℕ) ∣ sk.dilAt i := by
  have hp : (p : ℕ).Prime := hR.prime_big g p p.2
  have hpZ : _root_.Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hall : (p : ℕ) ∈ 𝒢.allPrimes := by
    rw [allPrimes_eq]
    exact Finset.mem_union_right _ (mem_bigPrimes.mpr ⟨g, p.2⟩)
  rw [Res.intCast_eq_zero_iff p.1 hp.pos]
  unfold Skel.step
  constructor
  · intro h
    rcases hpZ.dvd_mul.mp h with h1 | h1
    · rcases hpZ.dvd_mul.mp h1 with h2 | h2
      · exfalso
        have hs : edgeSign i.val = 1 ∨ edgeSign i.val = -1 := by
          unfold edgeSign
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hs with hs | hs
        · rw [hs] at h2
          exact hpZ.not_dvd_one h2
        · rw [hs] at h2
          exact hpZ.not_dvd_one (dvd_neg.mp h2)
      · exact absurd h2 (hR.not_dvd p hall)
    · exact Int.natCast_dvd_natCast.mp h1
  · intro h
    exact Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr h) _

/-- `h_{i+1} = h_i + σ_i k D_i` modulo `p`. -/
theorem Skel.off_succ_res (sk : Skel D) (i : Fin D.n) (p : ℕ) :
    ((sk.off (i.val + 1) : ℤ) : Res p) =
      ((sk.off i.val : ℤ) : Res p) + ((sk.step i : ℤ) : Res p) :=
  (congrArg (fun z : ℤ => (z : Res p)) (sk.off_succ i.val i.isLt)).trans (Int.cast_add _ _)

/-! ### The facts about one edge -/

/-- **The compatibility of a big prime `p` of the group `g` with the edge `i`** of a skeleton with
`BigValid`, under `RawHyp` [S-02:0375–0383]:

* if `p` is a shared source label, it is active at both visits and the step vanishes modulo `p`;
* `p` is active at the visit `i + 1` iff it is a shared source label or has an entry;
* if `p` is not a shared source label and is active at the visit `i` or has an entry, then the
  step does not vanish modulo `p` and `p ∤ D_i`. -/
theorem Skel.edgeFacts (sk : Skel D) (hR : RawHyp D) (hVal : sk.BigValid) (i : Fin D.n) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    ((∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) →
        i.val ∈ sk.activeVisits p ∧ i.val + 1 ∈ sk.activeVisits p ∧
          ((sk.step i : ℤ) : Res p.1) = 0) ∧
      (i.val + 1 ∈ sk.activeVisits p ↔
        (∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) ∨
          sk.entryCount i g p ≠ 0) ∧
      ((¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) →
        (i.val ∈ sk.activeVisits p ∨ sk.entryCount i g p ≠ 0) →
          ((sk.step i : ℤ) : Res p.1) ≠ 0 ∧ ¬((p : ℕ) ∣ sk.dilAt i)) := by
  have hSh := (hVal i).1
  have hA : i.val ∈ sk.activeVisits p ↔ ∃ sl, (sk.src i).2 g sl = p :=
    (sk.mem_activeVisits_iff hR.disjoint_big g p i.val (Nat.le_of_lt i.isLt)).trans
      (sk.exists_src_iff i g p).symm
  have hA' : i.val + 1 ∈ sk.activeVisits p ↔ ∃ sl, (sk.tgt i).2 g sl = p :=
    (sk.mem_activeVisits_iff hR.disjoint_big g p (i.val + 1) (Nat.succ_le_of_lt i.isLt)).trans
      (sk.exists_tgt_iff i g p).symm
  have hT := sk.exists_tgt_iff_shared_or_entry i g p hSh
  refine ⟨fun hS => ⟨?_, ?_, ?_⟩, hA'.trans hT, fun hS hpres => ?_⟩
  · obtain ⟨j, -, h⟩ := hS
    exact hA.mpr ⟨Sum.inl j, h⟩
  · exact hA'.mpr (hT.mpr (Or.inl hS))
  · exact (sk.stepRes_eq_zero_iff hR i g p).mpr (sk.dvd_dilAt_of_shared i g p hS)
  · have hnd : ¬((p : ℕ) ∣ sk.dilAt i) := by
      refine sk.not_dvd_dilAt hR hVal i g p hS ?_
      rcases hpres with h | h
      · exact Or.inl (hA.mp h)
      · exact Or.inr (hT.mpr (Or.inr h))
    exact ⟨fun h0 => hnd ((sk.stepRes_eq_zero_iff hR i g p).mp h0), hnd⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

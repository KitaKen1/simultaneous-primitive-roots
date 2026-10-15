module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailLift
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Memory truncation: a history at two cutoffs

Source: `verification/stage7-sources/S-02.tex`, lines 796–802 (`[S-02:0796–0802]`).

For `b ≤ Bc` and a history `h` at the cutoff `b`, with the same history `liftHist h` at the cutoff
`Bc`:

* `sync_fitsUpTo` — as long as the total memory stays at most `b` before and after every
  operation, the two histories visit corresponding states; the conditions "at most `b`" are the
  same for both;
* `sync_fits` — `liftHist h` fits `b` if and only if `h` fits `b`;
* `sync_weight` — if `h` fits `b`, the two histories have the same weight;
* `sync_birthsDistinct` — the two histories have the same performed births (`liftAddr` embeds the
  birth addresses; the additional ghost addresses at the cutoff `Bc` are not performed), so the
  distinct-birth rule holds for both or for none.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section Sync

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} {b Bc : ℕ} {D : MemData 𝒢 J ℓ N}

/-! ### States -/

omit [DecidableEq S] [DecidableEq B] in
theorem memTotal_liftState (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) :
    memTotal (liftState hb s) = memTotal s := rfl

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftState_permLists (hb : b ≤ Bc) (π : ListPerms S B J ℓ) (s : MState 𝒢 J ℓ b) :
    (liftState hb s).permLists π = liftState hb (s.permLists π) := rfl

omit [DecidableEq S] [DecidableEq B] in
theorem emptyVec_liftState (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) :
    emptyVec 𝒢 J ℓ Bc (liftState hb s) = emptyVec 𝒢 J ℓ b s := rfl

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem memMass_lift (hb : b ≤ Bc) (q : ℝ) (n : ℕ) (m : (g : B) → Mem 𝒢 b g) :
    memMass 𝒢 q n (fun g => liftMem hb (m g)) = memMass 𝒢 q n m :=
  Finset.prod_congr rfl fun _ _ => rfl

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The measure of `ℋ` at the two cutoffs. -/
theorem memWeight_liftState (hb : b ≤ Bc) (q : ℝ) (n : ℕ) (s : MState 𝒢 J ℓ b) :
    memWeight 𝒢 q n (liftState hb s) = memWeight 𝒢 q n s := by
  unfold memWeight
  exact ite_congr_of_iff Iff.rfl
    (congrArg (fun t =>
      haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n s.xb * t)
      (memMass_lift hb q n s.mem)) rfl

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftHist_init (hb : b ≤ Bc) (h : History D b) :
    (liftHist hb h).init = liftState hb h.init := rfl

/-! ### One step -/

omit [DecidableEq S] [DecidableEq B] in
/-- The condition of a visit operation is the same for the two histories, if they are at
corresponding states. -/
theorem sync_condG (hb : b ≤ Bc) (h : History D b) (i : Fin (D.n + 1))
    (hs : (liftHist hb h).visitState i.val = liftState hb (h.visitState i.val)) (β : ℕ) :
    (liftHist hb h).condG β i ↔ h.condG β i := by
  show (memTotal ((liftHist hb h).visitState i.val) ≤ β ∧
      (∑ g, ghostNewSize (((liftHist hb h).visitState i.val).mem g)
        (liftGhost hb (h.ghost i) g)) ≤ β) ↔
    (memTotal (h.visitState i.val) ≤ β ∧
      (∑ g, ghostNewSize ((h.visitState i.val).mem g) (h.ghost i g)) ≤ β)
  rw [hs, memTotal_liftState, sum_ghostNewSize_lift]

omit [DecidableEq S] [DecidableEq B] in
/-- The states after a visit operation correspond, if the states before it correspond and the
condition of the operation holds. -/
theorem sync_afterGhost (hb : b ≤ Bc) (h : History D b) (i : Fin (D.n + 1))
    (hs : (liftHist hb h).visitState i.val = liftState hb (h.visitState i.val))
    (hc : h.condG b i) :
    (liftHist hb h).afterGhost i = liftState hb (h.afterGhost i) := by
  obtain ⟨_, hc2⟩ := hc
  have hg : ∀ g, ghostNewSize ((h.visitState i.val).mem g) (h.ghost i g) ≤ b := fun g =>
    (Finset.single_le_sum
      (f := fun g => ghostNewSize ((h.visitState i.val).mem g) (h.ghost i g))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hc2
  show ghostTgt ((liftHist hb h).visitState i.val) (liftGhost hb (h.ghost i)) =
    liftState hb (ghostTgt (h.visitState i.val) (h.ghost i))
  rw [hs]
  exact ghostTgt_lift hb _ _ hg

omit [DecidableEq S] [DecidableEq B] in
/-- The condition of an edge operation is the same for the two histories, if they are at
corresponding states. -/
theorem sync_condE (hb : b ≤ Bc) (h : History D b) (i : Fin D.n)
    (ht : (liftHist hb h).afterGhost i.castSucc = liftState hb (h.afterGhost i.castSucc))
    (β : ℕ) : (liftHist hb h).condE β i ↔ h.condE β i := by
  show (memTotal ((liftHist hb h).afterGhost i.castSucc) ≤ β ∧
      (∑ g, (edgeNewList D i.val
        (((liftHist hb h).afterGhost i.castSucc).permLists (h.edge i).1)
        (liftEdge hb (h.edge i).2.1) g).length) ≤ β) ↔
    (memTotal (h.afterGhost i.castSucc) ≤ β ∧
      (∑ g, (edgeNewList D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1)
        (h.edge i).2.1 g).length) ≤ β)
  rw [ht, memTotal_liftState, liftState_permLists, sum_edgeNewList_lift]

omit [DecidableEq S] [DecidableEq B] in
/-- The states at the next visit correspond, if the states before the edge correspond and the
condition of the edge holds. -/
theorem sync_visitState_succ (hb : b ≤ Bc) (h : History D b) (i : Fin D.n)
    (ht : (liftHist hb h).afterGhost i.castSucc = liftState hb (h.afterGhost i.castSucc))
    (hc : h.condE b i) :
    (liftHist hb h).visitState (i.val + 1) = liftState hb (h.visitState (i.val + 1)) := by
  obtain ⟨_, hc2⟩ := hc
  rw [History.visitState_succ (liftHist hb h) i, History.visitState_succ h i, ht]
  exact edgeFullTgt_lift hb D i.val (h.afterGhost i.castSucc) (h.edge i)
    (edgeNewList_length_le_of_sum D i.val _ _ hc2)

/-! ### The whole history -/

omit [DecidableEq S] [DecidableEq B] in
/-- **The two histories stay together as long as the total memory is at most `b`**: the
conditions of the operations before the visit `i` hold for one of them if and only if they hold
for the other, and then the states at the visit `i` correspond. -/
theorem sync_fitsUpTo (hb : b ≤ Bc) (h : History D b) :
    ∀ i : ℕ, i ≤ D.n → ((liftHist hb h).FitsUpTo b i ↔ h.FitsUpTo b i) ∧
      (h.FitsUpTo b i → (liftHist hb h).visitState i = liftState hb (h.visitState i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨Iff.rfl, fun _ => liftHist_init hb h⟩
  | succ i ih =>
    intro hi
    have hi' : i < D.n := hi
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hi)
    have hstep : h.FitsUpTo b i →
        (((liftHist hb h).condG b (Fin.castSucc ⟨i, hi'⟩) ∧
            (liftHist hb h).condE b ⟨i, hi'⟩) ↔
          (h.condG b (Fin.castSucc ⟨i, hi'⟩) ∧ h.condE b ⟨i, hi'⟩)) ∧
        (h.condG b (Fin.castSucc ⟨i, hi'⟩) ∧ h.condE b ⟨i, hi'⟩ →
          (liftHist hb h).visitState (i + 1) = liftState hb (h.visitState (i + 1))) := by
      intro hA
      have hs : (liftHist hb h).visitState (Fin.castSucc (⟨i, hi'⟩ : Fin D.n)).val =
          liftState hb (h.visitState (Fin.castSucc (⟨i, hi'⟩ : Fin D.n)).val) := ih2 hA
      have hG := sync_condG hb h (Fin.castSucc ⟨i, hi'⟩) hs b
      have hE : h.condG b (Fin.castSucc ⟨i, hi'⟩) →
          ((liftHist hb h).condE b ⟨i, hi'⟩ ↔ h.condE b ⟨i, hi'⟩) := fun hc =>
        sync_condE hb h ⟨i, hi'⟩ (sync_afterGhost hb h (Fin.castSucc ⟨i, hi'⟩) hs hc) b
      refine ⟨⟨fun hx => ⟨hG.mp hx.1, (hE (hG.mp hx.1)).mp hx.2⟩,
        fun hx => ⟨hG.mpr hx.1, (hE hx.1).mpr hx.2⟩⟩, fun hx => ?_⟩
      exact sync_visitState_succ hb h ⟨i, hi'⟩
        (sync_afterGhost hb h (Fin.castSucc ⟨i, hi'⟩) hs hx.1) hx.2
    refine ⟨⟨fun hx => ?_, fun hx => ?_⟩, fun hx => ?_⟩
    · obtain ⟨hx1, hx2⟩ := hx
      have hA := ih1.mp hx1
      exact ⟨hA, fun _ => ((hstep hA).1).mp (hx2 hi')⟩
    · obtain ⟨hx1, hx2⟩ := hx
      exact ⟨ih1.mpr hx1, fun _ => ((hstep hx1).1).mpr (hx2 hi')⟩
    · obtain ⟨hx1, hx2⟩ := hx
      exact (hstep hx1).2 (hx2 hi')

omit [DecidableEq S] [DecidableEq B] in
/-- The conditions before a later visit contain the conditions before an earlier visit. -/
theorem History.fitsUpTo_of_le (h : History D Bc) (β : ℕ) (k : ℕ) :
    ∀ i : ℕ, h.FitsUpTo β (i + k) → h.FitsUpTo β i := by
  induction k with
  | zero => exact fun i hx => hx
  | succ k ih =>
    intro i hx
    have hx' : h.FitsUpTo β (i + k) ∧
        ∀ hi : i + k < D.n, h.condG β (Fin.castSucc ⟨i + k, hi⟩) ∧ h.condE β ⟨i + k, hi⟩ := hx
    exact ih i hx'.1

omit [DecidableEq S] [DecidableEq B] in
/-- A history which fits a bound satisfies the conditions of all its operations. -/
theorem History.cond_of_fits (h : History D Bc) (β : ℕ) (hf : h.Fits β) :
    (∀ i : Fin (D.n + 1), h.condG β i) ∧ ∀ i : Fin D.n, h.condE β i := by
  obtain ⟨hf1, hf2⟩ := hf
  have hstep : ∀ i : Fin D.n, h.condG β i.castSucc ∧ h.condE β i := by
    intro i
    obtain ⟨k, hk⟩ : ∃ k, D.n = i.val + 1 + k := ⟨D.n - (i.val + 1), by have := i.isLt; omega⟩
    have hx : h.FitsUpTo β (i.val + 1) := by
      refine History.fitsUpTo_of_le h β k (i.val + 1) ?_
      rw [← hk]
      exact hf1
    have hx' : h.FitsUpTo β i.val ∧
        ∀ hi : i.val < D.n, h.condG β (Fin.castSucc ⟨i.val, hi⟩) ∧ h.condE β ⟨i.val, hi⟩ := hx
    exact hx'.2 i.isLt
  refine ⟨fun i => ?_, fun i => (hstep i).2⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hf2
  · exact (hstep j).1

omit [DecidableEq S] [DecidableEq B] in
/-- **`liftHist h` fits `b` if and only if `h` fits `b`.** -/
theorem sync_fits (hb : b ≤ Bc) (h : History D b) : (liftHist hb h).Fits b ↔ h.Fits b := by
  obtain ⟨h1, h2⟩ := sync_fitsUpTo hb h D.n le_rfl
  constructor
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    have hA := h1.mp hx1
    exact ⟨hA, (sync_condG hb h (Fin.last D.n) (h2 hA) b).mp hx2⟩
  · intro hx
    obtain ⟨hx1, hx2⟩ := hx
    exact ⟨h1.mpr hx1, (sync_condG hb h (Fin.last D.n) (h2 hx1) b).mpr hx2⟩

/-- **A history which fits `b` has the same weight at the two cutoffs** [S-02:0797–0801]: "the
histories at the cutoff `B` are the histories at the cutoff `Bc` in which the total memory never
exceeds `B` (with the same weights and births)". -/
theorem sync_weight (hb : b ≤ Bc) (h : History D b) (θ : ℝ) (hf : h.Fits b) :
    (liftHist hb h).weight θ = h.weight θ := by
  obtain ⟨hG, hE⟩ := h.cond_of_fits b hf
  obtain ⟨hf1, hf2⟩ := hf
  have hstate : ∀ i : ℕ, i ≤ D.n →
      (liftHist hb h).visitState i = liftState hb (h.visitState i) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, D.n = i + k := ⟨D.n - i, by omega⟩
    refine (sync_fitsUpTo hb h i hi).2 (History.fitsUpTo_of_le h b k i ?_)
    rw [← hk]
    exact hf1
  have hag : ∀ i : Fin (D.n + 1),
      (liftHist hb h).afterGhost i = liftState hb (h.afterGhost i) :=
    fun i => sync_afterGhost hb h i (hstate i.val (Nat.le_of_lt_succ i.isLt)) (hG i)
  have hg : ∀ i : Fin (D.n + 1),
      ghostCoef D i.val ((liftHist hb h).visitState i.val) ((liftHist hb h).ghost i) =
        ghostCoef D i.val (h.visitState i.val) (h.ghost i) := by
    intro i
    obtain ⟨hc1, hc2⟩ := hG i
    rw [hstate i.val (Nat.le_of_lt_succ i.isLt)]
    exact ghostCoef_lift hb D i.val _ _ hc1 hc2
  have hgi : ∀ i : Fin D.n,
      ghostCoef D i.val ((liftHist hb h).visitState i.val) ((liftHist hb h).ghost i.castSucc) =
        ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) := fun i => hg i.castSucc
  have hgl : ghostCoef D D.n ((liftHist hb h).visitState D.n)
        ((liftHist hb h).ghost (Fin.last D.n)) =
      ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) := hg (Fin.last D.n)
  have he : ∀ i : Fin D.n,
      edgeFullCoef D (fun _ => 1) θ i.val ((liftHist hb h).afterGhost i.castSucc)
          ((liftHist hb h).edge i) =
        edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i) := by
    intro i
    obtain ⟨hc1, hc2⟩ := hE i
    rw [hag i.castSucc]
    exact edgeFullCoef_lift hb D _ θ i.val _ (h.edge i) hc1 hc2
  have hev : emptyVec 𝒢 J ℓ Bc ((liftHist hb h).afterGhost (Fin.last D.n)) =
      emptyVec 𝒢 J ℓ b (h.afterGhost (Fin.last D.n)) :=
    (congrArg (emptyVec 𝒢 J ℓ Bc) (hag (Fin.last D.n))).trans (emptyVec_liftState hb _)
  have hm : memWeight 𝒢 D.q D.n (liftHist hb h).init = memWeight 𝒢 D.q D.n h.init :=
    memWeight_liftState hb D.q D.n h.init
  have hprod : (∏ i : Fin D.n,
        ((ghostCoef D i.val ((liftHist hb h).visitState i.val)
          ((liftHist hb h).ghost i.castSucc) : ℝ) : ℂ) *
          edgeFullCoef D (fun _ => 1) θ i.val ((liftHist hb h).afterGhost i.castSucc)
            ((liftHist hb h).edge i)) =
      ∏ i : Fin D.n, ((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
        edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i) :=
    Finset.prod_congr rfl fun i _ => by rw [hgi i, he i]
  unfold History.weight
  rw [hm, hprod, hgl, hev]

/-! ### Births -/

/-- A birth address at the cutoff `b` as a birth address at the cutoff `Bc ≥ b`. -/
def liftAddr (hb : b ≤ Bc) {n : ℕ} : BirthAddr B J ℓ b n → BirthAddr B J ℓ Bc n
  | Sum.inl a => Sum.inl a
  | Sum.inr (Sum.inl a) => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inr a) => Sum.inr (Sum.inr (a.1, a.2.1, Fin.castLE hb a.2.2))

omit [Fintype B] [DecidableEq B] in
theorem liftAddr_injective (hb : b ≤ Bc) {n : ℕ} :
    Function.Injective (liftAddr (B := B) (J := J) (ℓ := ℓ) (n := n) hb) := by
  intro a a' h
  rcases a with a | a | a <;> rcases a' with a' | a' | a'
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Sum.inl.inj (Sum.inr.inj h))
  · exact absurd (Sum.inr.inj h) Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact absurd (Sum.inr.inj h) Sum.inr_ne_inl
  · have h1 : (a.1, a.2.1, Fin.castLE hb a.2.2) = (a'.1, a'.2.1, Fin.castLE hb a'.2.2) :=
      Sum.inr.inj (Sum.inr.inj h)
    have e1 : a.1 = a'.1 := congrArg (fun x : Fin (n + 1) × B × Fin Bc => x.1) h1
    have e2 : a.2.1 = a'.2.1 := congrArg (fun x : Fin (n + 1) × B × Fin Bc => x.2.1) h1
    have e3 : a.2.2 = a'.2.2 :=
      Fin.castLE_injective hb (congrArg (fun x : Fin (n + 1) × B × Fin Bc => x.2.2) h1)
    exact congrArg (fun x => Sum.inr (Sum.inr x)) (Prod.ext e1 (Prod.ext e2 e3))

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The birth at an address is the same for the two histories. -/
theorem liftHist_birth (hb : b ≤ Bc) (h : History D b) (a : BirthAddr B J ℓ b D.n) :
    (liftHist hb h).birth (liftAddr hb a) = h.birth a := by
  rcases a with a | a | a
  · rfl
  · exact congrFun (congrFun (edgeBirths_lift hb (h.edge a.1).2.1) a.2.1) a.2.2
  · rfl

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Every performed address of `liftHist h` is an address at the cutoff `b`: "a ghost address is
performed precisely when its batch is at least that large" [S-02:1060–1061], and the batches of
`h` have at most `b` births. -/
theorem liftHist_birth_range (hb : b ≤ Bc) (h : History D b) (a' : BirthAddr B J ℓ Bc D.n)
    (z : ℕ) (hz : (liftHist hb h).birth a' = some z) : ∃ a, liftAddr hb a = a' := by
  rcases a' with a | a | a
  · exact ⟨Sum.inl a, rfl⟩
  · exact ⟨Sum.inr (Sum.inl a), rfl⟩
  · have hlt : a.2.2.val < (h.ghost a.1 a.2.1).2.1.val := by
      by_contra hcon
      have e : (liftHist hb h).birth (Sum.inr (Sum.inr a)) = none := dif_neg hcon
      rw [e] at hz
      exact absurd hz.symm (Option.some_ne_none z)
    have hle : (h.ghost a.1 a.2.1).2.1.val ≤ b := Nat.le_of_lt_succ (h.ghost a.1 a.2.1).2.1.isLt
    exact ⟨Sum.inr (Sum.inr (a.1, a.2.1, ⟨a.2.2.val, lt_of_lt_of_le hlt hle⟩)), rfl⟩

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- **The distinct-birth rule holds for both histories or for none.** -/
theorem sync_birthsDistinct (hb : b ≤ Bc) (h : History D b) :
    Graph.PerformedBirthsDistinct (liftHist hb h).birth ↔
      Graph.PerformedBirthsDistinct h.birth := by
  constructor
  · intro hd i j z hi hj
    exact liftAddr_injective hb (hd (liftAddr hb i) (liftAddr hb j) z
      ((liftHist_birth hb h i).trans hi) ((liftHist_birth hb h j).trans hj))
  · intro hd i' j' z hi hj
    obtain ⟨i, rfl⟩ := liftHist_birth_range hb h i' z hi
    obtain ⟨j, rfl⟩ := liftHist_birth_range hb h j' z hj
    rw [liftHist_birth] at hi hj
    exact congrArg (liftAddr hb) (hd i j z hi hj)

end Sync

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

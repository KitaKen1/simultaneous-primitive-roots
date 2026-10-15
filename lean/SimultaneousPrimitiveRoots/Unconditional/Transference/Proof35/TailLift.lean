module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailGrowth
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Memory truncation: the operations at two cutoffs

Source: `verification/stage7-sources/S-02.tex`, lines 796–802 (`[S-02:0796–0802]`).

The memory states, the local transition choices and the histories are indexed by the cutoff
(`Fin Bc`: indices of pending particles, sizes of batches). For `b ≤ Bc` this file embeds the
objects at the cutoff `b` into the objects at the cutoff `Bc` and shows that the visit and the edge
operations commute with the embedding as long as the total memory stays at most `b`:

* `liftMem`, `liftState`, `liftBatch`, `liftGhost`, `liftEdge`, `liftFull`, `liftHist` — the
  embeddings (the particles, the terminated indices, the batches and the promoted indices are the
  same; only the bounds of the index types change).
* `ghostCoef_lift`, `ghostTgt_lift` — the visit operation: same coefficient and corresponding
  target, if the total memory is at most `b` before and after the operation.
* `edgeNewList_lift`, `edgeCoef_lift`, `edgeTgt_lift`, `edgeFullCoef_lift`, `edgeFullTgt_lift` —
  the same for the edge operation; `edgeBirths_lift`: the fresh births are the same.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- A `filterMap` over all indices below `Bc` of a function which vanishes at the indices from
`b` on is the `filterMap` over the indices below `b`. -/
theorem tail_filterMap_castLE {β : Type*} {b : ℕ} (Bc : ℕ) (hb : b ≤ Bc) :
    ∀ φ : Fin Bc → Option β, (∀ j : Fin Bc, b ≤ j.val → φ j = none) →
      (List.finRange Bc).filterMap φ =
        (List.finRange b).filterMap (fun j => φ (Fin.castLE hb j)) := by
  induction Bc, hb using Nat.le_induction with
  | base =>
    intro φ _
    rfl
  | succ Bc hb ih =>
    intro φ hφ
    have h3 : φ (Fin.last Bc) = none := hφ _ hb
    have h2 : [Fin.last Bc].filterMap φ = [] := (List.filterMap_cons_none h3).trans rfl
    rw [List.finRange_succ_last, List.filterMap_append, List.filterMap_map, h2, List.append_nil]
    exact ih (φ ∘ Fin.castSucc) (fun j hj => hφ _ hj)

theorem tail_promo_map_iff {b Bc : ℕ} (hb : b ≤ Bc) (o : Option (Fin b)) (j : Fin b) :
    o.map (Fin.castLE hb) = some (Fin.castLE hb j) ↔ o = some j := by
  cases o with
  | none =>
    exact ⟨fun h => absurd h.symm (Option.some_ne_none _),
      fun h => absurd h.symm (Option.some_ne_none _)⟩
  | some j₀ =>
    constructor
    · intro h
      exact congrArg some (Fin.castLE_injective hb (Option.some.inj h))
    · intro h
      exact congrArg (Option.map (Fin.castLE hb)) h

theorem tail_map_eq_none_iff {α β : Type*} (f : α → β) (o : Option α) :
    o.map f = none ↔ o = none := by
  cases o with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some a =>
    exact ⟨fun h => absurd h (Option.some_ne_none _), fun h => absurd h (Option.some_ne_none _)⟩

theorem tail_exists_of_map_eq_some {α β : Type*} (f : α → β) (o : Option α) (y : β)
    (h : o.map f = some y) : ∃ a, o = some a ∧ f a = y := by
  cases o with
  | none => exact absurd h.symm (Option.some_ne_none _)
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

section Lift

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} {b Bc : ℕ}

/-! ### Memories and states -/

/-- A memory at the cutoff `b` as a memory at the cutoff `Bc ≥ b`: the same particles. -/
def liftMem (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g) : Mem 𝒢 Bc g :=
  ⟨Fin.castLE (Nat.succ_le_succ hb) z.1, z.2⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem memAt_liftMem (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g) (j : Fin b) :
    memAt (liftMem hb z) (Fin.castLE hb j) = memAt z j := rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem memAt_liftMem_ge (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g) (j : Fin Bc) (hj : b ≤ j.val) :
    memAt (liftMem hb z) j = none := by
  have hz : z.1.val ≤ b := Nat.le_of_lt_succ z.1.isLt
  have hn : ¬j.val < z.1.val := by omega
  exact dif_neg hn

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The memory of a list of at most `b` particles, at the two cutoffs. -/
theorem memOfList_lift (hb : b ≤ Bc) {g : B} (l : List (Particle 𝒢 g)) (hl : l.length ≤ b) :
    memOfList (Bc := Bc) l = liftMem hb (memOfList (Bc := b) l) := by
  unfold memOfList
  rw [dif_pos (hl.trans hb), dif_pos hl]
  rfl

/-- A memory state at the cutoff `b` as a memory state at the cutoff `Bc ≥ b`. -/
def liftState (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) : MState 𝒢 J ℓ Bc :=
  ⟨s.y, s.xs, s.xb, fun g => liftMem hb (s.mem g)⟩

/-! ### The visit operation -/

/-- A batch at the cutoff `b` as a batch at the cutoff `Bc ≥ b`. -/
def liftBatch (hb : b ≤ Bc) {g : B} (β : Batch 𝒢 b g) : Batch 𝒢 Bc g :=
  ⟨Fin.castLE (Nat.succ_le_succ hb) β.1, β.2⟩

/-- A choice of the visit operation at the cutoff `b` as a choice at the cutoff `Bc ≥ b`. -/
def liftGhost (hb : b ≤ Bc) (c : GhostChoice 𝒢 b) : GhostChoice 𝒢 Bc :=
  fun g => ((c g).1.map (Fin.castLEEmb hb), liftBatch hb (c g).2)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem tail_ghostValid_lift (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g) (A : Finset (Fin b)) :
    GhostValid (liftMem hb z) (A.map (Fin.castLEEmb hb)) ↔ GhostValid z A := by
  constructor
  · intro h i hi
    exact h (Fin.castLE hb i) (Finset.mem_map_of_mem _ hi)
  · intro h i' hi'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hi'
    exact h i hi

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostSurvivors_lift (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g) (A : Finset (Fin b)) :
    ghostSurvivors (liftMem hb z) (A.map (Fin.castLEEmb hb)) = ghostSurvivors z A := by
  have hL := tail_filterMap_castLE Bc hb
    (fun i : Fin Bc => if i ∈ A.map (Fin.castLEEmb hb) then none else memAt (liftMem hb z) i)
    (fun j hj => by
      show (if j ∈ A.map (Fin.castLEEmb hb) then none else memAt (liftMem hb z) j) = none
      rw [memAt_liftMem_ge hb z j hj]
      exact ite_self none)
  unfold ghostSurvivors
  refine hL.trans (congrArg (fun φ => (List.finRange b).filterMap φ) (funext fun j => ?_))
  show (if Fin.castLE hb j ∈ A.map (Fin.castLEEmb hb) then none
      else memAt (liftMem hb z) (Fin.castLE hb j)) = (if j ∈ A then none else memAt z j)
  exact ite_congr_of_iff (Finset.mem_map' (Fin.castLEEmb hb)) rfl rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem tail_ghostNewSize_lift (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g)
    (c : Finset (Fin b) × Batch 𝒢 b g) :
    ghostNewSize (liftMem hb z) (c.1.map (Fin.castLEEmb hb), liftBatch hb c.2) =
      ghostNewSize z c := by
  show (ghostSurvivors (liftMem hb z) (c.1.map (Fin.castLEEmb hb))).length + c.2.1.val =
    (ghostSurvivors z c.1).length + c.2.1.val
  rw [ghostSurvivors_lift]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostCoefG_lift (hb : b ≤ Bc) (q ρ : ℝ) (n i : ℕ) (g : B) (z : Mem 𝒢 b g)
    (c : Finset (Fin b) × Batch 𝒢 b g) :
    ghostCoefG 𝒢 q ρ n i g (liftMem hb z) (c.1.map (Fin.castLEEmb hb), liftBatch hb c.2) =
      ghostCoefG 𝒢 q ρ n i g z c := by
  unfold ghostCoefG
  refine ite_congr_of_iff (tail_ghostValid_lift hb z c.1) ?_ rfl
  exact congrArg (fun k : ℕ =>
    Graph.sourceGhostD (visitQ q n i) ρ ^ k *
      Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - k) *
      (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
        c.2.1.val / (c.2.1.val.factorial : ℝ)) *
      ∏ j, tiltLaw (𝒢.big g) q n (c.2.2 j)) (Finset.card_map (Fin.castLEEmb hb))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostNewMem_lift (hb : b ≤ Bc) {g : B} (z : Mem 𝒢 b g)
    (c : Finset (Fin b) × Batch 𝒢 b g) (hc : ghostNewSize z c ≤ b) :
    ghostNewMem (liftMem hb z) (c.1.map (Fin.castLEEmb hb), liftBatch hb c.2) =
      liftMem hb (ghostNewMem z c) := by
  have hlen : (ghostSurvivors z c.1 ++ batchParticles c.2).length ≤ b := by
    have e : (ghostSurvivors z c.1 ++ batchParticles c.2).length = ghostNewSize z c := by
      unfold ghostNewSize batchParticles
      rw [List.length_append, List.length_ofFn]
    rw [e]
    exact hc
  have e1 : ghostNewMem (liftMem hb z) (c.1.map (Fin.castLEEmb hb), liftBatch hb c.2) =
      memOfList (Bc := Bc) (ghostSurvivors z c.1 ++ batchParticles c.2) :=
    congrArg (fun l => memOfList (Bc := Bc) (l ++ batchParticles c.2))
      (ghostSurvivors_lift hb z c.1)
  rw [e1]
  exact memOfList_lift hb _ hlen

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- **The target of the visit operation at the two cutoffs**, if the new memories have at most
`b` particles. -/
theorem ghostTgt_lift (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) (c : GhostChoice 𝒢 b)
    (hc : ∀ g, ghostNewSize (s.mem g) (c g) ≤ b) :
    ghostTgt (liftState hb s) (liftGhost hb c) = liftState hb (ghostTgt s c) :=
  congrArg (fun m => (⟨s.y, s.xs, s.xb, m⟩ : MState 𝒢 J ℓ Bc))
    (funext fun g => ghostNewMem_lift hb (s.mem g) (c g) (hc g))

omit [DecidableEq S] [DecidableEq B] in
theorem sum_ghostNewSize_lift (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) (c : GhostChoice 𝒢 b) :
    (∑ g, ghostNewSize ((liftState hb s).mem g) (liftGhost hb c g)) =
      ∑ g, ghostNewSize (s.mem g) (c g) :=
  Finset.sum_congr rfl fun g _ => tail_ghostNewSize_lift hb (s.mem g) (c g)

omit [DecidableEq S] [DecidableEq B] in
/-- **The coefficient of the visit operation at the two cutoffs**, if the total memory is at most
`b` before and after the operation. -/
theorem ghostCoef_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : GhostChoice 𝒢 b) (h1 : memTotal s ≤ b)
    (h2 : (∑ g, ghostNewSize (s.mem g) (c g)) ≤ b) :
    ghostCoef D i (liftState hb s) (liftGhost hb c) = ghostCoef D i s c := by
  have hc' : memTotal (liftState hb s) ≤ Bc ∧
      (∑ g, ghostNewSize ((liftState hb s).mem g) (liftGhost hb c g)) ≤ Bc := by
    refine ⟨h1.trans hb, ?_⟩
    rw [sum_ghostNewSize_lift]
    exact h2.trans hb
  unfold ghostCoef
  rw [if_pos hc',
    if_pos (⟨h1, h2⟩ : memTotal s ≤ b ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ b)]
  exact Finset.prod_congr rfl fun g _ => ghostCoefG_lift hb D.q D.ρ D.n i g (s.mem g) (c g)

/-! ### The edge operation -/

/-- A choice of the row transition of an edge at the cutoff `b` as a choice at the cutoff
`Bc ≥ b`: the same promoted indices. -/
def liftEdge (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) :
    EdgeChoice 𝒢 𝔉 Bc :=
  ⟨c.ν, c.r, c.store, fun g sl => (c.promo g sl).map (Fin.castLE hb), c.xsT, c.xbT⟩

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The new memory of an edge is the same list at the two cutoffs. -/
theorem edgeNewList_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (g : B) :
    edgeNewList D i (liftState hb s) (liftEdge hb c) g = edgeNewList D i s c g := by
  have hL := tail_filterMap_castLE Bc hb
    (fun j : Fin Bc => if ∃ sl, (liftEdge hb c).promo g sl = some j then none
      else (memAt ((liftState hb s).mem g) j).map (shiftParticle (edgeStep D i s c)))
    (fun j hj => by
      show (if ∃ sl, (liftEdge hb c).promo g sl = some j then none
        else (memAt (liftMem hb (s.mem g)) j).map (shiftParticle (edgeStep D i s c))) = none
      rw [memAt_liftMem_ge hb (s.mem g) j hj]
      exact ite_self none)
  have hfun : (fun j : Fin b => if ∃ sl, (liftEdge hb c).promo g sl = some (Fin.castLE hb j)
        then none else (memAt ((liftState hb s).mem g) (Fin.castLE hb j)).map
          (shiftParticle (edgeStep D i s c))) =
      fun j : Fin b => if ∃ sl, c.promo g sl = some j then none
        else (memAt (s.mem g) j).map (shiftParticle (edgeStep D i s c)) :=
    funext fun j => ite_congr_of_iff
      (exists_congr fun sl => tail_promo_map_iff hb (c.promo g sl) j) rfl
      (congrArg (Option.map (shiftParticle (edgeStep D i s c))) (memAt_liftMem hb (s.mem g) j))
  unfold edgeNewList
  exact congrArg₂ (· ++ ·)
    (hL.trans (congrArg (fun φ => (List.finRange b).filterMap φ) hfun)) rfl

omit [DecidableEq S] [DecidableEq B] in
theorem promoValid_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) :
    PromoValid D i (liftState hb s) (liftEdge hb c) ↔ PromoValid D i s c := by
  constructor
  · intro h g sl j hj
    have hj' : (liftEdge hb c).promo g sl = some (Fin.castLE hb j) :=
      congrArg (Option.map (Fin.castLE hb)) hj
    obtain ⟨hU, huniq, pr, hpr, h0, hnd, hx⟩ := h g sl (Fin.castLE hb j) hj'
    exact ⟨hU, fun sl' hsl' => huniq sl' (congrArg (Option.map (Fin.castLE hb)) hsl'), pr,
      hpr, h0, hnd, hx⟩
  · intro h g sl j' hj'
    obtain ⟨j, hj, rfl⟩ := tail_exists_of_map_eq_some (Fin.castLE hb) (c.promo g sl) j' hj'
    obtain ⟨hU, huniq, pr, hpr, h0, hnd, hx⟩ := h g sl j hj
    exact ⟨hU, fun sl' hsl' => huniq sl' ((tail_promo_map_iff hb (c.promo g sl') j).mp hsl'),
      pr, hpr, h0, hnd, hx⟩

open _root_.Classical in
omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem promoCount_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b)
    (g : B) : promoCount (liftEdge hb c) g = promoCount c g := by
  unfold promoCount
  exact congrArg Finset.card (Finset.filter_congr fun sl _ =>
    not_congr (tail_map_eq_none_iff (Fin.castLE hb) (c.promo g sl)))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem fresh_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) (g : B)
    (sl : Slot J ℓ) : Fresh (liftEdge hb c) g sl ↔ Fresh c g sl := by
  unfold Fresh
  exact and_congr Iff.rfl (tail_map_eq_none_iff (Fin.castLE hb) (c.promo g sl))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The fresh births of an edge choice are the same at the two cutoffs. -/
theorem edgeBirths_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) :
    edgeBirths (liftEdge hb c) = edgeBirths c := by
  funext g sl
  unfold edgeBirths
  exact ite_congr_of_iff (fresh_lift hb c g sl) rfl rfl

omit [DecidableEq S] [DecidableEq B] in
/-- **The target of the row transition of an edge at the two cutoffs**, if the new memories have
at most `b` particles. -/
theorem edgeTgt_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (hc : ∀ g, (edgeNewList D i s c g).length ≤ b) :
    edgeTgt D i (liftState hb s) (liftEdge hb c) = liftState hb (edgeTgt D i s c) :=
  congrArg (fun m => (⟨(resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y, c.xsT, c.xbT,
      m⟩ : MState 𝒢 J ℓ Bc))
    (funext fun g => (congrArg (memOfList (Bc := Bc)) (edgeNewList_lift hb D i s c g)).trans
      (memOfList_lift hb _ (hc g)))

omit [DecidableEq S] [DecidableEq B] in
theorem sum_edgeNewList_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) :
    (∑ g, (edgeNewList D i (liftState hb s) (liftEdge hb c) g).length) =
      ∑ g, (edgeNewList D i s c g).length :=
  Finset.sum_congr rfl fun g _ => congrArg List.length (edgeNewList_lift hb D i s c g)

omit [DecidableEq S] [DecidableEq B] in
theorem edgeStep_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) :
    edgeStep D i (liftState hb s) (liftEdge hb c) = edgeStep D i s c := rfl

omit [DecidableEq S] [DecidableEq B] in
theorem edgeMultiplier_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) :
    edgeMultiplier D i (liftState hb s) (liftEdge hb c) = edgeMultiplier D i s c := rfl

omit [DecidableEq S] [DecidableEq B] in
theorem storeValid_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) :
    StoreValid D (liftState hb s) (liftEdge hb c) ↔ StoreValid D s c := Iff.rfl

omit [DecidableEq S] [DecidableEq B] in
theorem memZeros_liftState (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) :
    memZeros (liftState hb s) = memZeros s := rfl

omit [DecidableEq S] [DecidableEq B] in
/-- The conditions of the coefficient of an edge at the two cutoffs, if the total memory is at
most `b` before and after the operation. -/
theorem edgeAbsCond_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (h1 : memTotal s ≤ b)
    (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ b) :
    EdgeAbsCond D i (liftState hb s) (liftEdge hb c) ↔ EdgeAbsCond D i s c := by
  have hstep := edgeStep_lift hb D i s c
  constructor
  · intro h
    obtain ⟨_, _, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
    rw [hstep] at a4
    exact ⟨h1, h2, a3, a4, a5, a6, a7, a8, (storeValid_lift hb D s c).mp a9,
      (promoValid_lift hb D i s c).mp a10⟩
  · intro h
    obtain ⟨_, _, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
    refine ⟨h1.trans hb, ?_, a3, ?_, a5, a6, a7, a8, (storeValid_lift hb D s c).mpr a9,
      (promoValid_lift hb D i s c).mpr a10⟩
    · rw [sum_edgeNewList_lift]
      exact h2.trans hb
    · rw [hstep]
      exact a4

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem liftState_y (hb : b ≤ Bc) (s : MState 𝒢 J ℓ b) : (liftState hb s).y = s.y := rfl

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem auxWeight_liftEdge (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) :
    auxWeight 𝒢.big (𝔉 (liftEdge hb c).ν).C (liftEdge hb c).r =
      auxWeight 𝒢.big (𝔉 c.ν).C c.r := rfl

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem promoProd_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 b) :
    (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount (liftEdge hb c) g)⁻¹) =
      ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹ :=
  Finset.prod_congr rfl fun g _ => by rw [promoCount_lift]

open _root_.Classical in
omit [Fintype S] [DecidableEq S] [DecidableEq B] in
theorem freshProd_lift (hb : b ≤ Bc) {𝔉 : N → Pattern 𝒢.big J ℓ} (q : ℝ) (n : ℕ)
    (c : EdgeChoice 𝒢 𝔉 b) :
    (∏ g, ∏ sl : Slot J ℓ, if Fresh (liftEdge hb c) g sl then
        tiltLaw (𝒢.big g) q n ((liftEdge hb c).xbT g sl) else 1) =
      ∏ g, ∏ sl : Slot J ℓ, if Fresh c g sl then tiltLaw (𝒢.big g) q n (c.xbT g sl) else 1 :=
  Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun sl _ =>
    ite_congr_of_iff (fresh_lift hb c g sl) rfl rfl

omit [DecidableEq S] [DecidableEq B] in
theorem memZeros_edgeTgt_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (hc : ∀ g, (edgeNewList D i s c g).length ≤ b) :
    memZeros (edgeTgt D i (liftState hb s) (liftEdge hb c)) = memZeros (edgeTgt D i s c) := by
  rw [edgeTgt_lift hb D i s c hc, memZeros_liftState]

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The real prefactor of the coefficient of an edge at the two cutoffs. -/
theorem edgeAbsReal_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ b) :
    edgeAbsReal D i (liftState hb s) (liftEdge hb c) = edgeAbsReal D i s c := by
  have hlen : ∀ g, (edgeNewList D i s c g).length ≤ b := edgeNewList_length_le_of_sum D i s c h2
  unfold edgeAbsReal
  rw [promoProd_lift hb c, freshProd_lift hb D.q D.n c, memZeros_edgeTgt_lift hb D i s c hlen,
    edgeStep_lift hb D i s c, memZeros_liftState hb s, auxWeight_liftEdge hb c,
    liftState_y hb s]

omit [DecidableEq S] [DecidableEq B] in
/-- **The coefficient of the row transition of an edge at the two cutoffs**, if the total memory
is at most `b` before and after the operation. -/
theorem edgeCoef_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (c : EdgeChoice 𝒢 D.fam b) (h1 : memTotal s ≤ b)
    (h2 : (∑ g, (edgeNewList D i s c g).length) ≤ b) :
    edgeCoef D θ i (liftState hb s) (liftEdge hb c) = edgeCoef D θ i s c := by
  by_cases hcond : EdgeAbsCond D i s c
  · have hcond' := (edgeAbsCond_lift hb D i s c h1 h2).mpr hcond
    rw [edgeCoef_of_cond D θ i (liftState hb s) (liftEdge hb c) hcond',
      edgeCoef_of_cond D θ i s c hcond, edgeAbsReal_lift hb D i s c h2, edgeStep_lift,
      edgeMultiplier_lift]
  · have hcond' : ¬EdgeAbsCond D i (liftState hb s) (liftEdge hb c) := fun h =>
      hcond ((edgeAbsCond_lift hb D i s c h1 h2).mp h)
    rw [edgeCoef_of_not_cond D θ i (liftState hb s) (liftEdge hb c) hcond',
      edgeCoef_of_not_cond D θ i s c hcond]

/-- A choice of the edge operation at the cutoff `b` as a choice at the cutoff `Bc ≥ b`. -/
def liftFull (hb : b ≤ Bc) {D : MemData 𝒢 J ℓ N} (ξ : EdgeFullChoice D b) :
    EdgeFullChoice D Bc :=
  (ξ.1, liftEdge hb ξ.2.1, ξ.2.2)

/-- **The coefficient of the edge operation at the two cutoffs.** -/
theorem edgeFullCoef_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N)
    (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (ξ : EdgeFullChoice D b) (h1 : memTotal s ≤ b)
    (h2 : (∑ g, (edgeNewList D i (s.permLists ξ.1) ξ.2.1 g).length) ≤ b) :
    edgeFullCoef D ψ θ i (liftState hb s) (liftFull hb ξ) = edgeFullCoef D ψ θ i s ξ := by
  have e1 : edgeCoef D θ i ((liftState hb s).permLists ξ.1) (liftEdge hb ξ.2.1) =
      edgeCoef D θ i (s.permLists ξ.1) ξ.2.1 :=
    edgeCoef_lift hb D θ i (s.permLists ξ.1) ξ.2.1 h1 h2
  have e2 : ψ (edgeBirths (liftEdge hb ξ.2.1)) = ψ (edgeBirths ξ.2.1) :=
    congrArg ψ (edgeBirths_lift hb ξ.2.1)
  show (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      (ψ (edgeBirths (liftEdge hb ξ.2.1)) *
        edgeCoef D θ i ((liftState hb s).permLists ξ.1) (liftEdge hb ξ.2.1)) *
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ =
    (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      (ψ (edgeBirths ξ.2.1) * edgeCoef D θ i (s.permLists ξ.1) ξ.2.1) *
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹
  rw [e1, e2]

omit [DecidableEq S] [DecidableEq B] in
/-- **The target of the edge operation at the two cutoffs.** -/
theorem edgeFullTgt_lift (hb : b ≤ Bc) (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ b)
    (ξ : EdgeFullChoice D b)
    (hc : ∀ g, (edgeNewList D i (s.permLists ξ.1) ξ.2.1 g).length ≤ b) :
    edgeFullTgt D i (liftState hb s) (liftFull hb ξ) = liftState hb (edgeFullTgt D i s ξ) :=
  congrArg (fun t : MState 𝒢 J ℓ Bc => t.permLists ξ.2.2)
    (edgeTgt_lift hb D i (s.permLists ξ.1) ξ.2.1 hc)

/-! ### Histories -/

/-- **A history at the cutoff `b` as a history at the cutoff `Bc ≥ b`**: the same initial data
and the same local transition choices. -/
def liftHist (hb : b ≤ Bc) {D : MemData 𝒢 J ℓ N} (h : History D b) : History D Bc :=
  ⟨h.y₀, h.xs₀, h.xb₀, fun i => liftGhost hb (h.ghost i), fun i => liftFull hb (h.edge i)⟩

end Lift

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
